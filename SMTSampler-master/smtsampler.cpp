#include <string.h>
#include <z3++.h>
#include <vector>
#include <map>
#include <unordered_set>
#include <unordered_map>
#include <algorithm>
#include <fstream>

enum {
	STRAT_SMTBIT,   // --smtbit，给 bit-vector 的每一个位加1个软约束
	STRAT_SMTBV,    // --smtbv，给 bit-vector 整体添加一个软约束
	STRAT_SAT       // --sat，将 SMT 公式转换为 SAT 公式
};	/* SMTSampler策略 */

extern int coverage_enable;		// ??
extern int coverage_bool;		// ??
extern int coverage_bv;			// ??
extern int coverage_all_bool;	// ??
extern int coverage_all_bv;		// ??

Z3_ast parse_bv(char const* n, Z3_sort s, Z3_context ctx);	// ??
std::string bv_string(Z3_ast ast, Z3_context ctx);			// 将AST结点输出为对应的字符串

typedef struct {
	char const* a[3] = { NULL, NULL, NULL };
} triple;

class SMTSampler {
	std::string input_file;     // 输入文件

	struct timespec start_time; // 开始的时间
	double solver_time = 0.0;   // 求解时间
	double check_time = 0.0;    // 验证时间
	double cov_time = 0.0;		// ??
	double convert_time = 0.0;	// 重写时间
	int max_samples;            // 最大样本数
	double max_time;            // 最大运行时间

	z3::context c;              // 上下文 c
	int strategy;               // 策略，为 STRAT_SMTBIT、STRAT_SMTBV、STRAT_SAT
	bool convert = false;		// 是否需要重写
	bool const flip_internal = false;	// 是否需要翻转内部结点（默认不需要）
	bool random_soft_bit = false;		// 是否按位随机产生软约束
	z3::apply_result* res0;		// ??
	z3::goal* converted_goal;	// ??
	z3::params params;			// Z3参数集
	z3::optimize opt;			// 优化求解器
	z3::solver solver;			// 约束求解器
	z3::model model;			// 模型
	z3::expr smt_formula;		// SMT公式
	std::vector<z3::func_decl> variables;	// 函数声明集合
	std::vector<z3::func_decl> ind;			// 函数声明集合 ?? 和variable的区别
	std::vector<z3::expr> internal;			// 内部结点表达式集合
	std::vector<z3::expr> constraints;		// 约束表达式集合
	std::vector<std::vector<z3::expr>> soft_constraints;		// 软约束表达式集合
	std::vector<std::pair<int, int>> cons_to_ind;				// 约束-函数声明 映射集
	std::unordered_map<int, std::unordered_set<int>> unsat_ind;	// 不满足函数映射集合
	std::unordered_set<int> unsat_internal;						// 不满足内部函数集合
	std::unordered_set<std::string> all_mutations;				// 总的样本集
	int epochs = 0;				// 样本代数
	int flips = 0;				// 样本翻转数
	int samples = 0;            // 样本数
	int valid_samples = 0;      // 有效样本数
	int solver_calls = 0;       // 求解调用数
	int unsat_ind_count = 0;	// 不满足函数数
	int all_ind_count = 0;		// 所有的函数数

	std::ofstream results_file; // 输出文件，结果文件

public:
	SMTSampler(std::string input, int max_samples, double max_time, int strategy) : opt(c), params(c), solver(c), model(c), smt_formula(c), input_file(input), max_samples(max_samples), max_time(max_time), strategy(strategy) {
		/* 构造函数，根据上下文、参数等构造 SMTSampler */

		z3::set_param("rewriter.expand_select_store", "true");	// 设置全局参数，当params未给予的时候，默认使用此参数。（设置expand_select_store）
		params.set("timeout", 5000u);		// 设置超时
		opt.set(params);					// 根据参数设置优化求解器
		solver.set(params);					// 根据参数设置约束求解器
		convert = strategy == STRAT_SAT;	// 设置默认翻转和策略
	}

	void run() {	/* SMTSampler运行函数 */
		clock_gettime(CLOCK_REALTIME, &start_time); // 记录运行开始时间
		srand(start_time.tv_sec);   				// 设置随机种子
		// parse_cnf();
		parse_smt();		// 根据输入的SMT文件，分析并构建采样基础
		results_file.open(input_file + ".samples"); // 创建样本文件
		while (true) {		// 持续运行，直到时间用完或者样本数足够
			opt.push();     // 为优化求解器创建回溯点（pop为回到回溯点）（因为优化求解器求解要压入规则、事实等，此处用于清空）
			solver.push();  // 为求解器创建回溯点
			for (z3::func_decl& v : ind) {	// 遍历函数声明数组 ind
				if (v.arity() > 0 || v.range().is_array())	// 若函数的参数个数大于0或者是个数组
					continue;	// 则跳过后续处理（即后续处理只针对bit-vector和bool）
				switch (v.range().sort_kind()) {
				case Z3_BV_SORT:	// 若为bit-vector
				{
					if (random_soft_bit) {	// 若为随机生成软约束
						for (int i = 0; i < v.range().bv_size(); ++i) {	// 遍历bit-vector
							if (rand() % 2)	// 则根据随机数，随机设置软约束
								assert_soft(v().extract(i, i) == c.bv_val(0, 1));
							else
								assert_soft(v().extract(i, i) != c.bv_val(0, 1));
						}
					}
					else {	// 若不是 ?? 感觉仍旧还是随机
						std::string n;
						char num[10];
						int i = v.range().bv_size();
						if (i % 4) {	//
							snprintf(num, 10, "%x", rand() & ((1 << (i % 4)) - 1));
							n += num;
							i -= (i % 4);
						}
						while (i) {
							snprintf(num, 10, "%x", rand() & 15);
							n += num;
							i -= 4;
						}
						Z3_ast ast = parse_bv(n.c_str(), v.range(), c);	// 根据软约束和原函数构造语法分析树
						z3::expr exp(c, ast);		// 根据上下文和语法分析树生成表达式
						assert_soft(v() == exp);	// 并把表达式加入opt中
					}
					break;
				}
				case Z3_BOOL_SORT:	// 若为布尔类型
					if (rand() % 2)	// 则随机生成并加入软约束
						assert_soft(v());
					else
						assert_soft(!v());
					break;
				default:
					std::cout << "Invalid sort\n";
					exit(1);
				}

			}
			z3::check_result result = solve();	// 进行约束求解
			if (result == z3::unsat) {          // 若不满足，则输出没有可行解
				std::cout << "No solutions\n";
				break;
			}
			else if (result == z3::unknown) { 	// 若超出求解能力，则输出不可解
				std::cout << "Could not solve\n";
				break;
			}

			opt.pop();		// 求解完毕，弹出断言，回到初始状态
			solver.pop();	// 求解完毕，回到初始状态

			sample(model);	// 根据求解得到的初始解进行采样
		}
	}

	void assert_soft(z3::expr const& e) {	/* 将约束加入到opt中 */
		opt.add(e, 1);
	}

	void print_stats() {	/* 打印统计数据 */
		struct timespec end;
		clock_gettime(CLOCK_REALTIME, &end);
		double elapsed = duration(&start_time, &end);
		std::cout << "Samples " << samples << '\n';				// 输出样本数
		std::cout << "Valid samples " << valid_samples << '\n';	// 输出有效样本数
		std::cout << "Unique valid samples " << all_mutations.size() << '\n';	// 输出有效且唯一的样本的个数
		std::cout << "Total time " << elapsed << '\n';			// 输出总的时间
		std::cout << "Solver time: " << solver_time << '\n';	// 输出求解时间
		std::cout << "Convert time: " << convert_time << '\n';	// 输出重写时间

		std::cout << "Check time " << check_time << '\n';		// 输出检验时间
		std::cout << "Coverage time: " << cov_time << '\n';		// ??
		std::cout << "Coverage bool: " << coverage_bool - coverage_all_bool << '/' << coverage_all_bool << ", coverage bv " << coverage_bv - coverage_all_bv << '/' << coverage_all_bv << '\n';
		std::cout << "Epochs " << epochs << ", Flips " << flips << ", UnsatInd " << unsat_ind_count << '/' << all_ind_count << ", UnsatInternal " << unsat_internal.size() << ", Calls " << solver_calls << '\n' << std::flush;
		// 输出代数，翻转数，不可满足的函数/总的函数 之比，不可满足内部结点数，求解调用数
	}

	std::unordered_set<Z3_ast> sub;	// AST中bool和bit-vector的结点集合
	std::unordered_set<Z3_ast> sup;	// AST已遍历结点集合
	std::unordered_set<std::string> var_names = { "bv", "true", "false" };	// 符号变量名字组，初始有bit-vector，布尔类型变量（后续可加入各类函数）
	int num_arrays = 0, num_bv = 0, num_bools = 0, num_bits = 0, num_uf = 0;
	// 数组数，bit-vector数，bool数，总的位数，未解释的函数数
	int maxdepth = 0;	// 最大求解深度

	void visit(z3::expr e, int depth = 0) {	/* AST结点访问函数 */
		if (sup.find(e) != sup.end())	// 若当前结点已遍历过，则退出
			return;
		assert(e.is_app());	// 确保表达式为application（Z3_APP_AST：常量和应用程序；Z3_NUMERAL_AST：数字常量）
		z3::func_decl fd = e.decl();	// 返回与此应用程序关联的声明（需要假定表达式为application）
		if (e.is_const()) {	// 若应用程序的参数个数为0，即为常量
			std::string name = fd.name().str();	// 取出函数声明的名字
			if (var_names.find(name) == var_names.end()) {	// 如果符号变量名字组中找不到当前函数
				var_names.insert(name);		// 则加入
				// std::cout << "declaration: " << fd << '\n';
				variables.push_back(fd);	// 同时将该函数声明加入到函数声明集合中
				if (fd.range().is_array()) {// 若是数组，则num_arrays计数加1
					++num_arrays;
				}
				else if (fd.is_const()) {	// 若函数声明的参数数量为0
					switch (fd.range().sort_kind()) {
					case Z3_BV_SORT:		// 若为bit-vector
						++num_bv;
						num_bits += fd.range().bv_size();	// 将向量的size加到总的位数
						break;
					case Z3_BOOL_SORT:		// 若为bool
						++num_bools;
						++num_bits;			// 总的位数加1
						break;
					default:
						std::cout << "Invalid sort\n";
						exit(1);
					}
				}
			}
		}
		else if (fd.decl_kind() == Z3_OP_UNINTERPRETED) {	// 若为未解释函数
			std::string name = fd.name().str();	// 取出函数声明的名字
			if (var_names.find(name) == var_names.end()) {	// 如果符号变量名字组中找不到当前函数
				var_names.insert(name);		// 则加入
				// std::cout << "declaration: " << fd << '\n';
				variables.push_back(fd);	// 同时将该函数声明加入到函数声明集合中
				++num_uf;					// 未解释函数数加1
			}
		}
		if (e.is_bool() || e.is_bv()) {	// 如果为bool或bit-vector
			sub.insert(e);	// 则加入到sub集中
		}
		sup.insert(e);		// 标志已遍历过
		if (depth > maxdepth)	// 更新已查找的最大深度
			maxdepth = depth;
		for (int i = 0; i < e.num_args(); ++i)	// 遍历函数的参数
			visit(e.arg(i), depth + 1);	// 遍历每个参数
	}

	void parse_smt() {	/* 根据SMT公式构建采样基础object的函数 */
		z3::expr formula = c.parse_file(input_file.c_str());    // 获取公式（按照SMT-LIB语法）
		Z3_ast ast = formula;   // 根据公式构建抽象语法树
		if (ast == NULL) {
			std::cout << "Could not read input formula.\n";
			exit(1);
		}
		smt_formula = formula;	// 保存SMT公式
		if (convert) {			// 若需要重写(rewrite)
			/* 构建重写策略 tactic */
			z3::tactic simplify(c, "simplify");		// 对原有表达式进行重写，例如将(> x 0.0)重写为(not(<= x 0.0)) ??
			z3::tactic bvarray2uf(c, "bvarray2uf");	// 将位向量组重写为未解释的位向量函数(unknow function)
			z3::tactic ackermannize_bv(c, "ackermannize_bv");	// 在bit-vector实例上运用完整的阿克曼函数 ??
			z3::tactic bit_blast(c, "bit-blast");	// 将bit-vector重写为SAT
			z3::tactic t = simplify & bvarray2uf & ackermannize_bv & bit_blast;

			/* 创建重写集合 goal 并将公式加入 */
			z3::goal g(c);	// 创建goal，本质上是a set of formula，可被转换或重写
			g.add(formula);	//将公式加入goal，进行重写

			struct timespec start;	// 获取开始时间
			clock_gettime(CLOCK_REALTIME, &start);
			z3::apply_result res = t(g);	// 根据策略tatic进行重写，并将结果存在res中
			struct timespec end;	// 获取结束时间
			clock_gettime(CLOCK_REALTIME, &end);
			convert_time += duration(&start, &end);	// 计算本公式重写时间，并将时间加到convert_time

			/* 取出重写完成的公式 */
			assert(res0->size() == 1);
			converted_goal = new z3::goal((*res0)[0]);
			formula = converted_goal->as_expr();

			/* 对公式进行约束求解 */
			z3::solver s(c);	// 创建约束求解器s
			s.set(params);		// 设置参数
			s.add(formula);		// 加入公式
			z3::check_result result = z3::unknown;	// 设置结果默认为unknown
			try {
				result = s.check();	// 调用solver进行断言check，将结果返回给result：sat,unsat,unknown
			}
			catch (z3::exception except) {
				std::cout << "Exception: " << except << "\n";
			}
			if (result == z3::unsat) {			// 若该公式不可满足
				std::cout << "Formula is unsat\n";
				exit(0);
			}
			else if (result == z3::unknown) {	// 若不知是否可满足
				std::cout << "Solver returned unknown\n";
				exit(0);
			}
			z3::model m = s.get_model();		// 获取模型
			ind = get_variables(m, true);		// 获取函数声明集，存到组ind
			z3::model original = res0->convert_model(m);	// 对模型进行重写
			evaluate(original, smt_formula, true, 1);		// 通过elvaluate函数将模型中未解释的函数赋予解释 ??

			opt.add(formula);	// 优化器opt加入重写后的公式
			solver.add(formula);// 求解器solver加入重写后的公式
		}
		else {				// 若不需要重写
			opt.add(formula);	// 直接将公式加入
			solver.add(formula);
			z3::check_result result = solve();	// 求解
			if (result == z3::unsat) {
				std::cout << "Formula is unsat\n";
				exit(0);
			}
			else if (result == z3::unknown) {
				std::cout << "Solver could not solve\n";
				exit(0);
			}
			evaluate(model, smt_formula, true, 1);	// 对模型进行计算评估 ??
		}

		visit(smt_formula);	// 根据公式访问对应的AST并进行分析
		std::cout << "Nodes " << sup.size() << '\n';	// 输出总的结点数
		std::cout << "Internal nodes " << sub.size() << '\n';	// 输出内部结点数(bool和bit-vector)
		std::cout << "Arrays " << num_arrays << '\n';	// 数组的个数
		std::cout << "Bit-vectors " << num_bv << '\n';	// bit-vector的个数
		std::cout << "Bools " << num_bools << '\n';		// bool的个数
		std::cout << "Bits " << num_bits << '\n';		// 位的总数(包括bool和bit-vector)
		std::cout << "Uninterpreted functions " << num_uf << '\n';	// 未解释函数的个数
		if (!convert) {	// 如果不需要转换，则直接更新函数声明集合
			ind = variables;	// ?? ind和variables的关系
		}
		for (Z3_ast e : sub) {	// 遍历AST中结点
			internal.push_back(z3::expr(c, e));	// 将结点的表达式压入到internal集中 ??
		}
	}

	z3::expr evaluate(z3::model m, z3::expr e, bool b, int n) {	/* 计算评估函数 */
		coverage_enable = n;
		z3::expr res = m.eval(e, b);	// 根据e，对给定模型中对应的AST进行评估计算（b为true表示会给未解释函数赋予解释）
		coverage_enable = 0;
		return res;
	}

	std::vector<z3::func_decl> get_variables(z3::model m, bool is_ind) {	/* 获取模型中的函数，存储到(解释或未解释)函数组中 */
		std::vector<z3::func_decl> ind;	// 创建函数声明索引组
		std::string str = "variable: ";
		if (is_ind) {					// 若是要获取函数声明存储到全局组ind中
			str = "ind: ";
		}
		for (int i = 0; i < m.size(); ++i) {	// 遍历模型
			z3::func_decl fd = m[i];			// 取出函数声明
			/* ?? */
			if (!is_ind && (fd.name().kind() == Z3_INT_SYMBOL || fd.name().str().find("k!") == 0)) {
				std::cout << fd << ": ignoring\n";
				continue;
			}
			ind.push_back(fd);	// 将声明压入函数声明索引组
			std::cout << str << fd << '\n';
		}
		return ind;
	}

	void parse_cnf() {	/* 根据SAT公式构建采样基础object的函数(SAT用的是CNF范式) */
		z3::expr_vector exp(c);
		std::ifstream f(input_file);
		assert(f.is_open());
		std::string line;
		while (getline(f, line)) {		// 从输入文件中按行读取
			std::istringstream iss(line);
			if (line.find("c ind ") == 0) {
				std::string s;
				iss >> s;
				iss >> s;
				int v;
				while (!iss.eof()) {
					iss >> v;
					if (v)
						ind.push_back(literal(v).decl());
				}
			}
			else if (line[0] != 'c' && line[0] != 'p') {
				z3::expr_vector clause(c);
				int v;
				while (!iss.eof()) {
					iss >> v;
					if (v > 0)
						clause.push_back(literal(v));
					else if (v < 0)
						clause.push_back(!literal(-v));
				}
				exp.push_back(mk_or(clause));
			}
		}
		f.close();
		z3::expr formula = mk_and(exp);
		opt.add(formula);
		solver.add(formula);
	}

	z3::expr value(char const* n, z3::sort s) {
		switch (s.sort_kind()) {
		case Z3_BV_SORT:
		{
			Z3_ast ast = parse_bv(n, s, c);
			z3::expr exp(c, ast);
			return exp;
		}
		case Z3_BOOL_SORT:
			return c.bool_val(atoi(n) == 1);
		default:
			std::cout << "Invalid sort\n";
			exit(1);
		}
	}

	void sample(z3::model m) {	/* 根据模型进行采样 */
		std::unordered_set<std::string> mutations;		// 样本集
		std::string m_string = model_string(m, ind);	// 将模型转换为string
		output(m, 0);	// 将模型(样本)进行输出
		opt.push();		// 压入优化求解器
		solver.push();	// 压入约束求解器
		size_t pos = 0;

		constraints.clear();		// 清空约束
		soft_constraints.clear();	// 清空软约束
		cons_to_ind.clear();		// 存储约束和函数声明之间的映射的向量组清空
		all_ind_count = 0;			// 总的索引数量初始化为0

		if (flip_internal) {		// 如果翻转内部函数 ??
			for (z3::expr& v : internal) {			// 遍历内部函数声明
				z3::expr b = m.eval(v, true);		// 对结点进行计算评估
				cons_to_ind.emplace_back(-1, -1);	// 在尾部添加<-1,-1>
				constraints.push_back(v == b);		// 添加约束"函数=表达式(值)"
				std::vector<z3::expr> soft;
				soft_constraints.push_back(soft);	// 加入空的软约束向量集
			}
		}

		/* 添加约束 */
		for (int count = 0; count < ind.size(); ++count) {	// 遍历函数声明
			z3::func_decl& v = ind[count];				// 取出函数声明
			if (v.range().is_array()) {					// 若为数组
				assert(m_string.c_str()[pos] == '[');
				++pos;
				int num = atoi(m_string.c_str() + pos);	// 获取条目数
				pos = m_string.find('\0', pos) + 1;

				z3::expr def = value(m_string.c_str() + pos, v.range().array_range());	// 获取else部分
				pos = m_string.find('\0', pos) + 1;

				for (int j = 0; j < num; ++j) {			// 遍历条目
					z3::expr arg = value(m_string.c_str() + pos, v.range().array_domain());	// 获取参数表达式
					pos = m_string.find('\0', pos) + 1;
					z3::expr val = value(m_string.c_str() + pos, v.range().array_range());	// 获取值
					pos = m_string.find('\0', pos) + 1;

					add_constraints(z3::select(v(), arg), val, -1);	// 添加约束，约束为select(a,i)=v
				}
				assert(m_string.c_str()[pos] == ']');
				++pos;
			}
			else if (v.is_const()) {	// 若为bit-vector或bool
				z3::expr a = value(m_string.c_str() + pos, v.range());	// 获取值的表达式
				pos = m_string.find('\0', pos) + 1;
				add_constraints(v(), a, count);	// 添加约束，约束为"v=a"
			}
			else {						// 若为函数
				assert(m_string.c_str()[pos] == '(');
				++pos;
				int num = atoi(m_string.c_str() + pos);	// 获取条目数
				pos = m_string.find('\0', pos) + 1;

				z3::expr def = value(m_string.c_str() + pos, v.range());	// 获取else
				pos = m_string.find('\0', pos) + 1;

				for (int j = 0; j < num; ++j) {			// 遍历条目
					z3::expr_vector args(c);
					for (int k = 0; k < v.arity(); ++k) {	// 遍历参数
						z3::expr arg = value(m_string.c_str() + pos, v.domain(k));	// 获取参数表达式
						pos = m_string.find('\0', pos) + 1;
						args.push_back(arg);				// 将参数表达式压入到参数组中
					}
					z3::expr val = value(m_string.c_str() + pos, v.range());		// 获取对应的值
					pos = m_string.find('\0', pos) + 1;

					add_constraints(v(args), val, -1);		// 添加约束，"参数表达式组-值组"
				}
				assert(m_string.c_str()[pos] == ')');
				++pos;
			}
		}

		struct timespec etime;
		clock_gettime(CLOCK_REALTIME, &etime);
		double start_epoch = duration(&start_time, &etime);

		/* 进行翻转编译，形成k=1的1代样本 */
		print_stats();		// 打印统计数据
		int calls = 0;
		int progress = 0;
		for (int count = 0; count < constraints.size(); ++count) {	// 遍历约束集
			auto u = unsat_ind.find(cons_to_ind[count].first);		// 寻找当前约束是否不满足
			if (u != unsat_ind.end() && u->second.find(cons_to_ind[count].second) != u->second.end()) {
				continue;	// 若是不满足的则不执行后续
			}
			z3::expr& cond = constraints[count];			// 取出约束
			opt.push();										// 压入opt
			solver.push();									// 压入solver
			opt.add(!cond);									// 将约束取反，加入opt中
			solver.add(!cond);								// 将约束取反，加入solver中
			for (z3::expr& soft : soft_constraints[count]) {// 遍历软约束集
				assert_soft(soft);	// 将软约束加入opt中
			}
			struct timespec end;
			clock_gettime(CLOCK_REALTIME, &end);
			double elapsed = duration(&start_time, &end);

			double cost = calls ? (elapsed - start_epoch) / calls : 0.0;	// ?? (似乎是对于求解的优化，对于求解代价小的，直接进行求解)
			cost *= constraints.size() - count;
			if (max_time / 3.0 + start_epoch > max_time && elapsed + cost > max_time) {
				std::cout << "Stopping: slow\n";
				finish();
			}
			z3::check_result result = z3::unknown;
			if (cost * rand() <= (max_time / 3.0 + start_epoch - elapsed) * RAND_MAX) {
				result = solve();		// 调用求解器进行求解
				++calls;
			}
			if (result == z3::sat) {		// 若可满足
				std::string new_string = model_string(model, ind);		// 则将当前model转为string
				if (mutations.find(new_string) == mutations.end()) {	// 若不在变异样本集中
					mutations.insert(new_string);	// 加入到变异样本集中
					output(model, 1);				// 输出样本（为k=1，即1代)
					flips += 1;						// 翻转数+1
				}
				else {
					// std::cout << "repeated\n";
				}
			}
			else if (result == z3::unsat) {	// 若不可满足
				// std::cout << "unsat\n";
				if (!is_ind(count)) {		// 若不属于ind中 ??
					unsat_internal.insert(count);	// 则加入到不满足内部函数集
				}
				else if (cons_to_ind[count].first >= 0) {	// 若属于ind中且为bit-vector或bool
					unsat_ind[cons_to_ind[count].first].insert(cons_to_ind[count].second);	// 加入到不满足ind中
					++unsat_ind_count;
				}
			}
			opt.pop();		// 弹出opt
			solver.pop();	// 弹出solver
			double new_progress = 80.0 * (double)(count + 1) / (double)constraints.size();	// ??
			while (progress < new_progress) {
				++progress;
				std::cout << '=' << std::flush;
			}
		}
		std::cout << '\n';

		/* 由1代产生k=2到k=6 */
		std::vector<std::string> initial(mutations.begin(), mutations.end());	// 集合initial，即初代样本集合(k=1)
		std::vector<std::string> sigma = initial;	// 集合sigma，表示第k代样本，初始为1代

		for (int k = 2; k <= 6; ++k) {	// k从2到6
			std::cout << "Combining " << k << " mutations\n";
			std::vector<std::string> new_sigma;	// 存储当前代的样本集
			int all = 0;		// 统计全部样本的个数
			int good = 0;		// 统计有效样本的个数

			for (std::string b_string : sigma) {		// 遍历sigma集合(第k代样本)中的样本
				for (std::string c_string : initial) {	// 遍历初代集合(k=1)中的样本
					size_t pos_a = 0;
					size_t pos_b = 0;
					size_t pos_c = 0;
					std::string candidate;
					for (z3::func_decl& w : ind) {		// 遍历函数声明
						if (w.range().is_array()) {		// 若为数组
							int arity = 0;
							z3::sort s = w.range().array_range();			// 获取函数的值域
							combine_function(m_string, b_string, c_string,
								pos_a, pos_b, pos_c, arity, s, candidate);	// 将样本combine到candidate中
						}
						else if (w.is_const()) {		// 若为bit-vector或bool
							z3::sort s = w.range();		// 获取值域
							// 直接将值combine得到新样本值，写入到candidate中
							std::string num = combine(m_string.c_str() + pos_a, b_string.c_str() + pos_b, c_string.c_str() + pos_c, s);
							pos_a = m_string.find('\0', pos_a) + 1;
							pos_b = b_string.find('\0', pos_b) + 1;
							pos_c = c_string.find('\0', pos_c) + 1;
							candidate += num + '\0';
						}
						else {							// 若为函数
							int arity = w.arity();		// 获取参数数
							z3::sort s = w.range();		// 获取值域
							combine_function(m_string, b_string, c_string,
								pos_a, pos_b, pos_c, arity, s, candidate);	// 将样本combine到候选样本中
						}
					}
					if (mutations.find(candidate) == mutations.end()) {	// 若样本集中找不到对应样本
						mutations.insert(candidate);		// 则加入到样本集中
						bool valid;
						if (convert) {		// 若需要重写
							z3::model cand = gen_model(candidate, ind);	// 则进行模型重写
							valid = output(cand, k);		// 根据重写后的模型输出样本，同时检测样本有效性
						}
						else {
							valid = output(candidate, k);	// 输出样本，同时检测样本有效性
						}
						++all;			// 更新总样本数
						if (valid) {	// 更新有效样本数
							++good;
							new_sigma.push_back(candidate);	// 加入当前代样本集
						}
					}
				}
			}
			double accuracy = (double)good / (double)all;	// 计算α率
			std::cout << "Valid: " << good << " / " << all << " = " << accuracy << '\n';
			print_stats();	// 打印统计信息
			if (all == 0 || accuracy < 0.1)		// 若无法生成样本或者α率过低，则不再继续
				break;
			sigma = new_sigma;	// 更新当前代
		}

		epochs += 1;
		opt.pop();
		solver.pop();
	}

	void add_constraints(z3::expr exp, z3::expr val, int count) {	/* 添加约束 */
		switch (val.get_sort().sort_kind()) {	// 判断值的类型
		case Z3_BV_SORT:	// 若为bit-vector
		{
			std::vector<z3::expr> soft;
			for (int i = 0; i < val.get_sort().bv_size(); ++i) {	// 遍历bit-vector的每个位
				all_ind_count += (count >= 0);		// 若count>=0，则计数+1
				cons_to_ind.emplace_back(count, i);	// 加入约束映射

				z3::expr r = val.extract(i, i);		// 取出从位i到i的值表达式(也就是取出当前位)
				r = r.simplify();					// 将表达式通过简化器进行简化
				constraints.push_back(exp.extract(i, i) == r);	// 加入约束"表达式-值"
				// soft.push_back(exp.extract(i, i) == r);
				if (strategy == STRAT_SMTBIT)		// 若策略为SMTBIT，则同时将其设为软约束加入opt中
					assert_soft(exp.extract(i, i) == r);
			}
			for (int i = 0; i < val.get_sort().bv_size(); ++i) {	// 可以删去 ??(原本应该是用于加入软约束的)
				soft_constraints.push_back(soft);
			}
			if (strategy == STRAT_SMTBV)	// 若策略为SMTBV，则将整个bit-vector都加入软约束
				assert_soft(exp == val);
			break;
		}
		case Z3_BOOL_SORT:	// 若为bool
		{
			all_ind_count += (count >= 0);		// 若count>=0，则计数+1
			cons_to_ind.emplace_back(count, 0);	// 加入约束映射
			constraints.push_back(exp == val);	// 加入约束"表达式-值"
			std::vector<z3::expr> soft;
			soft_constraints.push_back(soft);
			assert_soft(exp == val);			// 将其设为软约束并加入opt中
			break;
		}
		default:
			std::cout << "Invalid sort\n";
			exit(1);
		}
	}

	char const* parse_function(std::string const& m_string, size_t& pos, int arity, std::unordered_map<std::string, triple>& values, int index) {
		/* 进行语法分析函数 */
		bool is_array = false;
		if (arity == 0) {		// 若参数量为0，则表示为数组
			is_array = true;
			arity = 1;
		}
		assert(m_string.c_str()[pos] == is_array ? '[' : '(');
		++pos;
		int num = atoi(m_string.c_str() + pos);		// 获取条目数
		pos = m_string.find('\0', pos) + 1;

		char const* def = m_string.c_str() + pos;	// 获取else的部分
		pos = m_string.find('\0', pos) + 1;

		for (int j = 0; j < num; ++j) {				// 遍历映射条目
			int start = pos;
			for (int k = 0; k < arity; ++k) {
				pos = m_string.find('\0', pos) + 1;
			}
			std::string args = m_string.substr(start, pos - start);	// 获取完整的参数组
			values[args].a[index] = m_string.c_str() + pos;			// 获取完整的值组并存到索引对应的位置
			pos = m_string.find('\0', pos) + 1;
		}
		assert(m_string.c_str()[pos] == is_array ? ']' : ')');
		++pos;
		return def;	// 返回else部分(映射部分已通过参数values返回了)
	}

	unsigned char hex(char c) {	/* 将十六进制字符转为对应的数字(f转为acsii=15的特殊字符) */
		if ('0' <= c && c <= '9')
			return c - '0';
		else if ('a' <= c && c <= 'f')
			return 10 + c - 'a';
		std::cout << "Invalid hex\n";
		exit(1);
	}

	std::string combine(char const* val_a, char const* val_b, char const* val_c, z3::sort s) {	/* 将将值val_b、val_c的变异结合作用到val_a中，生成新样本 */
		std::string num;
		while (*val_a) {	// 按位遍历样本(a为原始样本，b为变异1，c为变异2)
			unsigned char a = hex(*val_a);	// 获取十六进制字符对应的数值(二进制存储)，用于后续异或操作
			unsigned char b = hex(*val_b);
			unsigned char c = hex(*val_c);
			unsigned char r = a ^ ((a ^ b) | (a ^ c));	// 进行异或操作，结合变异1和变异2，作用在原始样本上，生成新样本r
			/* 将生成的以二进制存储的样本转为对应的十六进制字符 */
			char n;
			if (r <= 9)	// 0~9
				n = '0' + r;
			else		// a~f
				n = 'a' + r - 10;
			num += n;	// 将结果加到num中
			++val_a;	// 遍历处理下一位
			++val_b;
			++val_c;
		}
		return num;		// 返回生成的样本
	}

	void combine_function(std::string const& str_a, std::string const& str_b, std::string const& str_c,
		size_t& pos_a, size_t& pos_b, size_t& pos_c, int arity, z3::sort s, std::string& candidate) {
		/* 结合函数，将三个样本结合为一个样本，通过candidata输出 */

		std::unordered_map<std::string, triple> values;
		char const* def_a = parse_function(str_a, pos_a, arity, values, 0);	// 获取映射存到values，返回else
		char const* def_b = parse_function(str_b, pos_b, arity, values, 1);
		char const* def_c = parse_function(str_c, pos_c, arity, values, 2);

		candidate += arity == 0 ? "[" : "(";
		candidate += std::to_string(values.size()) + '\0';	// 存入映射集合中的参数表达式组
		std::string def = combine(def_a, def_b, def_c, s);	// 将else组结合生成新else并存入候选样本中
		candidate += def + '\0';
		for (auto value : values) {		// 遍历映射集合，取出映射集合中的值组，并结合生成新值组，并存入候选样本中
			char const* val_a = value.second.a[0];
			if (!val_a)
				val_a = def_a;
			char const* val_b = value.second.a[1];
			if (!val_b)
				val_b = def_b;
			char const* val_c = value.second.a[2];
			if (!val_c)
				val_c = def_c;
			std::string val = combine(val_a, val_b, val_c, s);
			candidate += value.first;
			candidate += val + '\0';
		}
		candidate += arity == 0 ? "]" : ")";
	}

	bool is_ind(int count) {	// 判断是否 不是翻转内部函数或者不在内部函数集中 ??
		return !flip_internal || count >= internal.size();
	}

	z3::model gen_model(std::string candidate, std::vector<z3::func_decl> ind) {	/* 根据候选样本产生模型 */
		z3::model m(c);
		size_t pos = 0;
		for (z3::func_decl& v : ind) {		// 遍历函数声明组
			if (v.range().is_array()) {		// 若为数组
				assert(candidate.c_str()[pos] == '[');	// 和model_string里的对应
				++pos;
				int num = atoi(candidate.c_str() + pos);// 获取条目数
				pos = candidate.find('\0', pos) + 1;

				z3::expr def = value(candidate.c_str() + pos, v.range().array_range());	// 获取else部分
				pos = candidate.find('\0', pos) + 1;

				Z3_sort domain_sort[1] = { v.range().array_domain() };	// 获取函数声明排序的定义域
				Z3_sort range_sort = v.range().array_range();			// 获取函数声明排序的值域
				Z3_func_decl decl = (c, "k", 1, domain_sort, range_sort);	// 根据定义域和值域创立映射函数，并返回该函数声明
				z3::func_decl fd(c, decl);

				z3::func_interp f = m.add_func_interp(fd, def);			// 结合映射和else创建对函数的解释，并加入到模型中

				for (int j = 0; j < num; ++j) {			// 遍历条目，获取参数表达式和对应的值
					z3::expr arg = value(candidate.c_str() + pos, v.range().array_domain());
					pos = candidate.find('\0', pos) + 1;
					z3::expr val = value(candidate.c_str() + pos, v.range().array_range());
					pos = candidate.find('\0', pos) + 1;

					z3::expr_vector args(c);	// 构建表达式向量
					args.push_back(arg);		// 将参数表达式加入
					f.add_entry(args, val);		// 并创建"参数-值"的映射条目，加入到函数解释中
				}
				z3::expr array = as_array(fd);	// ??
				m.add_const_interp(v, array);	// 加入恒定解释 ??
				assert(candidate.c_str()[pos] == ']');
				++pos;
			}
			else if (v.is_const()) {	// 若为bit-vector或bool
				z3::expr a = value(candidate.c_str() + pos, v.range());	// 直接读取值
				pos = candidate.find('\0', pos) + 1;

				m.add_const_interp(v, a);		// 并将值作为解释加入
			}
			else {						// 若为函数
				assert(candidate.c_str()[pos] == '(');
				++pos;
				int num = atoi(candidate.c_str() + pos);		// 获取条目数
				pos = candidate.find('\0', pos) + 1;

				z3::expr def = value(candidate.c_str() + pos, v.range());	// 获取else
				pos = candidate.find('\0', pos) + 1;

				z3::func_interp f = m.add_func_interp(v, def);	// 创建函数解释

				for (int j = 0; j < num; ++j) {					// 遍历条目
					z3::expr_vector args(c);					// 创建参数表达式组
					for (int k = 0; k < v.arity(); ++k) {		// 遍历参数
						z3::expr arg = value(candidate.c_str() + pos, v.domain(k));	// 获取参数表达式
						pos = candidate.find('\0', pos) + 1;
						args.push_back(arg);					// 将参数表达式加入到表达式组
					}
					z3::expr val = value(candidate.c_str() + pos, v.range());		// 获取该参数组对应的各值
					pos = candidate.find('\0', pos) + 1;

					f.add_entry(args, val);			// 根据参数组和对应的值构建映射条目并加入到函数解释中
				}
				assert(candidate.c_str()[pos] == ')');
				++pos;
			}
		}
		return m;
	}

	bool output(z3::model m, int nmut) {	/* 将模型进行输出，并返回该样本是否有效 */
		std::string sample;
		if (convert) {	// 若需要重写
			struct timespec start, end;
			clock_gettime(CLOCK_REALTIME, &start);
			z3::model converted = res0->convert_model(m);	// 对模型进行重写
			sample = model_string(converted, variables);	// 将重写后的模型写为string
			clock_gettime(CLOCK_REALTIME, &end);
			convert_time += duration(&start, &end);
		}
		else {
			sample = model_string(m, ind);		// ?? 为什么不直接用402行的m_string
		}
		return output(sample, nmut);
	}

	bool output(std::string sample, int nmut) {	/* 将样本进行输出，并返回该样本是否有效 */
		samples += 1;

		struct timespec start, middle;
		clock_gettime(CLOCK_REALTIME, &start);

		double elapsed = duration(&start_time, &start);
		if (elapsed >= max_time) {
			std::cout << "Stopping: timeout\n";
			finish();
		}

		z3::model m = gen_model(sample, variables);		// 根据样本产生模型
		z3::expr b = evaluate(m, smt_formula, true, 0);	// 根据模型和SMT表达式进行评估

		bool valid = b.bool_value() == Z3_L_TRUE;		// 判断评估结果是否为成功
		if (valid) {	// 若该模型有效
			auto res = all_mutations.insert(sample);	// 则将模型加入到模型组中
			if (res.second) {
				results_file << nmut << ": " << sample << '\n';
			}
			++valid_samples;
			clock_gettime(CLOCK_REALTIME, &middle);
			evaluate(m, smt_formula, true, 2);			// ??
		}
		else if (nmut <= 1) {	// 若为原始样本或第1代（第1代的产生方式是和其他不一样的，如果样本模型无效则需要报错）
			std::cout << "Solution check failed, nmut = " << nmut << "\n";
			std::cout << b << "\n";
			exit(0);
		}

		struct timespec end;
		clock_gettime(CLOCK_REALTIME, &end);
		if (valid) {
			cov_time += duration(&middle, &end);
			check_time += duration(&start, &middle);
		}
		else {
			check_time += duration(&start, &end);
		}
		return valid;
	}

	void finish() {	/* 结束函数 */
		print_stats();			// 打印统计
		results_file.close();	// 关闭文件
		exit(0);
	}

	z3::check_result solve() {	/* 约束求解函数 */
		struct timespec start;		// 获取并记录开始时间
		clock_gettime(CLOCK_REALTIME, &start);
		double elapsed = duration(&start_time, &start);	// 计算截止目前位置的运行时间
		if (valid_samples >= max_samples) {	// 若已求得的样本数大于最大样本数，则finish
			std::cout << "Stopping: samples\n";
			finish();
		}
		if (elapsed >= max_time) {			// 若运行之间超过最大的运行时间，则finish
			std::cout << "Stopping: timeout\n";
			finish();
		}
		z3::check_result result = z3::unknown;	// 设置结果默认为unknown
		try {
			result = opt.check();				// 进行一致性检查，并返回最优解（即结合软约束的约束求解）
		}
		catch (z3::exception except) {
			std::cout << "Exception: " << except << "\n";
		}
		if (result == z3::sat) {			// 若可满足，则保存样本模型
			model = opt.get_model();
		}
		else if (result == z3::unknown) {	// 若不知，则调用solver进行进一步求解
			try {
				result = solver.check();
			}
			catch (z3::exception except) {
				std::cout << "Exception: " << except << "\n";
			}
			std::cout << "MAX-SMT timed out: " << result << "\n";
			if (result == z3::sat) {
				model = solver.get_model();	// 若可满足，则保存样本模型
			}
		}
		struct timespec end;
		clock_gettime(CLOCK_REALTIME, &end);
		solver_time += duration(&start, &end);	// 计算本次求解时间并加入到总的求解时间
		solver_calls += 1;	// 求解调用次数+1

		return result;
	}

	std::string model_string(z3::model m, std::vector<z3::func_decl> ind) {	/* 将模型转换为string */
		std::string s;
		for (z3::func_decl& v : ind) {	// 遍历函数声明组
			if (v.range().is_array()) {	// 若该函数为数组
				z3::expr e = m.get_const_interp(v);	// 获取模型中对于函数v的解释
				Z3_func_decl as_array = Z3_get_as_array_func_decl(c, e);	// 获取与该节点函数关联的函数声明 ??
				if (as_array) {	// 若存在
					z3::func_interp f = m.get_func_interp(to_func_decl(c, as_array));	// 获取该关联的函数的解释
					std::string num = "[";
					num += std::to_string(f.num_entries());			// 获取函数解释的条目数（函数被解释为一组有限映射和一个else，其中条目数即为映射数）
					s += num + '\0';
					std::string def = bv_string(f.else_value(), c);	// 获取函数解释中else的部分
					s += def + '\0';
					for (int j = 0; j < f.num_entries(); ++j) {		// 遍历获取到的映射
						std::string arg = bv_string(f.entry(j).arg(0), c);	// 获取函数解释中对应映射的参数表达式
						std::string val = bv_string(f.entry(j).value(), c);	// 获取参数的对应值
						s += arg + '\0';
						s += val + '\0';
					}
					s += "]";
				}
				else {			// 若不存在
					std::vector<std::string> args;		// 参数组
					std::vector<std::string> values;	// 参数对应的值组
					while (e.decl().name().str() == "store") {	// 若该函数解释的声明为"store"，即store(a,i,v)
						std::string arg = bv_string(e.arg(1), c);	// 获取参数
						if (std::find(args.begin(), args.end(), arg) != args.end())	// 若参数已加入参数组中，则跳出
							continue;
						args.push_back(arg);						// 将参数压入
						values.push_back(bv_string(e.arg(2), c));	// 将值压入
						e = e.arg(0);
					}
					std::string num = "[";
					num += std::to_string(args.size());			// 写入参数数量
					s += num + '\0';
					std::string def = bv_string(e.arg(0), c);	// 写入对应的值的数量
					s += def + '\0';
					for (int j = args.size() - 1; j >= 0; --j) {	// 遍历，一一写入参数和对应的值
						std::string arg = args[j];
						std::string val = values[j];
						s += arg + '\0';
						s += val + '\0';
					}
					s += "]";
				}
			}
			else if (v.is_const()) {	// 若参数数为0
				z3::expr b = m.get_const_interp(v);	// 获取模型中对于函数v的解释
				Z3_ast ast = b;						// 构造解释对应的AST结点
				switch (v.range().sort_kind()) {
				case Z3_BV_SORT:		// 若为bit-vector
				{
					if (!ast) {			// 若无法构建解释对应的AST结点，则直接将位向量写入
						s += bv_string(c.bv_val(0, v.range().bv_size()), c) + '\0';
					}
					else {				// 若存在，则将解释写入
						s += bv_string(b, c) + '\0';
					}
					break;
				}
				case Z3_BOOL_SORT:		// 若为bool
				{
					if (!ast) {			// 若无法构建解释对应的AST结点，则写入false
						s += std::to_string(false) + '\0';
					}
					else {				// 若可以构建，则写入true
						s += std::to_string(b.bool_value() == Z3_L_TRUE) + '\0';
					}
					break;
				}
				default:
					std::cout << "Invalid sort\n";
					exit(1);
				}
			}
			else {		// 若为函数
				z3::func_interp f = m.get_func_interp(v);	// 获取解释
				std::string num = "(";
				num += std::to_string(f.num_entries());		// 将映射条目数写入
				s += num + '\0';
				std::string def = bv_string(f.else_value(), c);	// 将else写入
				s += def + '\0';
				for (int j = 0; j < f.num_entries(); ++j) {		// 遍历映射条目
					for (int k = 0; k < f.entry(j).num_args(); ++k) {	// 遍历参数组
						std::string arg = bv_string(f.entry(j).arg(k), c);	// 写入对应的参数
						s += arg + '\0';
					}
					std::string val = bv_string(f.entry(j).value(), c);		// 写入参数组对应的值
					s += val + '\0';
				}
				s += ")";
			}
		}
		return s;
	}

	double duration(struct timespec* a, struct timespec* b) {	/* 计算a到b之间的持续时间 */
		return (b->tv_sec - a->tv_sec) + 1.0e-9 * (b->tv_nsec - a->tv_nsec);
	}

	z3::expr literal(int v) {
		return c.constant(c.str_symbol(std::to_string(v).c_str()), c.bool_sort());
	}
};

int main(int argc, char* argv[]) {
	int max_samples = 1000000;          // 设置默认最大样本数
	double max_time = 3600.0;           // 设置默认最长运行时间
	int strategy = STRAT_SMTBIT;        // 设置默认策略为 STRAT_SMTBIT
	if (argc < 2) {
		std::cout << "Argument required: input file\n";
		return 0;
	}
	bool arg_samples = false;
	bool arg_time = false;
	for (int i = 1; i < argc; ++i) {
		if (strcmp(argv[i], "-n") == 0)         // 若输入参数设置了最大样本数
			arg_samples = true;
		else if (strcmp(argv[i], "-t") == 0)    // 若输入参数设置了最大运行时间
			arg_time = true;
		else if (strcmp(argv[i], "--smtbit") == 0)  // 若输入参数设置了策略
			strategy = STRAT_SMTBIT;
		else if (strcmp(argv[i], "--smtbv") == 0)
			strategy = STRAT_SMTBV;
		else if (strcmp(argv[i], "--sat") == 0)
			strategy = STRAT_SAT;
		else if (arg_samples) {     // 修改最大样本数
			arg_samples = false;
			max_samples = atoi(argv[i]);
		}
		else if (arg_time) {      // 修改最大运行时间
			arg_time = false;
			max_time = atof(argv[i]);
		}
	}
	/* 根据参数创建 SMTSampler 对象，参数为：SMT公式，最大样本数，最大运行时间，策略 */
	SMTSampler s(argv[argc - 1], max_samples, max_time, strategy);
	s.run();    // 运行，生成样本
	return 0;
}

