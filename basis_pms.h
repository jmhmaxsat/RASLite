#ifndef _BASIS_PMS_H_
#define _BASIS_PMS_H_

#include <iostream>
#include <fstream>
#include <sstream>
#include <cstdlib>
#include <cmath>
#include <cstring>
#include <queue>
#include <stdio.h>
#include <stdlib.h>
#include <sys/times.h> //these two h files are for timing in linux
#include <unistd.h>

using namespace std;

#define mypop(stack) stack[--stack##_fill_pointer]
#define mypush(item, stack) stack[stack##_fill_pointer++] = item

const float MY_RAND_MAX_FLOAT = 10000000.0;
const int MY_RAND_MAX_INT = 10000000;
const float BASIC_SCALE = 0.0000001; //1.0f/MY_RAND_MAX_FLOAT;
int cutoff = 300;



long long *basis_clause_weight;



// Define a data structure for a literal.
struct lit
{
	int clause_num; //clause num, begin with 0
	int var_num;	//variable num, begin with 1
	bool sense;		//is 1 for true literals, 0 for false literals.
};

static struct tms start_time;
static double get_runtime()
{
	struct tms stop;
	times(&stop);
	return (double)(stop.tms_utime - start_time.tms_utime + stop.tms_stime - start_time.tms_stime) / sysconf(_SC_CLK_TCK);
}
static void start_timing()
{
	times(&start_time);
}

class Satlike
{
  private:
	/***********non-algorithmic information ****************/
	int problem_weighted; //表示问题是否是加权问题，如果是加权问题，则该变量为1，否则为0。
	int partial; //1 if the instance has hard clauses, and 0 otherwise.
	int pure_sat; //表示问题是否是纯粹的可满足性问题（没有硬子句），如果是，则该变量为1，否则为0。

	int max_clause_length; 
	int min_clause_length; 

	//size of the instance
	int num_vars;	//var index from 1 to num_vars
	int num_clauses; //clause index from 0 to num_clauses-1
	int num_hclauses;
	int num_sclauses;

	//steps and time
	int tries;
	int max_tries;
	unsigned int max_flips;
	unsigned int max_non_improve_flip;//连续非改进的最大翻转次数
	unsigned int step;//当前步数

	int print_time;
	int print60;
	int cutoff_time;
	int prioup_time;//优先级截止时间
	double opt_time;// 优化时间

	/**********end non-algorithmic information*****************/
	/* literal arrays */
	lit **var_lit;		   //var_lit[i][j] means the j'th literal of var i.
	int *var_lit_count;	//amount of literals of each var
	lit **clause_lit;	  //clause_lit[i][j] means the j'th literal of clause i.
	int *clause_lit_count; // amount of literals in each clause

	/* Information about the variables. */
	long long *score;
	long long *time_stamp;//变量的时间戳
	int **var_neighbor;
	int *var_neighbor_count;
	int *neighbor_flag;
	int *temp_neighbor;

	/* Information about the clauses */
	long long top_clause_weight;       //硬子句权重，硬子句权重大于软子句权重之和
	long long *org_clause_weight;
	long long total_soft_weight;
	long long *clause_weight;
	int *sat_count;//跟踪子句的满足变量数量
	int *sat_var;//跟踪满足子句的变量
	long long *clause_selected_count;
	int *best_soft_clause;

	//original unit clause stack
	lit *unit_clause;
	int unit_clause_count;

	//unsat clauses stack
	int *hardunsat_stack;		   //store the unsat clause number
	int *index_in_hardunsat_stack; //which position is a clause in the unsat_stack
	int hardunsat_stack_fill_pointer;

	int *softunsat_stack;		   //store the unsat clause number
	int *index_in_softunsat_stack; //which position is a clause in the unsat_stack
	int softunsat_stack_fill_pointer;

	//variables in unsat clauses
	int *unsatvar_stack;
	int unsatvar_stack_fill_pointer;
	int *index_in_unsatvar_stack;
	int *unsat_app_count; //a varible appears in how many unsat clauses

	//good decreasing variables (dscore>0 and confchange=1)
	int *goodvar_stack;
	int goodvar_stack_fill_pointer;
	int *already_in_goodvar_stack;

	/* Information about solution */
	int *cur_soln; //the current solution, with 1's for True variables, and 0's for False variables
	int *best_soln;
	int *local_opt_soln;
	int best_soln_feasible; //when find a feasible solution, this is marked as 1.
	int local_soln_feasible;
	int hard_unsat_nb;//用于跟踪不满足硬子句的数量
	long long soft_unsat_weight;//用于跟踪不满足软子句的权重。
	long long opt_unsat_weight;//用于跟踪最佳不满足权重
	long long local_opt_unsat_weight;//用于跟踪局部最佳不满足权重。

	//clause weighting
	int *large_weight_clauses;
	int large_weight_clauses_count;
	int large_clause_count_threshold;

	int *soft_large_weight_clauses;
	int *already_in_soft_large_weight_stack;
	int soft_large_weight_clauses_count;
	int soft_large_clause_count_threshold;

	//tem data structure used in algorithm
	int *best_array;
	int best_count;
	int *temp_lit;

	//parameters used in algorithm
	float rwprob;
	float rdprob;
	float smooth_probability;         //加权机制Weighting—MS中的平滑概率sp
	int hd_count_threshold;           //BMS策略中，所选取的样本数量k
	int h_inc;                        //加权机制Weighting-MS中不满足硬子句的增加值h_inc
	int softclause_weight_threshold;  //加权机制Weighting-MS中软子句权重增加阈值

	//function used in algorithm
	void build_neighbor_relation();
	void allocate_memory();
	bool verify_sol();
	void increase_weights();
	void smooth_weights();
	void update_clause_weights();
	void unsat(int clause);
	void sat(int clause);
	void init(vector<int> &init_solution);
	void flip(int flipvar);
	void update_goodvarstack1(int flipvar);
	void update_goodvarstack2(int flipvar);
	int pick_var();

  public:
	Satlike();
	void settings();
	void build_instance(char *filename);
	void local_search(char *inputfile);
	void local_search_with_decimation(char *inputfile);
	void simple_print();
	void print_best_solution();
	void free_memory();
};

#endif
