#ifndef _PMS_H_
#define _PMS_H_

#include "basis_pms.h"
#include "deci.h"

//遍历 goodvar_stack，将里面不再是 "goodvar" 的变量移除，然后遍历与 flipvar 相邻的变量，将其中是 "goodvar" 且不在 goodvar_stack的变量添加进去
/*

*/
void Satlike::update_goodvarstack1(int flipvar)
{
	int v;
	//remove the vars no longer goodvar in goodvar stack
	for (int index = goodvar_stack_fill_pointer - 1; index >= 0; index--)
	{
		v = goodvar_stack[index];
		if (score[v] <= 0)
		{
			goodvar_stack[index] = mypop(goodvar_stack); //如果变量 v 不再是 "goodvar"，则将 goodvar_stack 中的当前元素替换为堆栈中的最后一个元素，以删除 v。
			already_in_goodvar_stack[v] = -1; //将变量 v 在 already_in_goodvar_stack 数组中的条目标记为 -1，表示不再在 "goodvar stack" 中。
		}
	}

	//add goodvar
	for (int i = 0; i < var_neighbor_count[flipvar]; ++i) //遍历与 flipvar 相邻的变量。
	{
		v = var_neighbor[flipvar][i]; 
		if (score[v] > 0)
		{
			if (already_in_goodvar_stack[v] == -1) //检查变量 v 是否已经在 "goodvar stack" 中。
			{
				already_in_goodvar_stack[v] = goodvar_stack_fill_pointer;//如果变量 v 不在 "goodvar stack" 中，则将其标记为 "goodvar"，并在 already_in_goodvar_stack 中记录其位置。
				mypush(v, goodvar_stack); //将变量 v 添加到 "goodvar stack" 中。
			}
		}
	}
}


//先检查 flipvar 在 goodvar_stack 中的状态，对它进行添加或移除操作，然后然后遍历与 flipvar 相邻的变量，对其进行添加或移除操作
void Satlike::update_goodvarstack2(int flipvar)
{
	if (score[flipvar] > 0 && already_in_goodvar_stack[flipvar] == -1) //检查当前要翻转的变量 flipvar 的分数是否大于零且不在 goodvar_stack 中。如果条件成立，说明 flipvar 是一个好变量，可以添加到堆栈中。
	{ 
		already_in_goodvar_stack[flipvar] = goodvar_stack_fill_pointer;//如果 flipvar 是一个好变量，将它的索引位置设置为 goodvar_stack_fill_pointer，然后 goodvar_stack_fill_pointer 递增，表示堆栈的填充位置。
		mypush(flipvar, goodvar_stack); //将 flipvar 添加到 goodvar_stack 堆栈中。
	}
	else if (score[flipvar] <= 0 && already_in_goodvar_stack[flipvar] != -1) //如果 flipvar 不是好变量（分数小于等于零），且它在 goodvar_stack 中（索引位置不为 -1）
	{
		int index = already_in_goodvar_stack[flipvar]; //获取 flipvar 在 goodvar_stack 中的索引位置。
		int last_v = mypop(goodvar_stack); //从 goodvar_stack 中弹出最后一个变量，这是为了将其放到 flipvar 的位置上。
		goodvar_stack[index] = last_v; //将最后一个变量放到 flipvar 的位置上，以保持堆栈的连续性。
		already_in_goodvar_stack[last_v] = index; //更新 last_v 在 already_in_goodvar_stack 中的索引位置。
		already_in_goodvar_stack[flipvar] = -1; //将 flipvar 标记为不在 goodvar_stack 中。
	}
	int i, v;
	for (i = 0; i < var_neighbor_count[flipvar]; ++i) //遍历与 flipvar 相邻的变量
	{
		v = var_neighbor[flipvar][i];
		if (score[v] > 0)
		{
			if (already_in_goodvar_stack[v] == -1)
			{
				already_in_goodvar_stack[v] = goodvar_stack_fill_pointer;
				mypush(v, goodvar_stack);
			}
		}
		else if (already_in_goodvar_stack[v] != -1)
		{
			int index = already_in_goodvar_stack[v];
			int last_v = mypop(goodvar_stack);
			goodvar_stack[index] = last_v;
			already_in_goodvar_stack[last_v] = index;
			already_in_goodvar_stack[v] = -1;
		}
	}
}



//描述了变量的翻转操作，它会更新子句的满足状态、变量的分数以及好的变量堆栈，以帮助局部搜索算法寻找更好的解。
void Satlike::flip(int flipvar)
{
	int i, v, c;
	int index;
	lit *clause_c;

	int org_flipvar_score = score[flipvar]; //将当前翻转变量 flipvar 的原始分数保存在 org_flipvar_score 变量中，以备后续使用
	cur_soln[flipvar] = 1 - cur_soln[flipvar]; //执行变量翻转操作，将当前变量 flipvar 的值取反，即从 0 切换到 1 或从 1 切换到 0

	for (i = 0; i < var_lit_count[flipvar]; ++i) //遍历flipvar变量对应的所有文字
	{
		c = var_lit[flipvar][i].clause_num; //获取当前文字的子句编号并将其存储在变量 c 中
		clause_c = clause_lit[c]; //获取子句 c 中的文字列表，并将其存储在 clause_c 中

		if (cur_soln[flipvar] == var_lit[flipvar][i].sense) //检查当前文字的赋值是否与变量翻转后的值相匹配，如果匹配，表示当前文字为真
		{
			++sat_count[c]; //增加子句 c 的满足计数
			if (sat_count[c] == 2) //sat_count from 1 to 2 ，需要更新相关变量的分数。
			{
				score[sat_var[c]] += clause_weight[c];
			}
			else if (sat_count[c] == 1) // sat_count from 0 to 1，从 0 变为 1，，需要更新相关变量的分数，并执行 sat(c) 函数来更新子句 c 的满足状态。
			{
				sat_var[c] = flipvar; //record the only true lit's var
				for (lit *p = clause_c; (v = p->var_num) != 0; p++) //初始化了一个指向 lit 结构体的指针 p，并将其初始化为指向子句的首个文字（clause_c 是一个指向文字的数组），当 var_num 为零时表示子句的结尾
				{
					score[v] -= clause_weight[c];
				}
				sat(c);
			}
		}
		else // cur_soln[flipvar] != cur_lit.sense 如果不匹配，表示当前文字为假
		{
			--sat_count[c]; //减少子句 c 的满足计数
			if (sat_count[c] == 1) //sat_count from 2 to 1 ，从 2 变为 1，需要更新相关变量的分数。
			{
				for (lit *p = clause_c; (v = p->var_num) != 0; p++)
				{
					if (p->sense == cur_soln[v])
					{
						score[v] -= clause_weight[c];
						sat_var[c] = v;
						break;
					}
				}
			}
			else if (sat_count[c] == 0) //sat_count from 1 to 0 ，从 1 变为 0，需要更新相关变量的分数，并执行 unsat(c) 函数来更新状态。
			{
				for (lit *p = clause_c; (v = p->var_num) != 0; p++)
				{
					score[v] += clause_weight[c];
				}
				unsat(c);
			} //end else if
		}	 //end else
	}

	//update information of flipvar
	score[flipvar] = -org_flipvar_score; //更新翻转变量 flipvar 的分数。分数减去之前保存的原始分数，因为变量翻转后分数会改变
	update_goodvarstack1(flipvar); //调用 update_goodvarstack1 函数来更新好的变量堆栈，以确保堆栈中只包含好的变量。
}

//用于打印找到的最佳解
void Satlike::print_best_solution()
{
	if (best_soln_feasible == 0)
		return;

	printf("v");
	for (int i = 1; i <= num_vars; i++)
	{
		printf(" ");
		if (best_soln[i] == 0) //如果 best_soln[i] 的值为 0，表示变量 i 被赋值为假（False），那么函数会打印一个减号 "-"
			printf("-");
		printf("%d", i);
	}
	printf("\n");
}

//用于验证当前解的有效性
bool Satlike::verify_sol()
{
	int c, j, flag;
	long long verify_unsat_weight = 0;

	for (c = 0; c < num_clauses; ++c)
	{
		flag = 0;
		for (j = 0; j < clause_lit_count[c]; ++j) //检查当前文字是否与解中的变量赋值匹配。如果匹配，将 flag 设置为 1，表示找到了满足该子句的文字，然后跳出循环
			if (best_soln[clause_lit[c][j].var_num] == clause_lit[c][j].sense)
			{
				flag = 1;
				break;
			}

		if (flag == 0) //如果 flag 仍然为 0，说明没有找到满足该子句的文字
		{
			if (org_clause_weight[c] == top_clause_weight) //verify hard clauses
			{
				//output the clause unsatisfied by the solution
				cout << "c Error: hard clause " << c << " is not satisfied" << endl; //如果是硬子句，则输出一条错误信息，指出哪个硬子句没有得到满足，然后返回 0，表示解无效

				cout << "c ";
				for (j = 0; j < clause_lit_count[c]; ++j)
				{
					if (clause_lit[c][j].sense == 0)
						cout << "-";
					cout << clause_lit[c][j].var_num << " ";
				}
				cout << endl;
				cout << "c ";
				for (j = 0; j < clause_lit_count[c]; ++j)
					cout << best_soln[clause_lit[c][j].var_num] << " ";
				cout << endl;
				return 0;
			}
			else
			{
				verify_unsat_weight += org_clause_weight[c]; //如果不是硬子句，则将当前子句的权重加到 verify_unsat_weight 中，以便后续验证软约束的不满足权重
			}
		}
	}

	if (verify_unsat_weight == opt_unsat_weight) //循环结束后，检查 verify_unsat_weight 是否等于 opt_unsat_weight
		return 1; //如果相等，说明解满足了所有约束，返回 1，表示解有效
	else
	{
		cout << "c Error: find opt=" << opt_unsat_weight << ", but verified opt=" << verify_unsat_weight << endl; //如果不相等，输出一条错误信息，指出找到的最优不满足权重 opt_unsat_weight 与验证的不满足权重 verify_unsat_weight 不匹配，然后返回 0，表示解无效。
	}
	return 0;
}

// 函数用于打印解的信息，包括不满足权重和优化时间。如果找到了可行解且解有效，它会输出这些信息；如果没有找到可行解，它会输出 -1 作为标记。如果找到的解无效，它会输出一个错误消息
void Satlike::simple_print()
{
	if (best_soln_feasible != 0)
	{
		if (verify_sol() == 1)
			cout << opt_unsat_weight << '\t' << opt_time << endl;
		else
			cout << "solution is wrong " << endl;
	}
	else
		cout << -1 << '\t' << -1 << endl;
}

//将子句标记为不满足
inline void Satlike::unsat(int clause)
{
	if (org_clause_weight[clause] == top_clause_weight)
	{
		index_in_hardunsat_stack[clause] = hardunsat_stack_fill_pointer;
		mypush(clause, hardunsat_stack);
		hard_unsat_nb++;
	}
	else
	{
		index_in_softunsat_stack[clause] = softunsat_stack_fill_pointer;
		mypush(clause, softunsat_stack);
		soft_unsat_weight += org_clause_weight[clause];
	}
}


//将子句标记为满足
inline void Satlike::sat(int clause)
{
	int index, last_unsat_clause;

	if (org_clause_weight[clause] == top_clause_weight)
	{
		last_unsat_clause = mypop(hardunsat_stack);
		index = index_in_hardunsat_stack[clause];
		hardunsat_stack[index] = last_unsat_clause;
		index_in_hardunsat_stack[last_unsat_clause] = index;

		hard_unsat_nb--;
	}
	else
	{
		last_unsat_clause = mypop(softunsat_stack);
		index = index_in_softunsat_stack[clause];
		softunsat_stack[index] = last_unsat_clause;
		index_in_softunsat_stack[last_unsat_clause] = index;

		soft_unsat_weight -= org_clause_weight[clause];
	}
}

#endif
