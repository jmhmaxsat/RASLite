#ifndef _HEURISTIC_H_
#define _HEURISTIC_H_

#include "basis_pms.h"
#include "deci.h"



void Satlike::init(vector<int> &init_solution)
{
    soft_large_weight_clauses_count = 0; //大权重软子句数量
    //Initialize clause information
    for (int c = 0; c < num_clauses; c++)
    {
        already_in_soft_large_weight_stack[c] = 0; //大权重软子句标记
        clause_selected_count[c] = 0; //初始化子句被选中的次数为0

        if (org_clause_weight[c] == top_clause_weight)
            clause_weight[c] = 1; //如果是硬子句，则将子句权重初始化为1
        else
        {
            if (best_soln_feasible == 0) //如果找到的最佳解不可行
            {
                clause_weight[c] = 0; //将子句权重初始化为0
            }
            else //如果找到的最佳解可行
            {
                
                
                
                if (problem_weighted == 1)
                {
                    clause_weight[c] = org_clause_weight[c] + basis_clause_weight[c];
                }
                else
                {
                    clause_weight[c] = org_clause_weight[c];   //将软子句权重初始化为原始子句权重
                }
                
                 
                 

                
                if (clause_weight[c] > 1 && already_in_soft_large_weight_stack[c] == 0) //如果子句权重大于1且尚未标记为大权重软子句
                {
                    already_in_soft_large_weight_stack[c] = 1; //标记子句为大权重软子句
                    soft_large_weight_clauses[soft_large_weight_clauses_count++] = c; //将子句添加到大权重软子句堆栈，并增加大权重软子句数量计数器
                }
            }
        }
    }

    //init solution
    if (best_soln_feasible == 1) //如果找到的最佳解是可行解
    {
        best_soln_feasible = 2; //将 best_soln_feasible 设置为 2，这个值表示找到的最佳解是可行解但未被验证
        for (int v = 1; v <= num_vars; v++)
        {
            //cur_soln[v] = rand() % 2;
            time_stamp[v] = 0; //将变量 v 的时间戳设置为 0。这个时间戳通常用于跟踪变量的状态或操作时间
            unsat_app_count[v] = 0; //将变量 v 的不满足子句出现次数计数器设置为 0。这个计数器用于跟踪变量出现在多少个不满足的子句中
        }
    }
    else if (init_solution.size() == 0) //检查是否提供了自定义的初始解。init_solution 是一个存储初始解的容器
    {
        for (int v = 1; v <= num_vars; v++)
        {
            cur_soln[v] = rand() % 2; //如果没有提供自定义初始解，那么这里生成一个随机的 0 或 1 来初始化解中的变量 v
            time_stamp[v] = 0;
            unsat_app_count[v] = 0;
        }
    }
    else //如果提供了自定义的初始解，那么执行这个分支
    {
        for (int v = 1; v <= num_vars; v++)
        {
            cur_soln[v] = init_solution[v]; //将变量 v 的初始解设置为提供的自定义解。这个值可能是 0 或 1
            if (cur_soln[v] != 0 && cur_soln[v] != 1) //检查自定义的初始解是否是有效的（0 或 1）
                cur_soln[v] = rand() % 2;
            time_stamp[v] = 0;
            unsat_app_count[v] = 0;
        }
    }

    //init stacks
    hard_unsat_nb = 0;
    soft_unsat_weight = 0;
    hardunsat_stack_fill_pointer = 0;
    softunsat_stack_fill_pointer = 0;
    unsatvar_stack_fill_pointer = 0;
    large_weight_clauses_count = 0;

    /* figure out sat_count, sat_var and init unsat_stack */
    for (int c = 0; c < num_clauses; ++c)
    {
        sat_count[c] = 0; //将 sat_count 数组的第 c 个元素初始化为 0，用于跟踪子句 c 中满足的文字数量
        for (int j = 0; j < clause_lit_count[c]; ++j)
        {
            if (cur_soln[clause_lit[c][j].var_num] == clause_lit[c][j].sense)
            {
                sat_count[c]++;
                sat_var[c] = clause_lit[c][j].var_num;
            }
        }
        if (sat_count[c] == 0)
        {
            unsat(c);
        }
    }

    /*figure out score*/
    for (int v = 1; v <= num_vars; v++)
    {
        score[v] = 0;
        for (int i = 0; i < var_lit_count[v]; ++i)
        {
            int c = var_lit[v][i].clause_num;
            if (sat_count[c] == 0)
                score[v] += clause_weight[c];
            else if (sat_count[c] == 1 && var_lit[v][i].sense == cur_soln[v])
                score[v] -= clause_weight[c];
        }
    }

    //init goodvars stack
    goodvar_stack_fill_pointer = 0;
    for (int v = 1; v <= num_vars; v++)
    {
        if (score[v] > 0)
        {
            already_in_goodvar_stack[v] = goodvar_stack_fill_pointer;
            mypush(v, goodvar_stack);
        }
        else
            already_in_goodvar_stack[v] = -1;
    }

    //cout << goodvar_stack_fill_pointer << endl;
    //cout << hard_unsat_nb << endl;
    //cout << soft_unsat_weight << endl;
}


//用于选择要翻转的变量。
int Satlike::pick_var()
{
    int i, v;
    int best_var; //用于存储选择的最佳变量

    if (goodvar_stack_fill_pointer > 0) //检查是否有好的变量在堆栈中
    {
        if ((rand() % MY_RAND_MAX_INT) * BASIC_SCALE < rdprob)
            return goodvar_stack[rand() % goodvar_stack_fill_pointer]; //如果上述条件满足，将从好的变量堆栈中随机选择一个变量并返回

        if (goodvar_stack_fill_pointer < hd_count_threshold) //检查是否堆栈中的好变量数量小于BMS策略中的 k 值
        {
            best_var = goodvar_stack[0];
            for (i = 1; i < goodvar_stack_fill_pointer; ++i)
            {
                v = goodvar_stack[i];
                if (score[v] > score[best_var])
                    best_var = v;
                else if (score[v] == score[best_var]) //如果当前好变量的分数与最佳变量的分数相等，则继续比较它们的时间戳（time_stamp），以决定哪一个更优
                {
                    if (time_stamp[v] < time_stamp[best_var])
                        best_var = v;
                }
            }
            return best_var;
        }
        else
        {
            best_var = goodvar_stack[rand() % goodvar_stack_fill_pointer];
            for (i = 1; i < hd_count_threshold; ++i)
            {
                v = goodvar_stack[rand() % goodvar_stack_fill_pointer];
                if (score[v] > score[best_var])
                    best_var = v;
                else if (score[v] == score[best_var])
                {
                    if (time_stamp[v] < time_stamp[best_var])
                        best_var = v;
                }
            }
            return best_var;
        }
    }

    update_clause_weights(); //如果没有好的变量，将会更新子句权重

    int sel_c;
    lit *p;

    if (hardunsat_stack_fill_pointer > 0)
    {
        sel_c = hardunsat_stack[rand() % hardunsat_stack_fill_pointer]; //随机选择一个不满足的硬子句
    }
    else
    {
        sel_c = softunsat_stack[rand() % softunsat_stack_fill_pointer]; //随机选择一个不满足的软子句
    }
    if ((rand() % MY_RAND_MAX_INT) * BASIC_SCALE < rwprob)
        return clause_lit[sel_c][rand() % clause_lit_count[sel_c]].var_num; 

    best_var = clause_lit[sel_c][0].var_num;
    p = clause_lit[sel_c];
    for (p++; (v = p->var_num) != 0; p++) //迭代遍历选择子句中的所有文字，选择得分最高的变量
    {
        if (score[v] > score[best_var]) 
            best_var = v;
        else if (score[v] == score[best_var])
        {
            if (time_stamp[v] < time_stamp[best_var])
                best_var = v;
        }
    }

    return best_var;
}

void Satlike::local_search(char *inputfile)
{
    vector<int> init_solution; //创建一个名为 init_solution 的整数向量，用于存储初始解
    settings();
    for (tries = 1; tries < max_tries; ++tries)
    {
        init(init_solution); //调用 init 函数，使用初始解初始化问题实例
        for (step = 1; step < max_flips; ++step) //在每个尝试中，从1到 max_flips 执行变量翻转的步骤
        {
            if (hard_unsat_nb == 0 && (soft_unsat_weight < opt_unsat_weight || best_soln_feasible == 0))
            {
                if (soft_unsat_weight < opt_unsat_weight)
                {
                    best_soln_feasible = 1;
                    opt_unsat_weight = soft_unsat_weight;
                    opt_time = get_runtime();
                    for (int v = 1; v <= num_vars; ++v)
                        best_soln[v] = cur_soln[v];
                }
                if (opt_unsat_weight == 0)
                    return;
            }

            if (step % 1000 == 0) //检查当前步数是否为1000的倍数，用于控制在一定步数后检查是否需要结束搜索
            {
                double elapse_time = get_runtime(); //获取当前程序运行的时间
                if (elapse_time >= cutoff_time)
                    return;
                else if (opt_unsat_weight == 0)
                    return;
            }

            int flipvar = pick_var(); //选择一个变量 flipvar 进行翻转，具体选择的变量由 pick_var 函数决定
            flip(flipvar);
            time_stamp[flipvar] = step; //将选定的变量 flipvar 的时间戳更新为当前步数 step
        }
    }
}

void Satlike::local_search_with_decimation(char *inputfile)
{
    settings();
    Decimation deci(var_lit, var_lit_count, clause_lit, org_clause_weight, top_clause_weight); //创建一个 Decimation 对象 deci，并传递一些参数给它
    deci.make_space(num_clauses, num_vars); //为 Decimation 对象分配内存，以适应问题实例的规模

    opt_unsat_weight = __LONG_LONG_MAX__; //初始化优化的不满足权重为一个非常大的值
    for (tries = 1; tries < max_tries; ++tries)
    {       
        if (best_soln_feasible != 1)   //未找到可行解时，进行单元传播            
        {
            deci.init(local_opt_soln, best_soln, unit_clause, unit_clause_count, clause_lit_count);
            deci.unit_prosess();
            init(deci.fix); //使用单元传播后的解决方案进行初始化
        }
        else
            init(deci.fix);

        long long local_opt = __LONG_LONG_MAX__; //初始化局部最优解的不满足权重为一个非常大的值
        max_flips = max_non_improve_flip; //设置最大翻转次数为连续非改进的最大翻转次数
        for (step = 1; step < max_flips; ++step) //用于在给定的翻转次数内尝试改进解决方案
        {
            if (hard_unsat_nb == 0) //检查是否已经满足了所有硬子句
            {
                if (local_opt > soft_unsat_weight) //如果当前的局部最优解的不满足权重大于当前的不满足权重，则更新局部最优解的不满足权重和最大翻转次数
                {
                    local_opt = soft_unsat_weight;
                    max_flips = step + max_non_improve_flip;
                }
                if (soft_unsat_weight < opt_unsat_weight) //如果当前的不满足权重小于全局最优解的不满足权重，则更新全局最优解、最优不满足权重和优化时间
                {                    
                    cout << "o " << soft_unsat_weight << endl;
                    opt_unsat_weight = soft_unsat_weight;
                    opt_time = get_runtime();
                    for (int v = 1; v <= num_vars; ++v)
                        best_soln[v] = cur_soln[v];
                    



                    if (problem_weighted == 1)
                    {
                        for (int c = 0; c < num_clauses; ++c) 
                        {
                            if (org_clause_weight[c] == top_clause_weight) 
                            {
                                continue;
                            } 
                            else 
                            {
                                for (int k = 0; k < clause_lit_count[c]; ++k)
                                    if (best_soln[clause_lit[c][k].var_num] == clause_lit[c][k].sense)
                                    {
                                        basis_clause_weight[c] += 1;
                                        break;
                                    }
                            }
                        }
                    }

                    





                }
                if (best_soln_feasible == 0) 
                {
                    best_soln_feasible = 1;
                    break;
                }
            }
            //if(goodvar_stack_fill_pointer==0) cout<<step<<": 0"<<endl;
         
            if (opt_unsat_weight == 0)
            {                                 
                cout << "opt_unsat_weight == 0" << endl;
                simple_print();
                return;               
            }
            else if (get_runtime() >= 60 && print60 == 0)
            {                   
                print60 = 1;
                cout << "time limit:" << 60 << "s" << endl;
                simple_print();
            }    
            else if (get_runtime() >= cutoff)
            {
                cout << "time limit:" << cutoff << "s" << endl;
                simple_print();
                return;
            }

            int flipvar = pick_var();
            flip(flipvar);
            time_stamp[flipvar] = step;



        }
    }
}


void Satlike::increase_weights()
{
    int i, c, v;
    
    
    
    for (i = 0; i < hardunsat_stack_fill_pointer; ++i)
    {
        c = hardunsat_stack[i];
        clause_weight[c] += h_inc;

        if (clause_weight[c] == (h_inc + 1))
            large_weight_clauses[large_weight_clauses_count++] = c; //将子句索引 c 添加到大权重子句数组 large_weight_clauses 中，并递增 large_weight_clauses_count

        for (lit *p = clause_lit[c]; (v = p->var_num) != 0; p++)
        {
            score[v] += h_inc;
            if (score[v] > 0 && already_in_goodvar_stack[v] == -1)
            {
                already_in_goodvar_stack[v] = goodvar_stack_fill_pointer;
                mypush(v, goodvar_stack);
            }
        }
    }
    
    if (problem_weighted == 1)
    {
        for (i = 0; i < softunsat_stack_fill_pointer; ++i)
        {
            c = softunsat_stack[i];
            if (clause_weight[c] > softclause_weight_threshold)
                continue;
            else
                clause_weight[c]++;

            if (clause_weight[c] > 1 && already_in_soft_large_weight_stack[c] == 0)
            {
                already_in_soft_large_weight_stack[c] = 1;
                soft_large_weight_clauses[soft_large_weight_clauses_count++] = c;
            }
            for (lit *p = clause_lit[c]; (v = p->var_num) != 0; p++)
            {
                score[v]++;
                if (score[v] > 0 && already_in_goodvar_stack[v] == -1)
                {
                    already_in_goodvar_stack[v] = goodvar_stack_fill_pointer;
                    mypush(v, goodvar_stack);
                }
            }
        }
    }
    else
    {
        if (best_soln_feasible > 0){
            for (i = 0; i < softunsat_stack_fill_pointer; ++i)
            {
                c = softunsat_stack[i];
                if (clause_weight[c] > softclause_weight_threshold)
                    continue;
                else
                    clause_weight[c]++;

                if (clause_weight[c] > 1 && already_in_soft_large_weight_stack[c] == 0)
                {
                    already_in_soft_large_weight_stack[c] = 1;
                    soft_large_weight_clauses[soft_large_weight_clauses_count++] = c;
                }
                for (lit *p = clause_lit[c]; (v = p->var_num) != 0; p++)
                {
                    score[v]++;
                    if (score[v] > 0 && already_in_goodvar_stack[v] == -1)
                    {
                        already_in_goodvar_stack[v] = goodvar_stack_fill_pointer;
                        mypush(v, goodvar_stack);
                    }
                }
            }
        }
    }
    
    
}

void Satlike::smooth_weights()
{
    int i, clause, v;

    for (i = 0; i < large_weight_clauses_count; i++)
    {
        clause = large_weight_clauses[i];
        if (sat_count[clause] > 0) //检查当前子句是否已经被满足
        {
            clause_weight[clause] -= h_inc; //如果子句已被满足，就减少该子句的权重 

            if (clause_weight[clause] == 1) //检查子句的权重是否等于 1
            {
                large_weight_clauses[i] = large_weight_clauses[--large_weight_clauses_count]; //如果子句的权重降为 1，将其从具有大权重子句的列表中移除
                i--;
            }
            if (sat_count[clause] == 1) //检查改满足子句是否只有一个满足变量
            {
                v = sat_var[clause]; //获取该子句中的唯一满足字面值的变量
                score[v] += h_inc; //增加这个变量的分数 score，以实现平滑化
                if (score[v] > 0 && already_in_goodvar_stack[v] == -1)
                {
                    already_in_goodvar_stack[v] = goodvar_stack_fill_pointer;
                    mypush(v, goodvar_stack);
                }
            }
        }
    }


    if (problem_weighted == 1)
    {
        for (i = 0; i < soft_large_weight_clauses_count; i++)
        {
            clause = soft_large_weight_clauses[i];
            if (sat_count[clause] > 0)
            {
                clause_weight[clause]--;
                if (clause_weight[clause] == 1 && already_in_soft_large_weight_stack[clause] == 1) //检查子句的权重是否降到 1 并且它曾经在较大权重子句堆栈中
                {
                    already_in_soft_large_weight_stack[clause] = 0;
                    soft_large_weight_clauses[i] = soft_large_weight_clauses[--soft_large_weight_clauses_count];
                    i--;
                }
                if (sat_count[clause] == 1)
                {
                    v = sat_var[clause];
                    score[v]++;
                    if (score[v] > 0 && already_in_goodvar_stack[v] == -1)
                    {
                        already_in_goodvar_stack[v] = goodvar_stack_fill_pointer;
                        mypush(v, goodvar_stack);
                    }
                }
            }
        }
    }
    else
    {
        if (best_soln_feasible > 0){

            for (i = 0; i < soft_large_weight_clauses_count; i++)
            {
                clause = soft_large_weight_clauses[i];
                if (sat_count[clause] > 0)
                {
                    clause_weight[clause]--;
                    if (clause_weight[clause] == 1 && already_in_soft_large_weight_stack[clause] == 1) //检查子句的权重是否降到 1 并且它曾经在较大权重子句堆栈中
                    {
                        already_in_soft_large_weight_stack[clause] = 0;
                        soft_large_weight_clauses[i] = soft_large_weight_clauses[--soft_large_weight_clauses_count];
                        i--;
                    }
                    if (sat_count[clause] == 1)
                    {
                        v = sat_var[clause];
                        score[v]++;
                        if (score[v] > 0 && already_in_goodvar_stack[v] == -1)
                        {
                            already_in_goodvar_stack[v] = goodvar_stack_fill_pointer;
                            mypush(v, goodvar_stack);
                        }
                    }
                }
            }
        }
    }


    
}

//根据一定的概率条件来选择执行平滑权重操作或增加权重操作，这是算法的一个重要步骤，根据问题实例和算法状态来动态地调整子句的权重
void Satlike::update_clause_weights()
{
    if (((rand() % MY_RAND_MAX_INT) * BASIC_SCALE) < smooth_probability && large_weight_clauses_count > large_clause_count_threshold)
    {
        smooth_weights();
    }
    else
    {
        increase_weights();
    }
}

#endif