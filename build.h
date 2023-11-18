#ifndef _BUILD_H_
#define _BUILD_H_

#include "basis_pms.h"

Satlike::Satlike() {}



void Satlike::settings()
{
    cutoff_time = 60;
    print60 = 0;
    if (problem_weighted == 1)  //加权组的实例
    {
        max_tries = 100000000;
        max_flips = 200000000;
        max_non_improve_flip = 10000000;

        large_clause_count_threshold = 0; //设置两个用于筛选子句的阈值，初始值都为 0，表示不使用这些阈值
        soft_large_clause_count_threshold = 0;

        rdprob = 0.01; //设置随机翻转的概率为 0.01，表示以 1% 的概率进行随机翻转
        hd_count_threshold = 15;  //设置用于 BMS 策略的硬限制的参数 k 为 15
        rwprob = 0.1; //设置加权机制 Weighting-MS 中的随机翻转概率为 0.1，表示以 10% 的概率进行随机翻转
        smooth_probability = 0.01; //设置加权机制 Weighting-MS 中的平滑概率为 0.01

        //接下来的条件是根据问题的性质和规模调整参数的值
        if ((top_clause_weight / num_sclauses) > 10000)    //如果这个条件成立，说明硬子句的权重相对较大，算法会采取较大的步骤和阈值
        {
            h_inc = 300;
            softclause_weight_threshold = 500;
        }
        else                                              
        {
            h_inc = 3;
            softclause_weight_threshold = 0;
        }

        if (num_vars > 2000)                              
        {
            rdprob = 0.01;
            hd_count_threshold = 15;   
            rwprob = 0.1;
            smooth_probability = 0.0000001;  
        }
    }
    else  //如果问题不是加权问题   
    {
        max_tries = 100000000;
        max_flips = 200000000;
        max_non_improve_flip = 10000000;

        large_clause_count_threshold = 0;
        soft_large_clause_count_threshold = 0;

        rdprob = 0.01;
        hd_count_threshold = 42;
        rwprob = 0.091;
        smooth_probability = 0.000003;

        h_inc = 1;
        softclause_weight_threshold = 400;

        if (num_vars < 1100) //for somall instances
        {
            h_inc = 1;
            softclause_weight_threshold = 0;
            rdprob = 0.01;
            hd_count_threshold = 15;  
            rwprob = 0;
            smooth_probability = 0.01;  
            return;
        }
    }
}





/*
构建变量之间的邻居关系
得到var_neighbor[v][i]和var_neighbor_count[v]
*/
void Satlike::build_neighbor_relation()
{
    int i, j, count;
    int v, c, n;
    int temp_neighbor_count;

    for (v = 1; v <= num_vars; ++v)
    {
        neighbor_flag[v] = 1; //将当前变量 v 标记为邻居标志 neighbor_flag 为1，表示它是 v 的一个邻居
        temp_neighbor_count = 0; //初始化一个临时邻居计数器 temp_neighbor_count 为0

        //嵌套的两个循环用于查找与变量 v 具有共同子句的其他变量，这些变量也被视为 v 的邻居
        for (i = 0; i < var_lit_count[v]; ++i)
        {
            c = var_lit[v][i].clause_num;
            for (j = 0; j < clause_lit_count[c]; ++j)
            {
                n = clause_lit[c][j].var_num;
                if (neighbor_flag[n] != 1) //如果 n 不是 v 自身，且 n 不是已经被标记为邻居的变量
                {
                    neighbor_flag[n] = 1;
                    temp_neighbor[temp_neighbor_count++] = n;
                }
            }
        }

        neighbor_flag[v] = 0;

        var_neighbor[v] = new int[temp_neighbor_count];
        var_neighbor_count[v] = temp_neighbor_count;

        count = 0;
        for (i = 0; i < temp_neighbor_count; i++)
        {
            var_neighbor[v][count++] = temp_neighbor[i];
            neighbor_flag[temp_neighbor[i]] = 0;
        }
    }
}




/*
从输入文件中构建问题实例的数据结构

初始化：
clause_lit_count[c] = 0;
clause_lit[c] = NULL;
var_lit_count[v] = 0;
var_lit[v] = NULL;
var_neighbor[v] = NULL;
problem_weighted
num_hclauses 
num_sclauses
max_clause_length = 0;
min_clause_length = 100000000;
unit_clause_count
best_soln_feasible = 0;

得到：
org_clause_weight[c]
problem_weighted
total_soft_weight
num_sclauses
num_hclauses
clause_lit_count[c]
clause_lit[c][i].clause_num、clause_lit[c][i].var_num 、clause_lit[c][i].sense
clause_lit[c][i].clause_num = -1  clause_lit[c][i].var_num = 0 结束标志
unit_clause[c]
max_clause_length
min_clause_length
var_lit[v][i]
var_lit_count[v] 
var_lit[v][var_lit_count[v]].clause_num = -1;结束标志

allocate_memory();
build_neighbor_relation();

*/
void Satlike::build_instance(char *filename)
{
    istringstream iss;//创建一个 istringstream 对象 iss，用于将字符串分解为更小的部分以进行解析
    string line;//定义一个字符串变量 line，用于存储从文件中读取的一行文本
    char tempstr1[10];//定义两个字符数组，用于临时存储读取的字符串
    char tempstr2[10];

    ifstream infile(filename); //打开一个名为 filename 的文件以供读取的输入文件流对象
    if (!infile)//检查文件是否成功打开，如果未成功打开，则输出错误消息并退出程序
    {
        cout << "c the input filename " << filename << " is invalid, please input the correct filename." << endl;
        exit(-1);
    }

    /*** build problem data structures of the instance ***/
    while (getline(infile, line))//循环读取文件的每一行
    {
        if (line[3] == 'n' && line[4] == 'v' && line[5] == 'a' && line[6] == 'r' && line[7] == 's')
        {
            line[line.length()-1] = '\0';
            int items = sscanf(line.c_str(), "%s %s %d", tempstr1, tempstr2, &num_vars);
        }
        
        if (line[3] == 'n' && line[4] == 'c' && line[5] == 'l' && line[6] == 's')
        {
            line[line.length()-1] = '\0';
            int items = sscanf(line.c_str(), "%s %s %d", tempstr1, tempstr2, &num_clauses);
            break;
        }
    }

    allocate_memory();

    int v, c;
    for (c = 0; c < num_clauses; c++)
    {
        clause_lit_count[c] = 0;
        clause_lit[c] = NULL;
    }
    for (v = 1; v <= num_vars; ++v)
    {
        var_lit_count[v] = 0;
        var_lit[v] = NULL;
        var_neighbor[v] = NULL;
    }

    int cur_lit;
    c = 0;
    problem_weighted = 0;
    partial = 0;
    num_hclauses = num_sclauses = 0;
    max_clause_length = 0;
    min_clause_length = 100000000;
    unit_clause_count = 0;
  

    int *redunt_test = new int[num_vars + 1];//创建一个整数数组 redunt_test，用于检测变量是否多次出现在同一子句中
    memset(redunt_test, 0, sizeof(int) * (num_vars + 1)); //数组初始化为零，表示每个变量都尚未出现在任何子句中
    
    //Now, read the clauses, one at a time.
    top_clause_weight = __LONG_LONG_MAX__;
    total_soft_weight = 0;
    while (getline(infile, line))//它用于从文件 infile 读取一行内容并将其存储在字符串变量 line 中
    {
        if (line[0] == 'c')
            continue;
        else if (line[0] == 'p')
        {
            int read_items;
            num_vars = num_clauses = 0;
            read_items = sscanf(line.c_str(), "%s %s %d %d %lld", tempstr1, tempstr2, &num_vars, &num_clauses, &top_clause_weight);

            if (read_items < 5)
            {
                cout << "read item < 5 " << endl;
                exit(-1);
            }
            //cout << top_clause_weight << endl;
            iss.clear();//清除输入流 iss 的状态标志，以准备解析下一行
            iss.str(line);//将字符串 line 赋值给输入流 iss，这样可以使用输入流的操作符 >> 来从 line 中提取数据
            iss.seekg(0, ios::beg);//将输入流 iss 的读取位置移动到字符串的开头
            continue;
        }
        else
        {
            iss.clear();
            iss.str(line);
            iss.seekg(0, ios::beg);
        }
        clause_lit_count[c] = 0;

        if (line[0] == 'h')
        {
            iss >> tempstr1;
            org_clause_weight[c] = __LONG_LONG_MAX__;
        }
        else
            iss >> org_clause_weight[c];

        if (org_clause_weight[c] != top_clause_weight)
        {
            if (org_clause_weight[c] != 1)
                problem_weighted = 1;
            total_soft_weight += org_clause_weight[c];
            num_sclauses++;
        }
        else
        {
            num_hclauses++;
            partial = 1;
        }

        iss >> cur_lit; //从输入流 iss 中读取一个文字，并存储在 cur_lit 变量中
        int clause_reduent = 0;
        while (cur_lit != 0) //如果 cur_lit 不等于 0，表示还有文字需要处理
        {
            if (redunt_test[abs(cur_lit)] == 0)//检查 redunt_test 数组中与当前文字的绝对值匹配的位置是否为 0。如果为 0，表示这是第一次遇到该文字
            {
                temp_lit[clause_lit_count[c]] = cur_lit;//将当前文字存储在 temp_lit 数组中，用于后续处理
                clause_lit_count[c]++;//增加子句中文字的计数
                redunt_test[abs(cur_lit)] = cur_lit;//将 redunt_test 数组中与当前文字的绝对值匹配的位置设置为当前文字，表示已经遇到该文字
            }
            else if (redunt_test[abs(cur_lit)] != cur_lit)//如果之前遇到了相同绝对值的文字，但不等于当前文字，则说明子句中存在矛盾变量
            {
                clause_reduent = 1;//将 clause_reduent 标志设置为 1，表示子句中存在矛盾变量的
                break;
            }
            iss >> cur_lit;
        }
        if (clause_reduent == 1)//如果该子句存在矛盾变量，那么这个子句永远不可能被满足
        {
            for (int i = 0; i < clause_lit_count[c]; ++i)
                redunt_test[abs(temp_lit[i])] = 0;

            num_clauses--;
            clause_lit_count[c] = 0;
            continue;
        }

        clause_lit[c] = new lit[clause_lit_count[c] + 1];//为子句分配内存，以存储子句中的文字

        int i;
        for (i = 0; i < clause_lit_count[c]; ++i)
        {
            clause_lit[c][i].clause_num = c;
            clause_lit[c][i].var_num = abs(temp_lit[i]);
            redunt_test[abs(temp_lit[i])] = 0;//清除 redunt_test 中的标记
            if (temp_lit[i] > 0)
                clause_lit[c][i].sense = 1;
            else
                clause_lit[c][i].sense = 0;

            var_lit_count[clause_lit[c][i].var_num]++;//增加与该文字相关的变量的计数
        }
        clause_lit[c][i].var_num = 0;//将子句结束标记存储在最后一个文字的 var_num 属性中
        clause_lit[c][i].clause_num = -1;//将子句结束标记存储在最后一个文字的 clause_num 属性中

         if (clause_lit_count[c] == 1) //如果子句中只有一个文字，表示这是一个单子句
            unit_clause[unit_clause_count++] = clause_lit[c][0];

        if (clause_lit_count[c] > max_clause_length) //如果当前子句中的文字数量大于 max_clause_length，则更新 max_clause_length
            max_clause_length = clause_lit_count[c];

        if (clause_lit_count[c] < min_clause_length) //如果当前子句中的文字数量小于 min_clause_length，则更新 min_clause_length
            min_clause_length = clause_lit_count[c];

        c++; //增加子句计数
    }

    infile.close();//关闭文件流，结束文件的读取

    //creat var literal arrays
    for (v = 1; v <= num_vars; ++v)
    {
        //unassigned_hard_only_var[v - 1] = v;
        //index_in_unassigned_hard_only_var[v] = v - 1;
        var_lit[v] = new lit[var_lit_count[v] + 1];
        var_lit_count[v] = 0; //reset to 0, for build up the array
    }
    //unassigned_hard_only_var_num = num_vars;
    //scan all clauses to build up var literal arrays
    for (c = 0; c < num_clauses; ++c)
    {
        
        
        basis_clause_weight[c] = 0;
        
        
        
        
        for (int i = 0; i < clause_lit_count[c]; ++i)
        {
            v = clause_lit[c][i].var_num;
            var_lit[v][var_lit_count[v]] = clause_lit[c][i];
            ++var_lit_count[v];
        }
    }
    
    for (v = 1; v <= num_vars; ++v)
        var_lit[v][var_lit_count[v]].clause_num = -1;

    build_neighbor_relation();

    best_soln_feasible = 0;
}




void Satlike::allocate_memory()
{
    int malloc_var_length = num_vars + 10;
    int malloc_clause_length = num_clauses + 10;

    unit_clause = new lit[malloc_clause_length];

    var_lit = new lit *[malloc_var_length];
    var_lit_count = new int[malloc_var_length];
    clause_lit = new lit *[malloc_clause_length];
    clause_lit_count = new int[malloc_clause_length];

    score = new long long[malloc_var_length];
    var_neighbor = new int *[malloc_var_length];
    var_neighbor_count = new int[malloc_var_length];
    time_stamp = new long long[malloc_var_length];
    neighbor_flag = new int[malloc_var_length];
    temp_neighbor = new int[malloc_var_length];

    org_clause_weight = new long long[malloc_clause_length];
    clause_weight = new long long[malloc_clause_length];
    sat_count = new int[malloc_clause_length];
    sat_var = new int[malloc_clause_length];
    clause_selected_count = new long long[malloc_clause_length];
    best_soft_clause = new int[malloc_clause_length];

    hardunsat_stack = new int[malloc_clause_length];
    index_in_hardunsat_stack = new int[malloc_clause_length];
    softunsat_stack = new int[malloc_clause_length];
    index_in_softunsat_stack = new int[malloc_clause_length];

    unsatvar_stack = new int[malloc_var_length];
    index_in_unsatvar_stack = new int[malloc_var_length];
    unsat_app_count = new int[malloc_var_length];

    goodvar_stack = new int[malloc_var_length];
    already_in_goodvar_stack = new int[malloc_var_length];

    cur_soln = new int[malloc_var_length];
    best_soln = new int[malloc_var_length];
    local_opt_soln = new int[malloc_var_length];

    large_weight_clauses = new int[malloc_clause_length];
    soft_large_weight_clauses = new int[malloc_clause_length];
    already_in_soft_large_weight_stack = new int[malloc_clause_length];

    best_array = new int[malloc_var_length];
    temp_lit = new int[malloc_var_length];



    basis_clause_weight = new long long [malloc_clause_length];




}

void Satlike::free_memory()
{
    int i;
    for (i = 0; i < num_clauses; i++)
        delete[] clause_lit[i];

    for (i = 1; i <= num_vars; ++i)
    {
        delete[] var_lit[i];
        delete[] var_neighbor[i];
    }

    delete[] var_lit;
    delete[] var_lit_count;
    delete[] clause_lit;
    delete[] clause_lit_count;

    delete[] score;
    delete[] var_neighbor;
    delete[] var_neighbor_count;
    delete[] time_stamp;
    delete[] neighbor_flag;
    delete[] temp_neighbor;

    delete[] org_clause_weight;
    delete[] clause_weight;
    delete[] sat_count;
    delete[] sat_var;
    delete[] clause_selected_count;
    delete[] best_soft_clause;

    delete[] hardunsat_stack;
    delete[] index_in_hardunsat_stack;
    delete[] softunsat_stack;
    delete[] index_in_softunsat_stack;

    delete[] unsatvar_stack;
    delete[] index_in_unsatvar_stack;
    delete[] unsat_app_count;

    delete[] goodvar_stack;
    delete[] already_in_goodvar_stack;

    //delete [] fix;
    delete[] cur_soln;
    delete[] best_soln;
    delete[] local_opt_soln;

    delete[] large_weight_clauses;
    delete[] soft_large_weight_clauses;
    delete[] already_in_soft_large_weight_stack;

    delete[] best_array;
    delete[] temp_lit;


    
    delete[] basis_clause_weight;




}

#endif
