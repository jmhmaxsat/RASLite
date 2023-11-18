#ifndef _DECI_H_
#define _DECI_H_

#include "basis_pms.h"

using namespace std;



class Decimation
{
  public:
    Decimation(lit **ls_var_lit, int *ls_var_lit_count, lit **ls_clause_lit, long long *ls_org_clause_weight, long long ls_top_clause_weight);

    void make_space(int max_c, int max_v);
    void free_memory();
    void init(int *ls_local_opt, int *ls_global_opt, lit *ls_unit_clause, int ls_unit_clause_count, int *ls_clause_lit_count);
    void push_unit_clause_to_queue(lit tem_l);
    void assign(int v, int sense);
    void remove_unassigned_var(int v);
    void hunit_propagation();
    void sunit_propagation();
    void random_propagation();
    void unit_prosess();
    bool choose_sense(int v);

    vector<int> fix;

    int num_vars;
    int num_clauses;

    long long *h_true_score;
    long long *h_false_score;
    long long *hscore;
    long long *s_true_score;
    long long *s_false_score;
    long long *sscore;

    lit **clause_lit;
    lit **var_lit;
    int *var_lit_count;

    int *local_opt;
    int *global_opt;
    long long *org_clause_weight;
    long long top_clause_weight;

    lit *hunit_clause_queue;
    int *sense_in_hunit_clause_queue;
    int hunit_beg_pointer;              //硬单元子句记录起点
    int hunit_end_pointer;              //硬单元子句记录终点

    lit *sunit_clause_queue;
    int *sense_in_sunit_clause_queue;
    int sunit_beg_pointer;              //软单元子句记录起点
    int sunit_end_pointer;              //软单元子句记录终点

    int *unassigned_var;                //未赋值变量
    int *index_in_unassigned_var;                 
    int unassigned_var_count;           //未赋值变量数量

    int *clause_delete;
    int *clause_lit_count;
};

Decimation::Decimation(lit **ls_var_lit, int *ls_var_lit_count, lit **ls_clause_lit, long long *ls_org_clause_weight, long long ls_top_clause_weight)
{
    var_lit = ls_var_lit;
    var_lit_count = ls_var_lit_count;
    clause_lit = ls_clause_lit;
    org_clause_weight = ls_org_clause_weight;
    top_clause_weight = ls_top_clause_weight;
}



//分配空间
void Decimation::make_space(int max_c, int max_v)
{
    num_vars = max_v;
    num_clauses = max_c;

    max_c += 10;
    max_v += 10;

    h_true_score = new long long[max_v];
    h_false_score = new long long[max_v];
    hscore = new long long[max_v];
    s_true_score = new long long[max_v];
    s_false_score = new long long[max_v];
    sscore = new long long[max_v];

    fix.resize(max_v);    //分配容器内存大小
    fix.reserve(max_v);   //设置容器容量大小

    hunit_clause_queue = new lit[max_v];
    sense_in_hunit_clause_queue = new int[max_v];

    sunit_clause_queue = new lit[max_v];
    sense_in_sunit_clause_queue = new int[max_v];

    unassigned_var = new int[max_v];
    index_in_unassigned_var = new int[max_v];

    clause_delete = new int[max_c];
    clause_lit_count = new int[max_c];
}


//释放空间
void Decimation::free_memory()
{
    fix.clear();
    delete[] h_true_score;
    delete[] h_false_score;
    delete[] hscore;
    delete[] s_true_score;
    delete[] s_false_score;
    delete[] sscore;

    delete[] hunit_clause_queue;
    delete[] sense_in_hunit_clause_queue;

    delete[] sunit_clause_queue;
    delete[] sense_in_sunit_clause_queue;

    delete[] unassigned_var;
    delete[] index_in_unassigned_var;

    delete[] clause_delete;
    delete[] clause_lit_count;
}



//初始化
void Decimation::init(int *ls_local_opt, int *ls_global_opt, lit *ls_unit_clause, int ls_unit_clause_count, int *ls_clause_lit_count)
{
    int v;
    int c;
    //parameters used in decimation
    hunit_beg_pointer = 0;
    hunit_end_pointer = 0;

    sunit_beg_pointer = 0;
    sunit_end_pointer = 0;

    unassigned_var_count = num_vars;

    //data structure of the instance
    local_opt = ls_local_opt;
    global_opt = ls_global_opt;

    for (int i = 0; i < num_vars; ++i)
    {
        v = i + 1;
        unassigned_var[i] = v;
        index_in_unassigned_var[v] = i;

        fix[v] = -1; //返回索引 v 在容器fix中所指的元素
        sense_in_hunit_clause_queue[v] = -1; // not in hunit queue
        sense_in_sunit_clause_queue[v] = -1; // not in sunit queue
    }

    for (int i = 0; i < num_clauses; ++i)
    {
        clause_lit_count[i] = ls_clause_lit_count[i];
        clause_delete[i] = 0;
    }

    for (int i = 0; i < ls_unit_clause_count; ++i)
    {
        push_unit_clause_to_queue(ls_unit_clause[i]);
    }

   
    
    //figout score
    //计算hscore和sscore
    for (v = 1; v <= num_vars; ++v)
    {
        h_false_score[v] = 0;
        h_true_score[v] = 0;
        s_false_score[v] = 0;
        s_true_score[v] = 0;
        for (int i = 0; i < var_lit_count[v]; ++i) //遍历变量 v 的所有文字     var_lit_count[v]：变量 v 的文字数量
        {
            c = var_lit[v][i].clause_num; //var_lit[v][i].clause_num：变量 v 的第 i 个文字所在的子句索引
            if (org_clause_weight[c] == top_clause_weight) //如果此文字所在的子句是硬子句
            {
                if (var_lit[v][i].sense == 1) //如果变量 v 的第 i 个文字是正文字
                    ++h_true_score[v];  //存储变量 v 在硬子句中正文字的数量
                else
                    ++h_false_score[v];  //存储变量 v 在硬子句中负文字的数量
            }
            else //此文字所在子句是软子句
            {
                if (var_lit[v][i].sense == 1)                  
                    s_true_score[v] += org_clause_weight[c];  //存储变量 v 在软子句中正文字所在子句的权值之和
                else
                    s_false_score[v] += org_clause_weight[c]; //存储变量 v 在软子句中负文字所在子句的权值之和
            }
        }
        hscore[v] = max(h_false_score[v], h_true_score[v]);  //存储变量 v 在硬子句中正负文字数量中较大的那一方
        sscore[v] = max(s_false_score[v], s_true_score[v]);  //存储变量 v 在软子句中正负文字权重之和中较大的那一方
    }
}



//将单元子句放入单元子句队列
void Decimation::push_unit_clause_to_queue(lit tem_l)
{
    int v = tem_l.var_num; //文字tem_1所在的变量索引，从1开始
    int c = tem_l.clause_num;  //文字tem_1所在的子句索引
    if (org_clause_weight[c] == top_clause_weight)  //如果文字tem_1所在子句是硬子句
    {
        if (sense_in_hunit_clause_queue[v] == -1)   //如果变量不在硬单元子句队列
        {
            sense_in_hunit_clause_queue[v] = tem_l.sense;  //
            hunit_clause_queue[hunit_end_pointer++] = tem_l;
        }
        else  //如果变量在硬单元子句队列
        {
            if (sense_in_hunit_clause_queue[v] != tem_l.sense) //conflict var in hard unit queue
            {
                sense_in_hunit_clause_queue[v] = -2; //means this variable is conflict in hard unit queue
            }
        }
    }
    else  //如果文字tem_1所在子句是软子句
    {
        if (sense_in_hunit_clause_queue[v] != -1)
            return; //be defined by hard unit queue

        if (sense_in_sunit_clause_queue[v] == -1)
        {
            sense_in_sunit_clause_queue[v] = tem_l.sense;
            sunit_clause_queue[sunit_end_pointer++] = tem_l;
        }
        else
        {
            if (sense_in_sunit_clause_queue[v] != tem_l.sense) //conflict var in hard unit queue
            {
                sense_in_sunit_clause_queue[v] = -3; //means this variable is conflict in hard unit queue
            }
        }
    }
}


//移除已赋值的变量，原位置被未赋值变量数组的最后一个变量替代
void Decimation::remove_unassigned_var(int v)
{
    int index = index_in_unassigned_var[v];   //v 在未赋值变量数组的索引
    int last_var = unassigned_var[--unassigned_var_count];  //未赋值变量数组的最后一个变量
    unassigned_var[index] = last_var;  //v 所在未赋值变量数组的位置让给此数组的最后一个变量
    index_in_unassigned_var[last_var] = index;  //未赋值变量数组的最后一个变量的索引变成 v 之前在此数组的索引
}



//给变量赋值
void Decimation::assign(int v, int sense)
{
    int c, l;
    lit tem_lit;
    fix[v] = sense; //容器的索引 v 所指的元素赋值为sense的值
    remove_unassigned_var(v);  //将已赋值变量移除未赋值变量数组

    for (int i = 0; i < var_lit_count[v]; ++i) //遍历 v 所代表的变量的所有文字
    {
        c = var_lit[v][i].clause_num; //第v个变量的第i个文字所在的子句索引
        if (clause_delete[c] == 1)
            continue;

        if (sense == var_lit[v][i].sense)
        {
            clause_delete[c] = 1;
            if (org_clause_weight[c] == top_clause_weight)  
            {
                for (int j = 0; j < clause_lit_count[c]; j++) //遍历这个子句的所有文字
                {
                    tem_lit = clause_lit[c][j];
                    if (tem_lit.sense == 1)
                    {
                        h_true_score[tem_lit.var_num]--;
                    }
                    else
                        h_false_score[tem_lit.var_num]--;
                    hscore[tem_lit.var_num] = max(h_true_score[tem_lit.var_num], h_false_score[tem_lit.var_num]);
                }
            }
            else
            {
                for (int j = 0; j < clause_lit_count[c]; j++)
                {
                    tem_lit = clause_lit[c][j];
                    if (tem_lit.sense == 1)
                    {
                        s_true_score[tem_lit.var_num] -= org_clause_weight[c];
                    }
                    else
                        s_false_score[tem_lit.var_num] -= org_clause_weight[c];
                    sscore[tem_lit.var_num] = max(s_true_score[tem_lit.var_num], s_false_score[tem_lit.var_num]);
                }
            }
            continue;
        }

        for (int j = 0; j < clause_lit_count[c]; j++)
        {
            if (clause_lit[c][j].var_num == v)
            {
                swap(clause_lit[c][j], clause_lit[c][--clause_lit_count[c]]);
                break;
            }
        }
        if (clause_lit_count[c] == 1)
        {
            push_unit_clause_to_queue(clause_lit[c][0]);
        }
    }
}



//随机选择一个sense值
bool Decimation::choose_sense(int v)
{
    return rand() % 2; //返回结果只有 0 和 1
}



//传播硬单元子句
void Decimation::hunit_propagation()
{
    int v, c, sense, rd;

    v = hunit_clause_queue[hunit_beg_pointer].var_num;
    sense = hunit_clause_queue[hunit_beg_pointer].sense;
    hunit_beg_pointer++;


    //sense：1代表将其赋值为真，0代表将其赋值为假
    if (sense_in_hunit_clause_queue[v] == -2)  //被选择的硬单元子句存在冲突时
    {
        if (sscore[v] > 0)  //该变量的得分大于0
        {
            if (sscore[v] == s_true_score[v])  
                sense = 1;
            else
                sense = 0;
        }
        else
        {
            sense = choose_sense(v);
        }
    }
    assign(v, sense);
}





//传播软单元子句
void Decimation::sunit_propagation()
{
    int v, c, sense, rd;

    int ht;
    ht = 15;

    int best_v = sunit_clause_queue[sunit_beg_pointer].var_num;
    int best_score = sscore[best_v];
    int index = sunit_beg_pointer;
    int count = sunit_end_pointer - sunit_beg_pointer;
    
    //如果单元软子句大于15时，使用BMS概率采样，此时令K=15
    if (count > 15)
    {
        for (int i = 0; i < 15; ++i)   
        {
            rd = rand() % count;

            v = sunit_clause_queue[sunit_beg_pointer + rd].var_num;
            if (sscore[v] > best_score)
            {
                best_v = v;
                index = sunit_beg_pointer + rd;
            }
        }
    }
    else
    {
        for (int i = sunit_beg_pointer; i < sunit_end_pointer; ++i)
        {
            v = sunit_clause_queue[i].var_num;
            if (sscore[v] > best_score)
            {
                best_v = v;
                index = i;
            }
        }
    }

    //将index位置与sunit_beg_pointer位置的元素进行互换，然后sunit_beg_pointer++就从数组sunit_clause_queue中删去了已经传播的单元子句了
    swap(sunit_clause_queue[sunit_beg_pointer], sunit_clause_queue[index]);
    v = sunit_clause_queue[sunit_beg_pointer].var_num;
    sense = sunit_clause_queue[sunit_beg_pointer].sense;
    sunit_beg_pointer++;

    if (fix[v] != -1) //传播后fix[v] = sense
        return;

    if (sense_in_sunit_clause_queue[v] == -3)
    {
        sense = choose_sense(v);
    }
    assign(v, sense);
}



//不存在单元子句时单元传播
void Decimation::random_propagation()
{
    int v, sense;
    v = unassigned_var[rand() % unassigned_var_count]; //产生0到unassigned_var_count-1的随机数
    sense = rand() % 2;                                   
    assign(v, sense);
}



//单元传播过程
void Decimation::unit_prosess()
{

    while (unassigned_var_count > 0)
    {
        if (hunit_beg_pointer != hunit_end_pointer)        
        {
            hunit_propagation();
        }
        else if (sunit_beg_pointer != sunit_end_pointer)   
        {
            sunit_propagation();
        } 
        else                                               
        {
            random_propagation();
        }
    }
}

#endif
