#include "basis_pms.h"
#include "build.h"
#include "pms.h"
#include "heuristic.h"
#include <signal.h>  //系统头文件，提供了处理信号（例如中断信号）的功能


Satlike s;
void interrupt(int sig)
{
	s.print_best_solution();
	s.free_memory();
	exit(10);
}


// argc是命令行总的参数个数,argv[]是argc个参数，其中第0个参数是程序的全名，以后的参数命令行后面跟的用户输入的参数
//char argv[]是一个字符数组,其大小是int argc,主要用于命令行参数argv[]参数，数组里每个元素代表一个参数

int main(int argc, char *argv[]) 
     
{
	start_timing(); //调用了 start_timing 函数，用于开始计时，通常用于测量程序的运行时间。

	signal(SIGTERM, interrupt);//这一行代码用于设置信号处理程序。它告诉程序在接收到 SIGTERM 信号（通常表示程序终止信号）时，执行 interrupt 函数，即在程序被终止之前做一些清理工作。

	s.build_instance(argv[1]);

	s.settings();

	s.local_search_with_decimation(argv[1]);

	//s.simple_print();

	s.free_memory();

	return 0;
}
