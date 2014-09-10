#include <iostream>
#include <fstream>

int val;

int f(int n){
if(n==0) {return 3;}
else if(n==1) {return 5;}
else {
val = 3*f(n-1);
val = val - 2*f(n-2);
printf("%d \n",val);
return val;
}
}

int main()
{
//printf("%d",f(4));
f(20);
}
