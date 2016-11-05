#include"stdio.h"
#include"malloc.h"
#include"math.h"    
#include<cstring>
#include"source.h"
#include"windows.h"
void exchange(unsigned char *a,unsigned char *b)
{  
	unsigned char c;
   c=*a;
   *a=*b;
   *b=c;
}

//求矩阵的逆
int inv(unsigned char *p,int n)
{
	unsigned char *c = (unsigned char *)malloc(sizeof(unsigned char)* n*n);
  int *is,*js,i,j,k;
  int temp,fmax;
  is=(int *)malloc(n*sizeof(int));
  js=(int *)malloc(n*sizeof(int));
  for (i = 0; i < n*n; i++){
	  c[i] = p[i];
  }
  for(k=0;k<n;k++)
   {
      fmax=0;
      for(i=k;i<n;i++)
       for(j=k;j<n;j++)
        { 
		   temp=*(p+i*n+j);//找最大值
           if(temp>fmax)
           { 
			   fmax=temp;
               is[k]=i;js[k]=j;
            }
         }
     if(fmax==0)
       {  
		 free(is);
		 free(js);
 //        printf("     no inv\n");
         return(0);
       }
    if((i=is[k])!=k)
		for(j=0;j<n;j++){
			exchange((p+k*n+j),(p+i*n+j));//交换指针
		}
        
   if((j=js[k])!=k)
     for(i=0;i<n;i++)
        exchange((p+i*n+k),(p+i*n+j));  //交换指针
	p[k*n+k]= mul(1, inverse_table[p[k*n+k]]);
	
   for(j=0;j<n;j++)
     if(j!=k)
p[k*n+j] = mul(p[k*n+j],p[k*n+k]);
        //p[k*n+j]*=p[k*n+k];//主元行乘以主元的倒数（若主元为零，则矩阵不可逆，消元求逆过程终止），使主元变为1
   for(i=0;i<n;i++)
      if(i!=k)
        for(j=0;j<n;j++)
          if(j!=k)
             p[i*n+j]=p[i*n+j]^mul(p[i*n+k],p[k*n+j]);
   for(i=0;i<n;i++)//将 主元行乘以系数加到其他各行，使其他各行主元列元素消为零
     if(i!=k)
p[i*n+k] = mul(p[i*n+k],p[k*n+k]);
     //  p[i*n+k]*=-p[k*n+k];
 }
 for(k=n-1;k>=0;k--)
   {
     if((j=js[k])!=k)
        for(i=0;i<n;i++)
          exchange((p+j*n+i),(p+k*n+i));
     if((i=is[k])!=k)
        for(j=0;j<n;j++)
          exchange((p+j*n+i),(p+j*n+k));
  }
  free(is);
  free(js);
  return 1;
}

