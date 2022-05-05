/* 
   Program to translate lex format to gap format.
*/

/* version 0.1 */

#include <stdio.h>
#include <string.h>

int
main(argc,argv)
     int argc;
     char *argv[];

{
	int vertices;

    int x;
 
    printf("Enter integer representing the number of vertices in the triangulations to be converted\n");
    scanf("%d", &x);

	vertices=x;

	if(vertices==10){
	char filename[200];
	int a, b, c, d, e, f, g, h, z, y, eul;
	for(a=0;a<10+1;a++){
		for(b=0;b<10+1;b++){
			for(c=0;c<10+1;c++){
				for(d=0;d<10+1;d++){
						for(f=0;f<10+1;f++){
								for(h=0;h<10+1;h++){
										for(y=0;y<10+1;y++){
					for(eul=0;eul<10+1;eul++){
						if(a+b+c+d+e+f+g+h+z+y==vertices){	
	sprintf(filename,"3-manifolds_%dv_%d_%d_%d_%d_0_%d_0_%d_0_%d_Eul%d.lex%c",vertices,a,b,c,d,f,h,y,eul,0);

	FILE *file = fopen (filename, "r");
	if (file != NULL){

		char line [ 128 ]; /* or other suitable maximum line size */

		

		//while ( fgets ( line, sizeof line, file ) != NULL ) /* read a line */
		//{

		//	fputs ( line, stdout ); /* write the line */

		//}
		//fclose ( file );

	//}

	//else
	//{

	//	perror ( filename ); /* why didn't the file open? */

	//}

	//return 0;
	
	
  char inputline[2000];
  char outputchunk[50];
  int v,i;
  int isurface;
  int ichar;
  int outputlen;
  int f0,f1,f2,f3,g2;
  int degree[100],j,f0new,tmp,n[20],maxdeg;

		char filename[100];
		
  isurface = 0;
  
  static FILE *outputfile;		
	
  sprintf(filename,"3-manifolds_%dv_%d_%d_%d_%d_0_%d_0_%d_0_%d",vertices,a,b,c,d,f,g,h,y);
		
  outputfile = fopen(filename, "w");
  int count=1;
  while (fgets(inputline, 2000, file) != NULL)
    {
		//fputs ( line, stdout ); /* write the line */

      isurface++;
      
      f3 = strlen(inputline)/4;
      f0 = 0;
      for (i=4*f3-1; i>=0; i--) {
	v = inputline[i]-'a';
	if (v+1 > f0) {
	  f0new = v+1;
	  for (j=f0; j<f0new; j++)
	    degree[j] = 0;
	  f0 = f0new;
	}
	degree[v]++;
      }
      for (v=4; v<f0; v++)
	n[v] = 0;
      maxdeg = 0;
      for (v=0; v<f0; v++) {
	degree[v] = degree[v]/2 + 2;
	if (degree[v] > maxdeg)
	  maxdeg = degree[v];
	n[degree[v]]++;
      }
      for (i=0; i<f0-1; i++)
	for (j=f0-1; j>i; j--)
	  if (degree[j-1] > degree[j]) {
	    tmp = degree[j-1];
	    degree[j-1] = degree[j];
	    degree[j] = tmp;
	  }
      f1 = f3 + f0;
      f2 = 2*f1 - 2*f0;
      g2 = f1 -4*f0 +10;

      ichar = 0;
      fprintf(stdout,"## %d, f = (%d,%d,%d,%d), g_2 = %d.\n##  deg = %d",
	      isurface,f0,f1,f2,f3,g2,degree[0]);
      for (v=1; v<f0; v++)
	fprintf(stdout,",%d",degree[v]);
      fprintf(stdout,"\n");
      fprintf(stdout,"##  n_4,... = %d",n[4]);
      for (v=5; v<=maxdeg; v++)
	fprintf(stdout,",%d",n[v]);
      
		//write to file now//
		
		fprintf(outputfile,"\n");
		fflush(outputfile);
		
		//put name of complex here//
		
	
		//fprintf(outputfile,"%d_%d_%d_%d_%d_%d_%d_%d_0_0_#%d=",a,b,c,d,e,f,g,h,count);
		
		
      sprintf(outputchunk,"[[%d,%d,%d,%d],",
	      inputline[ichar]-'a'+1,inputline[ichar+1]-'a'+1,
	      inputline[ichar+2]-'a'+1,inputline[ichar+3]-'a'+1);
      fprintf(outputfile,"%s",outputchunk);
      outputlen = strlen(outputchunk);
      ichar += 4;
      while (inputline[ichar] != 0 && inputline[ichar] != '\n') {
	if (inputline[ichar+4] != 0 && inputline[ichar+4] != '\n')
	  sprintf(outputchunk,"[%d,%d,%d,%d],",
		  inputline[ichar]-'a'+1,inputline[ichar+1]-'a'+1,
		  inputline[ichar+2]-'a'+1,inputline[ichar+3]-'a'+1);
	else
	  sprintf(outputchunk,"[%d,%d,%d,%d]]",
		  inputline[ichar]-'a'+1,inputline[ichar+1]-'a'+1,
		  inputline[ichar+2]-'a'+1,inputline[ichar+3]-'a'+1);
	ichar += 4;
	if (outputlen + strlen(outputchunk) > 72) {
	  //fprintf(outputfile,"\n  ");
	  outputlen = 1;
	}
	fprintf(outputfile,"%s",outputchunk);
	fflush(outputfile);
	outputlen += strlen(outputchunk);
      }
      
      
	  fprintf(stdout,"\n");
	  fflush(outputfile);
	  count++;
    }
  }
	fclose ( file );
		
						}	
	}
	}
	}
    }
	}
	}
	}
	}
	//exit(0);
	return 1;
	}
	
	
	//9 vertices or less//
	if(vertices<10){
	char filename[200];
	int a, b, c, d, e, f, g, h, z, y, eul;
	for(a=0;a<10+1;a++){
		for(b=0;b<10+1;b++){
			for(c=0;c<10+1;c++){
				for(d=0;d<10+1;d++){
					for(eul=0;eul<10+1;eul++){
						if(a+b+c+d+e+f+g+h+z+y==vertices){	
	sprintf(filename,"3-manifolds_%dv_%d_%d_%d_%d_%d_%d_%d_%d_%d_%d_Eul%d.lex%c",vertices,a,b,c,d,0,0,0,0,0,0,eul,0);

	FILE *file = fopen (filename, "r");
	if (file != NULL){

		char line [ 128 ]; /* or other suitable maximum line size */

		

		//while ( fgets ( line, sizeof line, file ) != NULL ) /* read a line */
		//{

		//	fputs ( line, stdout ); /* write the line */

		//}
		//fclose ( file );

	//}

	//else
	//{

	//	perror ( filename ); /* why didn't the file open? */

	//}

	//return 0;
	
	
  char inputline[2000];
  char outputchunk[50];
  int v,i;
  int isurface;
  int ichar;
  int outputlen;
  int f0,f1,f2,f3,g2;
  int degree[100],j,f0new,tmp,n[20],maxdeg;

		char filename[100];
		
  isurface = 0;
  
  static FILE *outputfile;		
	
  sprintf(filename,"3-manifolds_%dv_%d_%d_%d_%d_%d_%d_%d_%d_%d_%d",vertices,a,b,c,d,0,0,0,0,0,0);
		
  outputfile = fopen(filename, "w");
  int count=1;
  while (fgets(inputline, 2000, file) != NULL)
    {
		//fputs ( line, stdout ); /* write the line */

      isurface++;
      
      f3 = strlen(inputline)/4;
      f0 = 0;
      for (i=4*f3-1; i>=0; i--) {
	v = inputline[i]-'a';
	if (v+1 > f0) {
	  f0new = v+1;
	  for (j=f0; j<f0new; j++)
	    degree[j] = 0;
	  f0 = f0new;
	}
	degree[v]++;
      }
      for (v=4; v<f0; v++)
	n[v] = 0;
      maxdeg = 0;
      for (v=0; v<f0; v++) {
	degree[v] = degree[v]/2 + 2;
	if (degree[v] > maxdeg)
	  maxdeg = degree[v];
	n[degree[v]]++;
      }
      for (i=0; i<f0-1; i++)
	for (j=f0-1; j>i; j--)
	  if (degree[j-1] > degree[j]) {
	    tmp = degree[j-1];
	    degree[j-1] = degree[j];
	    degree[j] = tmp;
	  }
      f1 = f3 + f0;
      f2 = 2*f1 - 2*f0;
      g2 = f1 -4*f0 +10;

      ichar = 0;
      fprintf(stdout,"## %d, f = (%d,%d,%d,%d), g_2 = %d.\n##  deg = %d",
	      isurface,f0,f1,f2,f3,g2,degree[0]);
      for (v=1; v<f0; v++)
	fprintf(stdout,",%d",degree[v]);
      fprintf(stdout,"\n");
      fprintf(stdout,"##  n_4,... = %d",n[4]);
      for (v=5; v<=maxdeg; v++)
	fprintf(stdout,",%d",n[v]);
      
		//write to file now//
		
		fprintf(outputfile,"\n");
		fflush(outputfile);
		
		//put name of complex here//
		
	
		//fprintf(outputfile,"%d_%d_%d_%d_%d_%d_%d_%d_0_0_#%d=",a,b,c,d,e,f,g,h,count);
		
		
      sprintf(outputchunk,"[[%d,%d,%d,%d],",
	      inputline[ichar]-'a'+1,inputline[ichar+1]-'a'+1,
	      inputline[ichar+2]-'a'+1,inputline[ichar+3]-'a'+1);
      fprintf(outputfile,"%s",outputchunk);
      outputlen = strlen(outputchunk);
      ichar += 4;
      while (inputline[ichar] != 0 && inputline[ichar] != '\n') {
	if (inputline[ichar+4] != 0 && inputline[ichar+4] != '\n')
	  sprintf(outputchunk,"[%d,%d,%d,%d],",
		  inputline[ichar]-'a'+1,inputline[ichar+1]-'a'+1,
		  inputline[ichar+2]-'a'+1,inputline[ichar+3]-'a'+1);
	else
	  sprintf(outputchunk,"[%d,%d,%d,%d]]",
		  inputline[ichar]-'a'+1,inputline[ichar+1]-'a'+1,
		  inputline[ichar+2]-'a'+1,inputline[ichar+3]-'a'+1);
	ichar += 4;
	if (outputlen + strlen(outputchunk) > 72) {
	  //fprintf(outputfile,"\n  ");
	  outputlen = 1;
	}
	fprintf(outputfile,"%s",outputchunk);
	fflush(outputfile);
	outputlen += strlen(outputchunk);
      }
      
      
	  fprintf(stdout,"\n");
	  fflush(outputfile);
	  count++;
    }
  }
	fclose ( file );
		
						}	
	}
	}
	}
	}
	}
	//exit(0);
	return 1;
	}
	
	if (vertices>10) {
		printf("this will take too long");
		return 0;
	}

}
