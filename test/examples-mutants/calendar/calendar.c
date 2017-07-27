/*This program prints a calendar for a year specified. The user enters a
     year for the calendar and the programs automatically prints the calendar
     in text format.
     The codes are: daycode (0 = Sun, 1 = Mon, etc.)
                    leapyear (0 = no leap year, 1 = leap year)   */
#include <stdio.h>
#include <stdlib.h>       
#define TRUE 1
#define FALSE 0
int getdaycode (int year);
int getleapyear (int year);
void printcalendar (FILE *fout, int year, int daycode, int leapyear);
int getyear (void);

int main() {
   
   int year, daycode, leapyear; 
   
   FILE *fout;
   
   fout = fopen ("calendar.txt", "w");
   
   year = getyear();                           
   
   daycode = getdaycode (year);
   
   leapyear = getleapyear (year);
   
   printcalendar(fout, year, daycode, leapyear);
   
   printf("Open up \'calendar.txt\' to see your calendar...\n");
   
   system("pause");
     
}
     
int getyear (void)
{
int year;
printf ("Enter a year: ");
/*scanf ("%d", &year);*/
return year;
}             
int getdaycode (int year)
{
int daycode;
int x1, x2, x3;
	x1 = (year - 1.)/ 4.0;
	x2 = (year - 1.)/ 100.;
	x3 = (year - 1.)/ 400.;
daycode = (year + x1 - x2 + x3) %7;
return daycode;
}             
int getleapyear (int year)
{
	
//if((year% 4) == 0 );
if(year% 4==0 && year%100 != 0 || year%400==0)
   return TRUE;
   else return FALSE;	
		
}
void printcalendar (FILE *fout, int year, int daycode, int leapyear) //function header
{
	int  daysinmonth,     /* number of days in month currently 
                                                     being printed */
         day,       /* counter for day of month */
         month;     /* month = 1 is Jan, month = 2 is Feb, etc. */
     fprintf (fout,"                   %d", year);
     for ( month = 1; month <= 12; month++ ) {
          switch ( month ) { /* print name and set daysinmonth */
          case 1:
               fprintf(fout,"\n\nJanuary" );
               daysinmonth = 31;
               break;
          case 2:
               fprintf(fout,"\n\nFebruary" );
               daysinmonth = leapyear ? 29 : 28;
               break;
          case 3:
               fprintf(fout, "\n\nMarch" );
               daysinmonth = 31;
               break;
          case 4:
               fprintf(fout,"\n\nApril" );
               daysinmonth = 30;
               break;
          case 5:
               fprintf(fout,"\n\nMay" );
               daysinmonth = 31;
               break;
          case 6:
               fprintf(fout,"\n\nJune" );
               daysinmonth = 30;
               break;
          case 7:
               fprintf(fout,"\n\nJuly" );
               daysinmonth = 31;
               break;
          case 8:
               fprintf(fout,"\n\nAugust" );
               daysinmonth = 31;
               break;
          case 9:
               fprintf(fout,"\n\nSeptember" );
               daysinmonth = 30;
               break;
          case 10:
               fprintf(fout,"\n\nOctober" );
               daysinmonth = 31;
               break;
          case 11:
               fprintf(fout,"\n\nNovember" );
               daysinmonth = 30;
               break;
          case 12:
               fprintf(fout,"\n\nDecember" );
               daysinmonth = 31;
               break;
          }
          fprintf(fout,"\n\nSun  Mon  Tue  Wed  Thu  Fri  Sat\n" );
          /* advance printer to correct position for first date */
          for ( day = 1; day <= 1 + daycode * 5; day++ )
               fprintf(fout," " );
          /* print the dates for one month */
          for ( day = 1; day <= daysinmonth; day++ ) {
               fprintf(fout,"%2d", day );
               if ( ( day + daycode ) % 7 > 0 ) /* before Sat? */
                    /* move to next day in same week */
                    fprintf(fout,"   " );
               else  /* skip to next line to start with Sun */
                    fprintf(fout, "\n " );
          }
          /* set daycode for next month to begin */
          daycode = ( daycode + daysinmonth ) % 7;
     }
}
