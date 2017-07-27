int test_divide_by_zero_case(int number)
{
     int x = 1;
     int result;
     if (number)
     {
         result = 0 /*(x/(number-x))*/; /* True Positive (commented out) */
     } else {
         result = (x/(x-1)); /* False Positive: when number > 0 */
     }
     return result;
}

int main(void) {
     int number = 1;
     return test_divide_by_zero_case(number);
}
