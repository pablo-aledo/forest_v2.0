int main () {
    // the inputs i wanna control
    char side_a;
    char side_b;
    char opcode;
    
    // the outputs i wanna observe
    char result;
    char zero;
    char carry_i;
    
    
   
    switch(opcode){
        case 0:
            result = side_a + side_b + carry_i;
            break;
        case 1:
            result = side_a - side_b - carry_i;
            break;
        case 2:
            result = --side_a;
            break;
        case 3:
            result = ++side_a;
            break;
    }
    if (result == 0){
        zero = 1;
    } else {
        zero = 0;
    }
    
    return result;
}

