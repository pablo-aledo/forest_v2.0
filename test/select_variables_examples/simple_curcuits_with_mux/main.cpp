 int main () {
  int a = 0;
  int b = 0;
  int c = 0;
  
  int y_gm;
  int y_sat;
  
  int mux_1_sel;
  int mux_2_sel;
  int mux_3_sel;
  
  int mux_1_in_sat;
  int mux_2_in_sat;
  int mux_3_in_sat;
  
  // Golden Reference Model
  
    {
        int im_1;
        int im_2;
    
        im_1 = a & b;
        im_2 = c ^ im_1;
        y_gm = ~im_2;
    }
  
  
  // Buggy SAT Version
  {
  
    int im_1;
    int im_2;
    
    if (mux_1_sel){
        im_1 = mux_1_in_sat;
    } else {
         im_1 = a & b;
    }
    
    if (mux_2_sel){
        im_2 = mux_2_in_sat;
    } else {
        im_2 = c ^ im_1;
    }
    
    if (mux_3_sel) {
        y_sat = mux_3_in_sat;
    } else {
        // Model a stuck on fault --> no negation here!
        y_sat = im_2;//~im_2;
    }
    
  }
  
    if (y_gm == y_sat){
        return 1;
    } else {
        return 0;
    }
 }
