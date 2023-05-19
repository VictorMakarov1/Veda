module 1_learn;                  // C:\Veda\Veda22_learn
use 0_root;                                      
[ 
 // Chapter 1. Propositonal logic.  
 // Lesson 1. The basic propositional functions: negation, conjunction, disjunction, implication, equivalence. 
 // precedence(from highest to lowest): ~,&,or,==,->;
 // so ~p -> p1 == p2 or p3 & p4 means (~p) -> (p1 == (p2 or (p3 & p4)));
  
~p -> p1 == p2 or p3 & p4;   (~p) -> (p1 == (p2 or (p3 & p4)));   // same formulas;
// 16777216;                      // Lexical ERROR: glex: too big number ( > 16777215 = 2^24 - 1) 
//  true == g;    // ERROR: typdclterm: x does not fit t0= bool(0 1 43)
 
//--------------------Truth Table: you must remember it!!!--------------------------------
 ~true == false;  ~false == true;                                                                      // negation;
 true & true == true; true & false == false; false & true == false; false & false == false;            // conjunction;
 true or true == true; true or false == true; false or true == true; false or false == false;          // disjunction;
 (true -> true) == true; (true -> false) == false; (false -> true) == true; (false -> false) == true;  // implication;
 (true == true) == true; (true == false) == false; (false == true) == false; (false == false) == true;

 //  ~~p == p;  is Taut;         // Syntax ERROR: smpt: unary after unary
 // ~(~p == p;   is Taut;        // Syntax ERROR: waiting for )

 ~(~p) == p;   is Taut;          // OK

//  ~p == p;      is Taut;       // exit1:ERROR: hnis: not tautology Q= see above
 // write in the next line your own V text;

]  