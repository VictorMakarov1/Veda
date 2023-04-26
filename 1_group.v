module 1_group;                  // Newveda_C4: 1_group.v 
use 0_root;                                      
[                                
// var A,B,C,X,Y,Y1,Z,t, set; var f,x,x1,y,y1,z,F, any; var p,p1,p2,p3,q,r,P, bool; var d,d1,d2, abterm;   // move to root.v ???

// ----------------------1 Definition of group and some immediate theorems 
 group := {elg, * ;                                 
  // Axelg  := elg in set;                                 // Tfnin := f in fn(A,B) == f in FN &  dom(f)=A & im(f)<:B;
  Axm    := * in fn(elg#elg, elg);                         // typm: was wrong scope for fn(elg#elg, elg))
  AxAssoc:= A[x,y,z: elg, x*(y*z) = (x*y)*z ];             // Associativity of *
  Axeinv := Ex[{e,inv; Axe := e in elg; Axinv  := inv in fn(elg,elg)}, 
               (Axre := A[x:elg, x * e = x]) & (Axrinv := A[x: elg, x * inv(x) = e])];
}; // end group

// dcl[\\, any, any, any];     
// !! AxgroupIn := A[G,G1: group, G <: G1 == elg.G <: elg.G1 & *(group).G <: *(group).G1];  // did not work: error;
! Tingroup := [A,f] in group == f in fn(A#A,A) & A[x,y,z:A, f(x,f(y,z)) = f(f(x,y),z)] & 
                  E[e1:A, inv1:fn(A,A), A[x:A, f(x,e1) = x] & A[x:A, f(x,inv1(x)) = e1]];  byeq Axab; 
// !! Axassoc := assoc(f,A) == f in fn(A#A,A) & A[x,y,z:A, f(x,f(y,z)) = f(f(x,y),z)];
// ! Tingroup1 := [A,f] in group == assoc(f,A) & E[e1:A, inv1:fn(A,A), A[x:A, f(x,e1) = x] & A[x:A, f(x,inv1(x)) = e1]];
//  EqProof Tingroup1;
// F1 := [A,f] in group;             by Axab;

// F2 := f in fn(A#A,A) & A[x,y,z:A, f(x,f(y,z)) = f(f(x,y),z)] & 
//       E[e1:A, inv1:fn(A,A), A[x:A, f(x,e1) = x] & A[x:A, f(x,inv1(x)) = e1]]; by -Axassoc;

// F3 := assoc(f,A) & E[e1:A, inv1:fn(A,A), A[x:A, f(x,e1) = x] & A[x:A, f(x,inv1(x)) = e1]];
//  end EqProof Tingroup1;

// group4 := {elg, *, e, inv;                                 // Axelg0 := Set(elg);
//           x_elg  := {x; x in elg};
//           Axm    := * in fn(elg#elg, elg); 
//           Axe    := e in elg; 
//           Axinv  := inv in fn(elg, elg);   
//           AxAssoc:= A[x,y,z: elg, x*(y*z) = (x*y)*z ]; // Associativity           
//           Axre   := A[x_elg, x * e = x];               // right identity element
//           Axrinv := A[x_elg, x * inv(x) = e];         // right inverse         
//          }; // end def group4 
                                                  //  AllP := All(x,P(x));  !! AxAll := Allp -> AllP(a); ??? AxAll := All(x,P(x)) -> P(a)
// group4 :: [                                       //  ExP := Exist(x,P(x)); !! AxExist := ExP(a) -> ExP; 
// M2 := [elg,*];                                   // elg, * - from group4;
// ! TM42 := M2 in group; by Axab; Axm & AxAssoc & L2; // Axelg & // because Axelg was removed;
// ! L1 := Exist(inv1, inv1 in fn(elg,elg) & A[x_elg, x * inv1(x) = e]);     is Witness(inv);  // is  AxExist(L1(inv));
// ! L2 := Exist(e1, e1 in elg & A[x_elg, x*e1 = x] & Exist(inv1, inv1 in fn(elg,elg) & A[x_elg, x * inv1(x) = e1]));  is Witness(e); // is AxExist(L2(e));
// ]; // group4 ::

// ------------------------------2 Some elementary theorems, following from the definition of group

group :: [   var a,b,c,ax, elg; // 1               // FN is the class of all functions
G := [elg, *(group)];                              // !! Axassoc := assoc(f,A) == f in fn(A#A,A) & A[x,y,z:A, f(x,f(y,z)) = f(f(x,y),z)];
x_elg := {x; x in elg};
g_elg := {g; g in elg};                            // twice ???
! LG_type := G in group;                           by Axab; Axm & AxAssoc & Axeinv;
! Lassoc := assoc(*(group), elg);                  by Axassoc;         Axm & AxAssoc;
! TelgNemp := elg ~= {};                           is Tinnemp(Axe);    // Tinnemp := x in X -> X ~= {};;
! TelginP1 := elg in P1[elg];                      is TP1in(TelgNemp); // ! TP1in := X ~= {} -> X in P1[X];;  
! LCL2  := A[x,y:elg, x*y in elg];                 is Tfndp(Axm);      // ! Tfndp := f in fn(A#B,C) -> A[x:A,y:B, f(x,y) in C]; 
! LinvFN := inv in FN;                             is TfnFNA(Axinv);   // ! TfnFNA := f in fn(A,B) -> f in FN;             
! Linvdom := dom(inv) = elg;                       is Tfndom(Axinv);   // ! Tfndom := f in fn(A,B) -> dom(f) = A; 
// ! Linv3 := im(inv) = elg;                       is Tbfnim(Linv0);  // ! Tbfnim := f in bfn(A,B) -> im(f) = B;
! LCL1  := A[x:elg, inv(x) in elg];                is TfnA(Axinv);     // ! TfnA := f in fn(A, B) -> A[x:A, f(x) in B];
// ! LCL3 := A[x,y:elg, inv(x)*y*x in elg];           is typeaxiom;       // also follows fom LCL1, LCL2;
! Axre1 := a = a*e;                                by Axsym; is Axre;  // !! Axsym := u=v == v=u; // Axre   := A[x:elg, x * e = x];

! Tmsurj := im(*(group)) = elg;
 Proof Tmsurj; by Axext; L1 & L2;                      // ! Axext := X = Y == X <: Y & Y <: X;  
L0 := im(*(group)) = {z; E[x1:elg,x2:elg, z = x1*x2]}; is Tim2(Axm); // ! Tim2 := f in fn(A#B,C) -> im(f)={z; E[x1:A,x2:B, z=f(x1,x2)]};
L1 := im(*(group)) <: elg;                             is Tim2In(Axm); // ! Tim2In := f in fn(A#B,C) -> im(f) <: C;
L2 := elg <: im(*(group));                             by AxIn;        // !! AxIn := X2 <: Y2 == All(x, x in X2 -> x in Y2);
L3 := All(x, x in elg -> x in im(*(group)));
  Proof L3;
assume(x);
F0 := x in elg;                                    assume;
F01 := x = x * e;                                  is -Axre;           // Axre   := A[x:elg, x * e = x]// the decision formula;
F1 := x in im(*(group));                           by L0;
F2 := x in {z; E[x1:elg,x2:elg, z = x1*x2]};       by Axab;
F3 := E[x1:elg,x2:elg, x = x1*x2];                 is Witness(x,e);
  end Proof L3;
 end Proof Tmsurj;

! Tcancel_law1 := a*c = b*c -> a = b;              // Cancellation law (right); // ! Teqrm := A[a,b,c: elg, a = b == a*c = b*c];
 EqProof Tcancel_law1;
F0 := a*c = b*c;                                   assume;
F01 := c * inv(c) = e;                             is Axrinv;              // ! Axrinv := A[x: elg, x * inv(x) = e];
F02 := b*e = b;                                    is Axre;                // ! Axre   := A[x:elg, x * e = x];
F03 := a*e = a;                                    is Axre;
F1 := a;                                           by -F03;
F2 := a*e;                                         by -F01;
F3 := a*(c * inv(c));                              by AxAssoc(a,c,inv(c)); // a*(c*inv(c)) = (a*c) * inv(c);
F4 := (a*c) * inv(c);                              by F0;
F5 := (b*c) * inv(c);                              by -AxAssoc(b,c,inv(c));
F6 := b*(c * inv(c));                              by F01;
F7 := b*e;                                         by F02;
F8 := b;
 end EqProof Tcancel_law1;

! Tcancel_law1A := A[a,b,c: elg, a = b == a*c = b*c];
 Proof Tcancel_law1A;
F0 := a in elg;                                    assume;
F01 := b in elg;                                   assume;
F02 := c in elg;                                   assume;
G0 := a = b == a*c = b*c;                          by Deqv; L1 & L2;
L1 := a = b -> a*c = b*c;
  EqProof L1;
F0 := a = b;                                       assume;
F1 := a*c;                                         by F0;
F2 := b*c;
  end EqProof L1;
L2 :=  a*c = b*c -> a = b;                         is Tcancel_law1;
 end Proof Tcancel_law1A;

! Laaa := A[a:elg, a*a = a -> a = e];              // was: Laa1 := a*a = a -> a = e;
 EqProof Laaa;
F0 := a in elg;                                    assume;              // was an error, when absent;
F00 := a*a = a;                                    assume;
F01 := a * inv(a) = e;                             is Axrinv;           // ! Axrinv := A[x: elg, x * inv(x) = e];
F02 := a*e = a;                                    is Axre;             // ! Axre   := A[x:elg, x * e = x];
F1 := a;                                           by -F02;
F2 := a*e;                                         by -F01;
F3 := a*(a*inv(a));                                by AxAssoc(a,a,inv(a));
F4 := (a*a)*inv(a);                                by F00;
F5 := a * inv(a);                                  by F01;
F6 := e; 
 end EqProof Laaa;

! Laa2 := (inv(a)*a) * (inv(a)*a) = (inv(a)*a);    is Associnve;
! Tlinv := inv(ax)*ax = e;                         is Laaa(Laa2);    // inv(x) is also a left inverse of x;

! Tle := A[a:elg, e*a = a];                        // was Tle := e*a = a: Problems: instance(e*b,e*a) did not compute s, because e*a=e*b;
 EqProof Tle;                                      // e is also a left identity // was: ! Tle := A[a:elg, e * a = a];
F0 := a in elg;                                    assume;
F01 := a * inv(a) = e;                             is Axrinv;       // ! Axrinv := A[x: elg, x * inv(x) = e];
F02 := a*e = a;                                    is Axre;         // ! Axre   := A[x:elg, x * e = x];
F1 := e*a;                                         by -F01;
F2 := (a*inv(a))*a;                                by -AxAssoc;     //  AxAssoc:= A[x,y,z: elg, x*(y*z) = (x*y)*z ];  
F3 := a * (inv(a)*a);                              by Tlinv;
F4 := a * e;                                       by F02;
F5 := a;
 end EqProof Tle;

! Tle1 := a = e*a;                                 by Axsym; is Tle; // !! Axsym := u=v == v=u;

! Leqlm := A[c,a,b: elg, a = b -> c*a = c*b]; 
 EqProof Leqlm; 
F0 := c in elg;                                    assume;
F01 := a in elg;                                   assume;
F02 := b in elg;                                   assume;
F03 := a = b;                                      assume;
F1 := c*a;                                         by F03;
F2 := c*b;
 end EqProof Leqlm;

! Tcancel_law2 := c*a = c*b -> a = b;              // Cancellation law (left); // ! Teqrm := A[a,b,c: elg, a = b == a*c = b*c];
 Proof Tcancel_law2;
F0 := c*a = c*b;                                   assume; 
F1 := inv(c)*(c*a) = inv(c)*(c*b);                 is Leqlm(inv(c),c*a,c*b)(F0); by AxAssoc, AxAssoc;
F2 := (inv(c)*c)*a = (inv(c)*c)*b;                 by Tlinv;                     // ! Tlinv := inv(a)*a = e; 
F3 := e*a = e*b;                                   by Tle;                       // ! Tle := e*a = a;
F4 := a = b;
 end Proof Tcancel_law2;

! Teee := e*e = e;                                 is Tle; by Taut(p == (p==true));
! Teee1 := Teee == true;                           // is Taut(true==true);

! Tcancel_law2A := A[a,b,c: elg,  a = b == c*a = c*b];
 Proof Tcancel_law2A;
F0 := a in elg;                                    assume;
F01 := b in elg;                                   assume;
F02 := c in elg;                                   assume;
G0 := a = b == c*a = c*b;                          by Deqv; L1 & L2;
L1 := a = b -> c*a = c*b;
  EqProof L1;
F0 := a = b;                                       assume;
F1 := c*a;                                         by F0;
F2 := c*b;
  end EqProof L1;
L2 :=  c*a = c*b -> a = b;                         is Tcancel_law2;
 end Proof Tcancel_law2A;

! Tcancel_law2A1 := A[a,b,c: elg, c*a=c*b == a=b];  by Teqvsym; Tcancel_law2A;  // ! Teqvsym := (p==q) == (q==p);

! TeUnique := A[z:elg, A[x:elg, x * z = x] -> e = z];
 Proof TeUnique;
F0 := z in elg;                                    assume;
F01 := A[x:elg, x * z = x];                        assume;
F1 := e * z =  e;                                  is F01(e); by Tle;           // ! Tle := A[a:elg, e*a = a];  
F2 := z = e;                                       by Axsym;                    // !! Axsym := u=v == v=u;
F3 := e = z;
 end Proof TeUnique;

! Teqmr := A[a,x,b: elg, a*x = b == x = inv(a)*b];  
 EqProof Teqmr;
F0 := a in elg;                                   assume;
F01 := x in elg;                                  assume;
F02 := b in elg;                                  assume;
F1 :=  a*x = b;                                   by Tcancel_law2A(a*x, b,inv(a)); // Tcancel_law2A := A[a,b,c: elg, a = b == c*a = c*b];
F2 := inv(a)*(a*x) = inv(a)*b;                    by AxAssoc;
F3 := (inv(a)*a)*x = inv(a)*b;                    by Tlinv, Tle;  // ! Tlinv := inv(a)*a = e; 
F4 := x = inv(a)*b;                                    // Axsym := u=v == v=u;
 end EqProof Teqmr;

! Teqmr1 := A[a,x,b: elg, b = a*x == x = inv(a)*b];  by Axsym; Teqmr;

! Teqml := A[a,x,b: elg, x*a = b == x = b*inv(a)]; 
 EqProof Teqml;
F0 := a in elg;                                   assume;
F01 := x in elg;                                  assume;
F02 := b in elg;                                  assume;
F1 := x*a = b;                                    by Tcancel_law1A(x*a,b,inv(a)); // Tcancel_law1A := A[a,b,c: elg, a = b == a*c = b*c];
F2 := (x*a)*inv(a) = b*inv(a);                    by -AxAssoc;       
F3 := x*(a*inv(a)) = b*inv(a);                    by Axrinv, Axre;                // Axre   := A[x:elg, x * e = x];
F4 := x = b*inv(a);
 end EqProof Teqml;

! Teqml1 := A[a,x,b:elg, b=x*a == x = b*inv(a)];  by Axsym; Teqml;             // b = a*x == inv(a)*b = x; b:a, a:x. x:y;

! Teqer := A[x,a:elg, a*x = e == x = inv(a)];
 EqProof Teqer;
F0 := x in elg;                                  assume;
F01 := a in elg;                                 assume;
F1 := a*x = e;                                   by Teqmr;         // ! Teqmr := A[a,x,b: elg, a*x = b == x = inv(a)*b];
F2 := x = inv(a)*e;                              by Axre;          // Axre   := A[x:elg, x * e = x];
F3 := x = inv(a);
 end EqProof Teqer;

! Teqer1 := A[x,a:elg, a*x = e == inv(a) = x];   by Axsym; Teqer;
//  EqProof Teqer1;
// F0 := x in elg;                                  assume;
// F01 := y in elg;                                 assume;
// F1 := x*y = e;                                   by Axsym;         // !! Axsym := u=v == v=u;
// F2 := e = x*y;                                   by Teqer;         // ! Teqer := A[x,y:elg, e = x*y == y = inv(x)];
// F3 := y = inv(x);                                by Axsym;       
// F4 := inv(x) = y;
//  end EqProof Teqer1;                            // ??? hprs ??? was Teqer;

// ! Teqer2 := A[x,a:elg, a*x=e == x=inv(a);

! TinvUnique := A[f:fn(elg,elg), A[x:elg, x * f(x) = e] -> inv = f];
 Proof TinvUnique;
F0 := f in fn(elg,elg);                           assume; 
F01 := dom(f) = elg;                              is Tfndom(F0);  by -Linvdom;    // !! Tfndom := f in fn(A,B) -> dom(f) = A;
F02 := dom(f) = dom(inv);                         by Axsym;
F03 := dom(inv) = dom(f);
F04 := A[x:elg, x*f(x) = e];                      assume;                       // ! Linvdom := dom(inv) = elg; 
G0 := inv = f;                                    by Tfneq; F03 & G1; // !! Tfneq := A[f,g: FN, f=g == dom(f)=dom(g) & A[x:dom(f), f(x)=g(x)]];
G1 := A[x:dom(inv), inv(x) = f(x)];
  Proof G1;
H0 := x in dom(inv);                              assume; by Linvdom;
H01 := x in elg;
H1 := x*f(x) = e;                                 is F04; by Teqer1;  // ! Teqer1 := A[x,a:elg, a*x = e == inv(a) = x]; 
H2 := inv(x) = f(x);
  end Proof G1;
 end Proof TinvUnique; 

! Teqel := A[x,a:elg, x*a = e == x = inv(a)];   
 EqProof Teqel;
F0 := x in elg;                                  assume;
F01 := a in elg;                                 assume;
F1 := x*a = e;                                   by Teqml;            // ! Teqml := A[a,x,b: elg, x*a = b == x = b * inv(a)];
F2 := x = e * inv(a);                            by Tle;
F3 := x = inv(a);
 end EqProof Teqel;

! Teqel1 := A[x,a:elg, e = x*a == x = inv(a)];  by Axsym; Teqel;

! Tinve := inv(e) = e;                             // is Teqel(e,e)(Teee);
 Proof Tinve;
F1 := e*e = e == inv(e) = e;                     is Teqer1; by Teee1;            // ! Teqer1 := A[x,a:elg, a*x = e == inv(a) = x]; 
F3 := true == inv(e) = e;                        by Taut((true==p)==p); Tinve;   // ! Teee1 := Teee == true; // Teee := e*e = e;
// F4 := inv(e) = e;                             // error: no merging with Tinve;
 end Proof Tinve;               

! Tinv := A[x,y:elg, inv(x) = y == x = inv(y)];
 EqProof Tinv;
F0 := x in elg;                                  assume;
F01 := y in elg;                                 assume;
F1 := inv(x) = y;                                by Tcancel_law2A(inv(x),y,x); // Tcancel_law2A := A[a,b,c: elg, a = b == c*a = c*b];
F2 := x * inv(x) = x*y;                          by Axrinv;
F3 := e = x*y;                                   by Teqel1;  // ! Teqel1 := A[x,a:elg, e = x*a == x = inv(a)]; 
F4 := x = inv(y);
 end EqProof Tinv;

! Tinvmlt := A[x,y:elg, inv(x*y) = inv(y) * inv(x)];
 Proof Tinvmlt;
F0 := x in elg;                                assume;
F01 := y in elg;                               assume; //  a:(x*y) X:(inv(y)*inv(x)) = e;
F1 := (x*y)* (inv(y)*inv(x)) = e;              is Associnve; by Teqer1;  // ! Teqer1 := A[x,a:elg, a*x = e == inv(a) = x]; 
F2 := inv(x*y) = inv(y) * inv(x);    
 end Proof Tinvmlt;

! Tinvinv := A[x:elg, inv(inv(x)) = x];
 Proof Tinvinv;
F0 := x in elg;                                assume;
F1 := inv(x * inv(x)) = inv(inv(x)) * inv(x);  is Tinvmlt(x,inv(x)); by Axrinv,Tinve;
F2 := e = inv(inv(x)) * inv(x);                by Tcancel_law1A(e, inv(inv(x)) * inv(x), x);  
F3 := e * x = (inv(inv(x)) * inv(x)) * x;      by Tle, -AxAssoc, Tlinv,Axre;    // ! Tlinv := inv(a)*a = e;
F4 := x = inv(inv(x));                         by Axsym;                        // Axre   := A[x:elg, x * e = x];       
F5 := inv(inv(x)) = x;
 end Proof Tinvinv;

! Teqmr2 := A[a,x,b: elg, b = inv(a)*x == x = a*b];  byeq Teqmr1, Tinvinv;      // ! Teqmr1 := A[a,x,b: elg, b = a*x == x = inv(a)*b];

! Tinvmlt1 := A[x,y:elg, inv(inv(x)*y) = inv(y)*x];  byeq Tinvmlt, Tinvinv;

! Tinvm1 := A[x,y:elg, e = inv(x) * y == x = y];
 EqProof Tinvm1;
F0 := x in elg;                                assume;
F01 := y in elg;                               assume;
F1 := e = inv(x) * y;                          by Tcancel_law2A(e,inv(x)*y,x);  // Tcancel_law2A := A[a,b,c: elg, a = b == c*a = c*b];
F2 := x*e = x*(inv(x)*y);                      by Axre,AxAssoc,Axrinv,Tle;      // Axre   := A[x:elg, x * e = x];
F3 := x = y;
 end EqProof Tinvm1;

! Tinvm2 := A[x,y:elg, e = x * inv(y) == x = y]; 
 EqProof Tinvm2;
F0 := x in elg;                                assume;
F01 := y in elg;                               assume;
F1 := e = x * inv(y);                          by Tcancel_law1A(e,x*inv(y),y);  // Tcancel_law1A := A[a,b,c: elg, a = b == a*c = b*c];
F2 := e*y = (x*inv(y))*y;                      by Tle,-AxAssoc,Tlinv,Axre,Axsym;
F3 := x = y;
 end EqProof Tinvm2;

! Tinvm2a := A[x,y:elg, x * inv(y) = e == x = y]; by Axsym; Tinvm2;        // Axsym := u=v == v=u;

! Tinvdom := dom(inv) = elg;                   is Tfndom(Axinv); // Tfndom := f in fn(A,B) -> dom(f) = A; Axinv := inv in fn(elg,elg);

! L04 := A[y:elg, E[x:elg, y = inv(x)]];
 Proof L04;
F0 := y in elg;                               assume;                     // ! Tinvinv := A[x:elg, inv(inv(x)) = x];
F01 := y = inv(inv(y));                       by Axsym; is Tinvinv(y);    // Axsym := u=v == v=u;
F1 := E[x:elg, y = inv(x)];                   is Witness(inv(y));
 end Proof L04;
                                                          // ! Tinvsurj:  inv|elg is a surjective function;
! Tinvsurj := im(inv) = elg;    is Tfnim1a(Axinv & L04);  // ! Tfnim1a := f in fn(A,B) & A[y:B, E[x:A, y = f(x)]] -> im(f) = B;     
                                                          // Axinv := inv in fn(elg,elg);
! Teqme := A[x,y:elg, x*y = x -> y=e]; 
 Proof Teqme;
F0 := x in elg;                     assume;
F01 := y in elg;                    assume;
F02 := x*y = x;                     assume;  by Tcancel_law2A(x*y,x,inv(x)); // Tcancel_law2A := A[a,b,c: elg, a = b == c*a = c*b];
F1 := inv(x)*(x*y) = inv(x)*x;      by AxAssoc,Tlinv,Tle; // ,Tlinv; ??? mm ??? 8.15.20 rep2i replaces all instances ???
F2 := y = e;
 end Proof Teqme;
                                                        // !! Axinv  := inv in fn(elg,elg);                          
// ! L05 := dom(inv|elg) = elg;        is TredomFn(Axinv); // ! TredomFn := f in Fn(A,B) -> dom(f|A) = A; // L05,L06 not used; 11.19.20
// ! L06 := inv|elg in fn(elg,elg);

! Tinvinj0 := A[x,y:elg, inv(x)=inv(y) -> x=y]; 
 Proof Tinvinj0;                            
F0 := x in elg;                     assume;
F01 := y in elg;                    assume;
F02 := inv(x) = inv(y);             assume; by Tcancel_law2A(inv(x),inv(y),x);
F1 := x*inv(x) = x*inv(y);          by Axrinv;
F2 := e = x*inv(y);                 by Tinvm2; // ! Tinvm2 := A[x,y:elg, e = x * inv(y) == x = y]; 
F3 := x = y;
 end Proof Tinvinj0;
                                    // ! TAeqimp := A[x,y:A, G(x)=G(y) -> x=y] -> A[x,y:A, G(x)=G(y) == x=y];           
! Tinvinj := A[x,y: elg, inv(x)=inv(y) == x=y]; is TAeqimp(Tinvinj0); 
                                                        
! Tinvinj1 := injective(inv);       by  Axinj; Tinvinj0; // !! Axinj := A[f:FN, injective(f) == A[x1,x2: dom(f), f(x1) = f(x2) -> x1 = x2]];

                                    //  ! Tbfnin1 := f in bfn(A,B) == f in fn(A,B) & injective(f) & im(f) = B;
! Tinvbfn := inv in bfn(elg,elg);   by Tbfnin1;  Axinv & Tinvinj1 & Tinvsurj;  

dcl[conj, fn(elg#elg,elg)];         // CHECK: conj(x,y) in elg !!! // no such a problem if another def: conj := F[x,y:elg, x*y*inv(x)];
!! Axconj := A[x,y:elg, conj(x,y) = x*y*inv(x)];
// ! Lconj_type := conj in fn(elg#elg, elg);

Felgax := F[x:elg, a*x];            // a is a variable of type elg;

! Lmbfn0 := A[x:elg, a*x in elg];   // ??? is LCL2;
 Proof Lmbfn0;
F0 := x in elg;                     assume;
G0 := a*x in elg;                   is LCL2(a,x);       // ! LCL2  := A[x,y:elg, x*y in elg];
 end Proof Lmbfn0;

Felgxa := F[x:elg, x*a];             // a is a variable of type elg;
! Lmbfn1a := Felgax in fn(elg, elg); by TFinfn1; Lmbfn0; // ! TFinfn1 := F[x:A, G(x)] in fn(A,B) ==  A[x:A, G(x) in B];

! Lmbfn1b := injective(Felgax); 
 Proof Lmbfn1b;    by TFinj;         // ! TFinj := injective(F[x:A, G(x)]) == A[x1,x2:A, G(x1)=G(x2) -> x1=x2];
L1 := A[x1,x2:elg, a*x1 = a*x2 -> x1 = x2];
  Proof L1;
F0 := x1 in elg;               assume;
F01 := x2 in elg;              assume;
F02 := a*x1 = a*x2;            assume; by -Tcancel_law2A(x1,x2,a); // Tcancel_law2A := A[a,b,c: elg, a = b == c*a = c*b];
F1 := x1 = x2;                 // no error was discovered: by Tcancel_law2A(a*x1,a*x2,a); 
  end Proof L1;
 end Proof Lmbfn1b;
                               // ! TFim1 := im(FAGx)=B == FAGx in fn(A,B) && A[y:B, E[x:A,y=G(x)]];
! Lmbfn1c := im(Felgax) = elg; 
 Proof Lmbfn1c;                by TFim1; Lmbfn1a & L1;
L1 := A[y:elg, E[x:elg, y = a*x]];
  Proof L1;
F0 := y in elg;                assume;
F01 := y = a*(inv(a)*y);       is Associnve;
G0 := E[x:elg, y = a*x];       is Witness(inv(a)*y);
  end Proof L1;
 end Proof Lmbfn1c;

! TRelgl := R[x:elg, a*x] = elg;  by -TimF; Lmbfn1c; // ! Lmbfn1c := im(Felgax) = elg; by TimF;  // ! TimF   := im(F[d, g]) = R[d, g]; 
                               // ! Tbfnin1 := f in bfn(A,B) == f in fn(A,B) & injective(f) & im(f) = B;
// ! Tmbfn1 := A[a:elg, F[x:elg, a*x] in bfn(elg, elg)];

! Lmbfn2 := A[x:elg, x*a in elg];    // ??? is LCL2;
 Proof Lmbfn2;
F0 := x in elg;                      assume;
G0 := x*a in elg;                    is LCL2(x,a);       // ! LCL2  := A[x,y:elg, x*y in elg];
 end Proof Lmbfn2;

! Lmbfn2a := Felgxa in fn(elg, elg); by TFinfn1; Lmbfn2; // ! TFinfn1 := F[x:A, G(x)] in fn(A,B) ==  A[x:A, G(x) in B];

! Lmbfn2b := injective(Felgxa); 
 Proof Lmbfn2b;    by TFinj;    // ! TFinj := injective(F[x:A, G(x)]) == A[x1,x2:A, G(x1)=G(x2) -> x1=x2];
L1 := A[x1,x2:elg, x1*a = x2*a -> x1 = x2];
  Proof L1;
F0 := x1 in elg;               assume;
F01 := x2 in elg;              assume;
F02 := x1*a = x2*a;            assume; by -Tcancel_law1A(x1,x2,a); // Tcancel_law1A := A[a,b,c: elg, a = b == a*c = b*c];
F1 := x1 = x2;                 // no error was discovered: by Tcancel_law1A(x1*a,x2*a,a);
  end Proof L1;
 end Proof Lmbfn2b;
                                                       
! Lmbfn2c := im(Felgxa) = elg;                         //   Felgxa := F[x:elg, x*a]; 
 Proof Lmbfn2c;                by TFim1; Lmbfn2a & L1; // ! TFim1 := im(FAGx)=B == FAGx in fn(A,B) && A[y:B, E[x:A,y=G(x)]];
L1 := A[y:elg, E[x:elg, y = x*a]];
  Proof L1;
F0 := y in elg;                assume;
F01 := y = (y*inv(a))*a;       is Associnve;                        // was F01 := y = a*(inv(a)*y): error!
G0 := E[x:elg, y = x*a];       is Witness(y*inv(a));
  end Proof L1;
 end Proof Lmbfn2c;    

! Tmbfn2 := Felgxa in bfn(elg,elg); by Tbfnin1; Lmbfn2a & Lmbfn2b & Lmbfn2c;      
                                                                   // wiki: A/B = A*inv(B) is sometimes called right division;
! TRelgr := R[x:elg, x*a] = elg;  by -TimF; Lmbfn2c;               // ! TimF   := im(F[d, g]) = R[d, g];

! TE1rdiv := A[y,z:elg, E1[x:elg, y = x*z]];   // ! Teqmr := A[a,x,b: elg, a*x = b == x = inv(a)*b];  
 Proof TE1rdiv;    
F0 := y in elg;                assume;
F01 := z in elg;               assume;
F02 := y = y*inv(z)*z;         is Associnve;
G0 := E1[x:elg, y = x*z];      by TE1a; G1 & G2;    // ! TE1a := E1[x:A, P(x)] == E[x:A, P(x)] & A[x1,x2:A, P(x1) & P(x2) -> x1=x2]];
G1 := E[x:elg, y = x*z];       is Witness(y*inv(z));
G2 := A[x1,x2:elg, y = x1*z & y = x2*z -> x1=x2];
  Proof G2;
H0 := x1 in elg;               assume;
H01 := x2 in elg;              assume;              // b = a*x == inv(a)*b = x; b:a, a:x. x:y;           
H02 := y = x1*z;               assume; by Teqml1;   // ! ! Teqml1 := A[a,x,b: elg, b = x*a == x = inv(a)*b]; by Axsym; Teqml; 
H1 := x1 = y*inv(z);
H03 := y = x2*z;               assume; by Teqml1;
H2 := x2 = y*inv(z);
H3 := x1=x2;                   is Axeq2(H1 & H2);  // !! Axeq2 := x=a & y=a -> x=y;
  end Proof G2;
 end Proof TE1rdiv;
  
! TE1ldiv := A[y,z:elg, E1[x:elg, y = z*x]];
 Proof TE1ldiv;    
F0 := y in elg;                assume;
F01 := z in elg;               assume;
F02 := y = z*(inv(z)*y);       is Associnve;
G0 := E1[x:elg, y = z*x];      by TE1a; G1 & G2;    // ! TE1a := E1[x:A, P(x)] == E[x:A, P(x)] & A[x1,x2:A, P(x1) & P(x2) -> x1=x2]];
G1 := E[x:elg, y = z*x];       is Witness(inv(z)*y);
G2 := A[x1,x2:elg, y = z*x1 & y = z*x2 -> x1=x2];
  Proof G2;
H0 := x1 in elg;               assume;
H01 := x2 in elg;              assume;
H02 := y = z*x1;               assume; by Teqmr1;   // ! Teqmr1 := A[a,x,b: elg, b = a*x == x = inv(a)*b]; 
H1 := x1 = inv(z)*y;
H03 := y = z*x2;               assume; by Teqmr1;
H2 := x2 = inv(z)*y;
H3 := x1=x2;                   is Axeq2(H1 & H2);  // !! Axeq2 := x=a & y=a -> x=y;
  end Proof G2;
 end Proof TE1ldiv;
 
! Telge := elg ~= {e} == E[x:elg, x ~= e];          // use TSin2E; /// ! TSin2E := a in A & A ~= {a} == E[b:A, b ~= a];
 Proof Telge;                                by Deqv; L1 & L2;
L1 := elg ~= {e} -> E[x:elg, x ~= e];
  Proof L1;
F0 := elg ~= {e};                            assume;
G0 := E[x:elg, x ~= e];                      is TSin2E(Axe & F0);  // Axe    := e in elg; 
  end Proof L1;
L2 := E[x:elg, x ~= e] ->  elg ~= {e};     // by Reductio ad absurdum
  Proof L2;
F0 := Ex[x:elg, F01 := x ~= e];              assume; 
F02 := elg = {e};                            assume; by TSin3A; Axe & F1;  // ! TSin3A := A = {a} == a in A & A[x:A, x = a];
F1 := A[x:elg, x = e];
F2 := x = e;                                 is F1(x);
F3 := false;                                 is Tneq1a(F2 & F01);          // ! Tneq1a := x=y & x~=y -> false;
  end Proof L2;
 end Proof Telge;

// ! Tme3   := A[x,y:elg, x*e*y = x*y];                  ///

! Linv1 := A[f,t,h,g: elg, f = g*h & t*g = g*t -> inv(f)*t*f = inv(h)*t*h];  // removed *inv(t)
 EqProof Linv1;
F0 := f in elg;                              assume;  // not necessary: see F04, F05; WRONG! if absent then ERROR!
// F01 := t in elg;                             assume;
// F02 := h in elg;                             assume;
// F03 := g in elg;                             assume;
F04 := f = g*h;                              assume;   // no merging with f = g*h in cond ???
F05 := t*g = g*t;                            assume;
F1 := inv(f)*t*f;                            by F04;  // ,F04;  // removed f;
F2 := inv(g*h)*t*(g*h);                      by Tinvmlt(g,h);  // ! Tinvmlt := A[x,y:elg, inv(x*y) = inv(y) * inv(x)];
F3 := (inv(h)*inv(g))*t*(g*h);               by Associnve;
F31 := inv(h)*inv(g)*(t*g)*h;                by F05;
F4 := inv(h)*inv(g)*(g*t)*h;                 by Associnve;
// F41 := inv(h)*(inv(g)*g)*t*h;             // by Tlinv(g);  // ! Tlinv := A[a:elg, inv(a) * a = e];
// F5 := inv(h)*e*t*h;                       // by Axre(inv(h));   // ! Tme3   := A[x,y:elg, x*e*y = x*y];
F6 := inv(h)*t*h;
 end EqProof Linv1;
                                                                         // ! Tlinv := inv(a)*a = e;
! Linv2 := A[x,y: elg, (x * inv(y))*y = x];  byeq -AxAssoc, Tlinv, Axre; // AxAssoc:= A[x,y,z: elg, x*(y*z) = (x*y)*z ];

abel := A[x,y: elg, x * y = y * x];

]; // group :: [   // 1                                      // FN is the class of all functions

!! Axgr0 := A[G:group, G = [elg.G, *(group).G]];               // ??? Can be proved ???
// mm := [elg, *];
// Tmm1 := mm in monoid;
// Tmm2 := monoid <: group;

// trivgr := F[a:any, [{a}, {[[a,a], a]}] ];                  // trivial group
// ! Ttrivgr := All(a, trivgr(a) in group);                   // 

group :: [ // 2

// / := F[x,y:elg, x * inv(y)];
// dcldiv := dcl[/, elg,elg,elg];
// !! Axdiv := / @ dcldiv = F[x,y: elg, x*inv(y)];
// ! L0 := inv in fn(elg,elg);

// ! Tdiv1 := A[x,y: elg, x/y = x*inv(y)];
//  EqProof Tdiv1;
// F0 := x in elg;                                           assume;
// F01 := y in elg;                                          assume;
// F1 := x/y;                                                by Axdiv,Red;
// F2 := F[x,y: elg, x*inv(y)](x,y);                     // by Red; ???  was error in trm: stp1:must be ) ,not , q= smpt:case '(' 
// F3 := x*inv(y);
//  end EqProof Tdiv1;

// ! Tdiv2 := A[x,y: elg, x/y = e == x=y];
//  EqProof Tdiv2;
// F0 := x in elg;                                           assume;
// F01 := y in elg;                                          assume;
// F1 := x/y = e;                                            by Tdiv1;
// F2 := x*inv(y) = e;                                       by Tinvm2a;    // ! Tinvm2a := A[x,y:elg, x * inv(y) = e == x = y];
// F3 := x=y;
//  end EqProof Tdiv2;

// ! Tdiv3 := A[x,y: elg, inv(x/y) = y/x];
//  EqProof Tdiv3;
// F0 := x in elg;                                           assume;
// F01 := y in elg;                                          assume;
// F1 := inv(x/y);                                           by Tdiv1;     // ! Tdiv1 := A[x,y: elg, x/y = x*inv(y)];
// F2 := inv(x*inv(y));                                      by Tinvmlt;   // ! Tinvmlt := A[x,y:elg, inv(x*y) = inv(y) * inv(x)];
// F3 := inv(inv(y))*inv(x);                                 by Tinvinv;   // ! Tinvinv := A[x:elg, inv(inv(x)) = x];
// F4 := y * inv(x);                                         by -Tdiv1;
// F5 := y / x;
// end EqProof Tdiv3;

//////////////////////////// 3. Exponentiation (the power function) in group  ////////////////////////////////////
// pw := F[x:elg, n:nat, PS(F[k: 1..n, x])];
dpw := {x,n; x in elg; n in nat};                        // was x_elg_n_nat := {x,n; x in elg; n in nat}; // {x:elg,n:nat}:  error;
// x_elg := {x; x in elg};                               // moved up;
                        
dcl[pw,fn(dpw,elg)];                                     recdef;        // dpw := {x:elg,n:nat}; // B = elg;
!! Axpw0 := A[x_elg, pw(x,0) = e];                       // A[x:elg, pw(x,0) = b(x)];                       
!! Axpw1 := A[dpw, pw(x,n+1) = pw(x,n) * x];
! Lpw0 := e in elg;                                      is Axe;        // A[x_elg, b(x) in elg]; // A[d1, b(X) in B]
// end of recursive definition of pw;
// ! Lpw1 := A[dpw, pw(x,n) in elg -> pw(x,n+1) in elg]; // not necessary, because it follows from dcl[pw,fn(dpw,elg)];
// Proof Lpw1;
//F0 := x in elg;                                          assume;
//F01 := n in nat;                                         assume;
//F02 := pw(x,n) in elg;                                   assume;
//G0 := pw(x,n+1) in elg;                                  by Axpw1;       // !! Axpw1 := A[dpw, pw(x,n+1) = pw(x,n) * x];
//G1 := pw(x,n) * x in elg;
// end Proof Lpw1;

! Tpwin := pw in fn(dpw,elg);                            is typeaxiom;   // dpw := {x:elg,n:nat};
! Tpwt := A[dpw, pw(x,n) in elg];                        is Tfnd(Tpwin); // ! Tfnd := f in fn(d, B) ->  A[d, f(^d) in B];
! Tpw1 :=  A[x:elg, pw(x,1) = x];
 EqProof Tpw1;
F0 := x in elg;                                          assume;
F01 := 0+1 = 1;                                          is Red;                    
F1 := pw(x,1);                                           by -F01;
F2 := pw(x,0+1);                                         by Axpw1;       // !! Axpw1 := A[dpw, pw(x,n+1) = pw(x,n) * x];
F3 := pw(x,0)*x;                                         by Axpw0,Tle;   // ! Tle := e*a = a;
F4 := x;
 end EqProof Tpw1;

! Tpwe := A[n:nat, pw(e,n) = e];
 Proof Tpwe;                                             by Mathind; Basis & Step;
Basis := pw(e,0) = e;                                    is Axpw0;       // !! Axpw0 := A[x_elg, pw(x,0) = e];  
Step := A[n:nat, pw(e,n) = e -> pw(e,n+1) = e];
  EqProof Step;
F0 := n in nat;                                          assume;
F01 := pw(e,n) = e;                                      assume;
F1 := pw(e,n+1);                                         by Axpw1;       // !! Axpw1 := A[dpw, pw(x,n+1) = pw(x,n) * x];
F2 := pw(e,n)*e;                                         by F01;
F3 := e*e;                                               by Teee;        // ! Teee := e*e = e;
F4 := e;
  end EqProof Step;
 end Proof Tpwe;

! Tpwpr := A[n:nat, A[m:nat,x:elg, pw(x,m) * pw(x,n) = pw(x,m+n)]];      // pr: product;
 Proof Tpwpr;                                            by Mathind; Basis & Step; 
Basis := A[m:nat,x:elg, pw(x,m) * pw(x,0) = pw(x,m+0)]; // ! Mathind := A[n:nat, P(n)] == P(0) & A[k:nat, P(k) -> P(k+1)];
  EqProof Basis;
F0 := m in nat;                                          assume;
F01 := x in elg;                                         assume;
F1 := pw(x,m) * pw(x,0);                                 by Axpw0,Axre;  // Axre   := A[x:elg, x * e = x]; 
F2 := pw(x,m);                                           by -Axir0;      // !! Axir0   := A[x:int, x + 0 = x];
F3 := pw(x,m+0);
  end EqProof Basis;
Step := A[k:nat,A[m:nat,x:elg, pw(x,m) * pw(x,k) = pw(x,m+k)] -> (G0 := A[m:nat, x:elg, pw(x,m) * pw(x,k+1) = pw(x,m+(k+1))])];
  Proof Step;
F0 := k in nat;                                          assume;
F01 := A[m:nat, x:elg, pw(x,m) * pw(x,k) = pw(x,m+k)];   assume;
   EqProof G0;                                           // because an error in rnam: rnam found the global m; 8.22.20
F02 := m in nat;                                         assume;
F03 := x in elg;                                         assume;
F1 := pw(x,m) * pw(x,k+1);                               by Axpw1;       // !! Axpw1 := A[dpw, pw(x,n+1) = pw(x,n) * x];
F2 := pw(x,m) * (pw(x,k)*x);                             by AxAssoc;
F3 := (pw(x,m) * pw(x,k))*x;                             by F01;  // 
F4 := pw(x,m+k) * x;                                     by -Axpw1;
F5 := pw(x,(m+k) + 1);                                   by -Axiaddass;  // Axiaddass := A[x,y,z: int, x+(y+z) = (x+y)+z ];
F6 := pw(x,m+(k+1));
   end EqProof G0;
  end Proof Step;
 end Proof Tpwpr;
                                                        // ! TA1_23 := A[x1:A1,x2:A2,x3:A3, Q] = A[x1:A1, A[x2:A2, x3:A3, Q]];        ///
! Tpwpr1 := A[n:nat,m:nat,x:elg, pw(x,m) * pw(x,n) = pw(x,m+n)]; by TA1_23; Tpwpr;  // pr: product; same as Tpwpr

! Tpwprcomm := A[n:nat,m:nat,x:elg, pw(x,m) * pw(x,n) = pw(x,n)*pw(x,m)]; 
 Proof Tpwprcomm;
F0 := n in nat;                                          assume;
F01 := m in nat;                                         assume;
F02 := x in elg;                                         assume;
F1 := pw(x,m) * pw(x,n) = pw(x,m+n);                     is Tpwpr1;
F2 := pw(x,n) * pw(x,m) = pw(x,n+m);                     is Tpwpr1;
F3 := m+n = n+m;                                         is Axiaddcomm;       // !! Axiaddcomm := A[x,y: int, x+y = y+x ];
F4 := pw(x,m+n) = pw(x,n+m);                             byeq F3; 
F5 := pw(x,m) * pw(x,n) = pw(x,n)*pw(x,m);               is Axeq3(F1&F2&F4);  // !! Axeq3 := x=a1 & y=a2 & a1=a2 -> x=y; 
 end Proof Tpwprcomm;

! Tpwpw0 := A[n:nat, A[m:nat,x:elg, pw(pw(x,m), n) = pw(x, m*n)]];            // (x^m)^n = x^(m*n);
 Proof Tpwpw0;                                           by Mathind; Basis & Step; 
Basis := A[m:nat,x:elg, pw(pw(x,m), 0) = pw(x,m*0)];     // ! Mathind := A[n:nat, P(n)] == P(0) & A[k:nat, P(k) -> P(k+1)];
  EqProof Basis;
F0 := m in nat;                                          assume;
F01 := x in elg;                                         assume;
F02 := pw(x,m*0) = e;                                    byeq Tintmlt0, Axpw0; // !! Axpw0 := A[x_elg, pw(x,0) = e]; // ! Tintmlt0 := k*0 = 0;
F1 := pw(pw(x,m), 0);                                    by Axpw0, -F02;       // )); was non caught; 
F2 := pw(x,m*0);
  end EqProof Basis;

Step := A[k:nat,A[m:nat,x:elg,  pw(pw(x,m), k) = pw(x,m*k)] -> (G0 := A[m:nat, x:elg,  pw(pw(x,m), k+1) = pw(x,m*(k+1))])];
  Proof Step;
F0 := k in nat;                                          assume;
F01 := A[m:nat, x:elg, pw(pw(x,m), k) = pw(x,m*k)];      assume;
   EqProof G0;
F02 := m in nat;                                         assume;
F03 := x in elg;                                         assume;
F1 := pw(pw(x,m), k+1);                                  by Axpw1;        // !! Axpw1 := A[dpw, pw(x,n+1) = pw(x,n) * x];
F2 := pw(pw(x,m), k) * pw(x,m);                          by F01;
F3 := pw(x,m*k) * pw(x,m);                               by Tpwpr1;       // ! Tpwpr1 := A[n:nat,m:nat,x:elg, pw(x,m) * pw(x,n) = pw(x,m+n)];
F4 := pw(x,m*k + m);                                     by -Tintdistr1a; // ! ! Tintdistr1a := A[z,x: int, z*(x+1) = z*x + z];
F5 := pw(x,m*(k+1));
   end EqProof G0;
  end Proof Step;
 end Proof Tpwpw0;
                                                        // ! TAA3 := A[x:t,x1:t1,x2:t2, P(x,x1,x2)] == A[x:t, A[x1:t1,x2:t2, P(x,x1,x2)]];
! Tpwpw := A[n:nat, m:nat,x:elg, pw(pw(x,m), n) = pw(x, m*n)];   by TAA3; Tpwpw0;         // (x^m)^n = x^(m*n);
                          
! Tpwinv := A[n:nat, A[x:elg, inv(pw(x,n)) = pw(inv(x), n)]];
 Proof Tpwinv;                                           by Mathind; Basis & Step; 
Basis := A[x:elg, inv(pw(x,0)) = pw(inv(x), 0)];         // ! Mathind := A[n:nat, P(n)] == P(0) & A[k:nat, P(k) -> P(k+1)];
  EqProof Basis;
F0 := x in elg;                                          assume;
F01 := pw(inv(x),0) = e;                                 is Axpw0;  // !! Axpw0 := A[x:elg, pw(x,0) = e];
F1 := inv(pw(x,0));                                      by Axpw0;
F2 := inv(e);                                            by Tinve;  // ! Tinve := inv(e) = e;    
F3 := e;                                                 by -F01;
F4 := pw(inv(x),0);
  end EqProof Basis;
Step := A[k:nat, A[x:elg, inv(pw(x,k)) = pw(inv(x), k)] -> (G0 := A[x:elg, inv(pw(x,k+1)) = pw(inv(x), k+1)])];
  Proof Step;
F0 := k in nat;                                          assume;
F01 := A[x:elg, inv(pw(x,k)) = pw(inv(x), k)];           assume;
   EqProof G0;
F02 := x in elg;                                         assume;
F1 := inv(pw(x,k+1));                                    by Axpw1;   // !! Axpw1 := A[dpw, pw(x,n+1) = pw(x,n) * x];
F2 := inv(pw(x,k)*x);                                    by Tinvmlt; // ! Tinvmlt := A[x,y:elg, inv(x*y) = inv(y) * inv(x)];
F3 := inv(x) * inv(pw(x,k));                             by F01;
F4 := inv(x) * pw(inv(x),k);                             by -Tpw1,2;   // ! Tpw1 :=  A[x:elg, pw(x,1) = x]; 1:F4, 2:inv(x);
F5 := pw(inv(x),1) * pw(inv(x),k);                       by Tpwpr1; 
F6 := pw(inv(x),1+k);                                    by Axiaddcomm;
F7 := pw(inv(x),k+1);
   end EqProof G0;
  end Proof Step;
 end Proof Tpwinv;

! Tpwinv1 := A[n:nat,x:elg, inv(pw(x,n)) = pw(inv(x), n)];  by TAA2; Tpwinv;

(^) := F[x:elg,n:int, if(n >= 0, pw(x,n), inv(pw(x,-n)))];       // was dcl[^,elg,int,elg]; // dpw := {x,n; x in elg; n in nat};

! Texp_type := (^) in fn(elg#int,elg);
 Proof Texp_type;                                       by TFinfn2; // ! TFinfn2 := F[dAB,G(a,b)] in fn(A#B,C)==A[dAB, G(a,b) in C]; 
F1 := A[x:elg,n:int, G0 := if(n >= 0, pw(x,n), inv(pw(x,-n))) in elg]; 
  Proof F1;
H0 := x in elg;                                         assume;
H01 := n in int;                                        assume;  // ! Tifin2a := a in X & b in X -> if(p,a,b) in X;
G0;                                                     by Tifin2; L1 & L2; // Tifin2 := if(p,a,b) in X == (p -> a in X) & (~p -> b in X); /// is Tif4;
L1 := n >= 0 -> pw(x,n) in elg;                         // by Tpwt; is Taut; // ! Tpwt := A[dpw, pw(x,n) in elg];
  Proof L1;
K0 := n >= 0;                                           assume; by -Tnat0;  // ! Tnat0 := k in nat == k >= 0; 
K01 := n in nat;                                        // dpw := {x,n; x in elg; n in nat}
G1 := pw(x,n) in elg;                                   is Tpwt;    // ! Tpwt := A[dpw, pw(x,n) in elg];
   end Proof L1;
L2 := ~(n >= 0) -> inv(pw(x,-n)) in elg;
  Proof L2;
K0 := ~(n >= 0);                                        assume;  by -Tlt1; // ! Tlt1 := k < m == ~(k >= m);
K01 := n < 0;
K02 := -n in nat;                                       is Tnat5(K01);     // ! Tnat5 := k<0 -> -k in nat;
K1 := pw(x,-n) in elg;                                  is Tpwt;
K2 := inv(pw(x,-n)) in elg;                             is LCL1;           // ! LCL1  := A[x:elg, inv(x) in elg];
   end Proof L2;
  end Proof F1;
 end Proof Texp_type;

! Axexp := A[x:elg, n:int, x^n = if(n >= 0, pw(x,n), inv(pw(x,-n)))];  byeq Red;

! Texppw := A[x:elg, n:nat, x^n = pw(x,n)];
 EqProof Texppw;
F0 := x in elg;                                          assume;
F01 := n in nat;                                         assume; by Tnat0;    // ! Tnat0 := k in nat == k >= 0;
F02 := n >= 0;                                           // by Axexp1: rnam caught the error, but with a strange message; // comment for next line;
F1 := x^n;                                               by Axexp;       // did not work:F1;  by Axexp,Red; F3;            
F2 := if(n >= 0, pw(x,n), inv(pw(x,-n)));                by Tif1(F02);   // by Red;        // Tif1(F02);        // ! Tif1 := p -> if(p,a,b) = a;
F3 := pw(x,n);
 end EqProof Texppw;

! Texppw1 := A[x:elg, n:int, n < 0 -> x^n = inv(pw(x,-n))];                    // was Texp3
 EqProof Texppw1;
F0 := x in elg;                                          assume;
F01 := n in int;                                         assume;
F02 := n < 0;                                            assume;              by Tlt1;    // ! Tlt1 := k < m == ~(k >= m);
F03 := ~(n >= 0);
F1 := x^n;                                               by Axexp;
F2 := if(n >= 0, pw(x,n), inv(pw(x,-n)));                by Tif2(F03);        // ! Tif2 := ~p -> if(p,a,b) = b; 
F3 := inv(pw(x,-n));
 end EqProof Texppw1;
                                                         // ! Texp_type := (^) in fn(elg#int,elg);
! Texp0 := A[x:elg, x^0 = e];
 EqProof Texp0;
F0 := x in elg;                                          assume;
F1 := x^0;                                               by Texppw;              // ! Texppw := A[x:elg, n:nat, x^n = pw(x,n)];
F2 := pw(x,0);                                           by Axpw0;           // !! Axpw0 := A[x:elg, pw(x,0) = e];
F3 := e;
 end EqProof Texp0;

! Texppw1a := A[x:elg, n:int, n <= 0 -> x^n = inv(pw(x,-n))];
 Proof Texppw1a;
F0 := x in elg;                                          assume;
F01 := n in int;                                         assume;
F02 := n <= 0;                                           assume; by Tlint;     // ! Tlint := A[a,b:int, a <= b == a < b or a = b];
F03 := n < 0 or n = 0;
G0 := x^n = inv(pw(x,-n));                               by Case2(F03); L1 & L2;
L1 := n < 0 -> G0;                                       is Texppw1; 
L2 := n = 0 -> G0;                                       // G0 := x^n = inv(pw(x,-n)); 
  EqProof L2; 
H0 := n = 0;                                             assume;
H01 := inv(pw(x,-n)) = e;                                byeq H0,Tintmn0,Axpw0,Tinve; // ! Tintmn0 := -0 = 0; // ! Tinve := inv(e) = e; 
H1 := x^n;                                               by H0, Texp0, -H01;
H2 := inv(pw(x,-n));                                            
  end EqProof L2;
 end Proof Texppw1a;

! Texppw1b := A[x:elg, n:int, n < 0 -> x^n = pw(inv(x),-n)];
 EqProof Texppw1b;
F0 := x in elg;                                          assume;
F01 := n in int;                                         assume;
F02 := n < 0;                                            assume;
F03 := -n in nat;                                        is Tnat5(F02);
F1 := x^n;                                               by Texppw1;            // ! Texppw1 := A[x:elg, n:int, n < 0 -> x^n = inv(pw(x,-n))];
F2 := inv(pw(x,-n));                                     by Tpwinv1;            // ! Tpwinv1 := A[n:nat,x:elg, inv(pw(x,n)) = pw(inv(x), n)];
F3 := pw(inv(x),-n);
 end EqProof Texppw1b;

! Texpt := A[x:elg, k:int, x^k in elg];                  is Tfndp(Texp_type); by TAA2;
! Texpt0 := A[x:elg, A[k:int, x^k in elg]];              // ! TAA2 := A[x:t,x1:t1, P(x,x1)] == A[x:t, A[x1:t1, P(x,x1)]];
! Texpt1 := A[x:elg, R[k:int, x^k] <: elg];              by TRA; Texpt0;   // ! TRA  := R[d, f] <: B == A[d, f in B];   

! Texpe0 := A[n:nat, e^n = e];  
 EqProof Texpe0;
F0 := n in nat;                                          assume;
F1 := e^n;                                               by Texppw;         // ! Texppw := A[x:elg, n:nat, x^n = pw(x,n)];
F2 := pw(e,n);                                           by Tpwe;
F3 := e;
 end EqProof Texpe0;

! Texpe := A[k:int, e^k = e];
 Proof Texpe;
F0 := k in int;                                          assume;
F01 := k >= 0 or k < 0;                                  is Tint1;         // ! Tint1 := A[k:int, k >= 0 or k < 0];
G0 := e^k = e;                                           by Case2(F01); L1 & L2;
L1 := k>=0 -> e^k = e;
  EqProof L1;
H0 := k>=0;                                              assume;  by -Tnat0;   // ! Tnat0 := k in nat == k >= 0;
H01 := k in nat;
H1 := e^k;                                               by Texppw;
H2 := pw(e,k);                                           by Tpwe;            // ! Tpwe := A[n:nat, pw(e,n) = e];
H3 := e;
  end EqProof L1;
L2 := k<0 -> e^k = e;   
  EqProof L2;
H0 := k < 0;                                             assume; 
H01 := -k in nat;                                        is Tnat5(H0);       // ! Tnat5 := k<0 -> -k in nat;
H02 := e^k = inv(pw(e,-k));                              is Texppw1(e,k)(H0); // Texppw1 := A[x:elg, n:int, n<0 -> x^n = inv(pw(x,-n))];
H1 := e^k;                                               by H02;
H2 := inv(pw(e,-k));                                     by Tpwe;            // ! Tpwe := A[n:nat, pw(e,n) = e];
H3 := inv(e);                                            by Tinve;
H4 := e;
  end EqProof L2;
 end Proof Texpe;

! Texp0a := A[a:elg, k: int, k=0 -> a^k = e];             
 EqProof Texp0a;
F0 := a in elg;                                          assume;
F01 := k in int;                                         assume;
F02 := k=0;                                              assume;
F1 := a^k;                                               by F02;
F2 := a^0;                                               by Texp0;
F3 := e;
 end EqProof Texp0a;

! Texp0b := A[a:elg, k: int, a^k ~= e -> k ~= 0 ];      //  by Contraposition;
 Proof Texp0b;
F0 := a in elg;                                          assume;
F01 := k in int;                                         assume;
F1 := a^k ~= e -> k ~= 0;                                by CP;  // ! CP := p->q == ~q -> ~p; // Contraposition;
F2 := ~(k ~= 0) -> ~(a^k ~= e);                          by TNneq;  // !  TNneq := ~(u ~= v) == u = v;
F3 := k=0 -> a^k = e;                                    is Texp0a;
 end Proof Texp0b;

! Texp1 := A[a:elg, a^1 = a];
 EqProof Texp1;
F0 := a in elg;                                         assume;
F1 := a^1;                                              by Texppw; // ! Texppw := A[x:elg, n:nat, x^n = pw(x,n)];
F2 := pw(a,1);                                          by Tpw1;  // ! Tpw1 :=  A[x:elg, pw(x,1) = x];
F3 := a;
 end EqProof Texp1;

// ! Texp1a := A[x:elg,k:int, k >= 0 ->  x^k = pw(x,k)];  // k in nat & //   see Texppw; ??? not needed ???
// EqProof Texp1a;
//F0 := x in elg;                                         assume;
//F01 := k in int;                                        assume;
//F02 := k >= 0;                                          assume; by -Tnat0;  // ! Tnat0 := k in nat == k >= 0;
//F03 := k in nat;
//F1 := x^k;                                              by Texppw;
//F2 := pw(x,k);
// end EqProof Texp1a;


! Tinvexp := A[x:elg, k:int, G0 := inv(x^k) = x^(-k)];
 Proof Tinvexp;
F0 := x in elg;                                         assume;
F01 := k in int;                                        assume;
F02 := k in nat or k <= 0;                              is Tint2;            // ! Tint2 := A[k:int, k in nat or k < = 0];
G0;                                                     by Case2(F02); L1 & L2;
L1 := k in nat -> G0;
  Proof L1;
H0 := k in nat;                                         assume; by Tnat0a;   // ! Tnat0a := k in nat == -k <= 0; 
H1 := -k <= 0;                                          // ! Texppw1a := A[x:elg, n:int, n <= 0 -> x^n = inv(pw(x,-n))];
H2 := x^(-k) =  inv(pw(x,-(-k)));                       is Texppw1a(x,-k)(H1); by Tintmnmn; // ! Tintmnmn := -(-k) = k; 
H3 := x^(-k) =  inv(pw(x,k));                           by -Texppw;           // ! Texppw := A[x:elg, n:nat, x^n = pw(x,n)];
H4 := x^(-k) =  inv(x^k);                               by Axsym;            // Axsym := u=v == v=u;
H5 := inv(x^k) = x^(-k);
  end Proof L1;

L2 := k <= 0 -> G0;
  EqProof L2;
H0 := k <= 0;                                    assume; by -Tnat1;   // ! Tnat1 := -k in nat == k <= 0;
H01 := -k in nat;                                // ??? did not find automatically ???
H1 := inv(x^k);                                  by Texppw1a(x,k)(H0); // ! Texppw1a := A[x:elg, n:int, n <= 0 -> x^n = inv(pw(x,-n))];
H2 := inv(inv(pw(x,-k)));                        by Tinvinv;
H3 := pw(x,-k);                                  by -Texppw;           // ! Texppw := A[x:elg, n:nat, x^n = pw(x,n)];
H4 := x^(-k);
  end EqProof L2;
 end Proof Tinvexp;

! Tinvexp1 := A[x:elg, k:int, inv(x)^k = x^(-k)];
 Proof Tinvexp1;
F0 := x in elg;                                  assume;
F01 := k in int;                                 assume;
F02 := k in nat or k<0;                          is Tnatorlt0;          // !! Tnatorlt0 := k in nat or k < 0;          
G0 := inv(x)^k = x^(-k);                         by Case2(F02); L1 & L2;
L1 := k in nat -> G0;
  EqProof -L1;
H0 := k in nat;                                  assume; by Tnat0a;     // ! Tnat0a := k in nat == -k <= 0;
H01 := -k <= 0;                                                         // ! Tpwinv1 := A[n:nat,x:elg, inv(pw(x,n)) = pw(inv(x), n)]
H1 := x^(-k);                                    by Texppw1a; // (x,-k)(H01); // Texppw1a := A[x:elg, n:int, n <= 0 -> x^n = inv(pw(x,-n))];
H2 := inv(pw(x,-(-k)));                          by Tintmnmn, Tpwinv1;  // ! Tintmnmn := -(-k) = k;;                       
H3 := pw(inv(x), k);                             by -Texppw;            // ! Texppw := A[x:elg, n:nat, x^n = pw(x,n)];
H4 := inv(x)^k
  end EqProof -L1;
L2 := k<0 -> G0;
  EqProof L2;
H0 := k<0;                                      assume;
H01 := -k in nat;                               is Tnat5(H0);           // ! Tnat5 := k<0 -> -k in nat;
H1 := inv(x)^k;                                 by Texppw1b;            // ! Texppw1b := A[x:elg, n:int, n < 0 -> x^n = pw(inv(x),-n)];
H2 := pw(inv(inv(x)), -k);                      by Tinvinv;
H3 := pw(x,-k);                                 by -Texppw;             // ! Texppw := A[x:elg, n:nat, x^n = pw(x,n)];
H4 := x ^ (-k);
  end EqProof L2;
 end Proof Tinvexp1;

! Tinvexp2 := A[a:elg, k: int, inv(a^k) = inv(a)^k];
 Proof Tinvexp2;
F0 := a in elg;                                 assume;
F01 := k in int;                                assume;
F1 := inv(a^k) = a^(-k);                        is Tinvexp;
F2 := inv(a)^k = a^(-k);                        is Tinvexp1;            // ! Tinvexp1 := A[x:elg, k:int, inv(x)^k = x^(-k)];
F3 := inv(a^k) = inv(a)^k;                      is Axeq2(F1 & F2);      // !! Axeq2 := x=a & y=a -> x=y;
 end Proof Tinvexp2;

! Lexpmlt1 := A[x:elg, k:int, x^k = x^(k-1)*x];
 Proof Lexpmlt1;
F0 := x in elg;                                 assume;
F01 := k in int;                                assume;
F1 := k in nat1 or k<=0;                        is Tint1b;              // ! Tint1b := A[k:int, k in nat1 or k <= 0];
G0 := x^k = x^(k-1)*x;                          by Case2(F1); L1 & L2;
L1 := k in nat1 -> G0;
  EqProof L1;
H0 := k in nat1;                                assume;                // Tnat1nat := nat1 <: nat;
//      k in nat;                                 is TinIn(H & Tnat1nat);  // wlot should add it automatically
H01 := k-1 in nat;                              is Tnat6(H0);           // ! Tnat6 := k in nat1 -> k-1 in nat;
H02 := (k-1)+1 in nat;                          is Tnatadd;             // ! Tnatadd := A[k,m:nat, k+m in nat];      
H03 := k = (k-1)+1;                             is -Tint4;              // ! Tint4 := (k-m) + m = k;
H1 := x^k;                                      by Texppw;              // ! Texppw := A[x:elg, n:nat, x^n = pw(x,n)];
H2 := pw(x,k);                                  by H03;
H3 := pw(x,(k-1)+1);                            by Axpw1;               // !! Axpw1 := A[dpw, pw(x,n+1) = pw(x,n) * x];
H4 := pw(x,k-1)*x;                              by -Texppw;             // ! Texppw := A[x:elg, n:nat, x^n = pw(x,n)];
H5 := x^(k-1)*x;
  end EqProof L1;                        
L2 := k <= 0 -> G0;                             // G0 := x^k = x^(k-1)*x;
  Proof L2;                                                           // ! Texppw1b := A[x:elg, n:int, n<0 -> x^n = pw(inv(x),-n)];
H0 := k <= 0;                                   assume;  by -Tnat1;     // ! Tnat1 := -k in nat == k <= 0;
H01 := -k in nat;                                                       // !Texppw1a := A[x:elg, n:int, n<=0 -> x^n = inv(pw(x,-n))];
H02 := -k + 1 in nat;                           is Tnatadd;             // ! Tnatadd := A[k,m:nat, k+m in nat];
H03 := k-1 < 0;                                 by Tintltle1;  H0;      // ! Tintltle1 := k-1 < m == k<=m; ??? by Tintltle; accepted
H04 := x^k = pw(inv(x),-k);                     byeq Texppw1a,Tpwinv1;  // ! Tpwinv1 := A[n:nat,x:elg, inv(pw(x,n)) = pw(inv(x), n)]        
H05 := x^(k-1) = pw(inv(x),-k + 1);             byeq Texppw1b, Tint3;   // ! Tint3 := -(k-1) = -k + 1;// -(k-1) = -k + 1;
G0;                                             by Teqml1;              // ! Teqml1 := A[a,x,b: elg, b = x*a == x = b * inv(a)];
G1 := x^(k-1) = x^k * inv(x);                   by H05,H04;
H2 := pw(inv(x),-k + 1) = pw(inv(x),-k)*inv(x); is Axpw1;               // !! Axpw1 := A[dpw, pw(x,n+1) = pw(x,n) * x]; 
  end Proof L2;
 end Proof Lexpmlt1;

! Lexpmlt2 := A[x:elg, k:int, x^(k-1) = x^(k) * inv(x)];
 Proof Lexpmlt2;
F0 := x in elg;                                 assume;
F01 := k in int;                                assume;
F1 := x^k = x^(k-1) * x;                        is Lexpmlt1; by Teqml1;  // ! Teqml1 := A[a,x,b: elg, b = x*a == x = b * inv(a)];
F2 := x^(k-1) = x^k * inv(x);
 end Proof Lexpmlt2;
                                                // ! Tinj0 := A[f:FN, injective(f) ->  A[x1,x2: dom(inv), x1 = x2 == f(x1) = f(x2)]];
! Lexpmlt3 := A[x:elg, k:int, x^k = x * x^(k-1)];
 Proof Lexpmlt3;
F0 := x in elg;                                    assume;
F01 := k in int;                                   assume;               // ! Tinvinj := A[x,y: elg), inv(x) = inv(y) == x = y];
G0 := x^k = x * x^(k-1);                           by -Tinvinj, Tinvmlt; // ! Tinvmlt := A[x,y:elg, inv(x*y) = inv(y) * inv(x)];
G1 := inv(x^k) = inv(x^(k-1)) * inv(x);            by Tinvexp2;          // ! Tinvexp2 := A[a:elg, k: int, inv(a^k) = inv(a)^k];
G2 := inv(x)^k = inv(x)^(k-1) * inv(x);            is  Lexpmlt1;         // ! Lexpmlt1 := A[x:elg, k:int, x^k = x^(k-1)*x];
 end Proof Lexpmlt3;

! Lexpmlt4 := A[x:elg, k:int, x^(k-1) = inv(x) * x^(k)];
 Proof Lexpmlt4;
F0 := x in elg;                                 assume;
F01 := k in int;                                assume;
F1 := x^k = x * x^(k-1);                        is Lexpmlt3; by Teqmr1; // ! Teqmr1 := A[a,x,b: elg, b = a*x == x = inv(a)*b];
F2 := x^(k-1) = inv(x) * x^k;
 end Proof Lexpmlt4;

! Lexpmlt := A[k:nat, A[m:int,x:elg, x^(-k)*x^m = x^(-k + m)]];
 Proof Lexpmlt;                                    by Mathind; Basis & Step;
Basis := A[m:int,x:elg, x^(-0)*x^m = x^(-0 + m)];
  EqProof Basis;
F0 := m in int;                                    assume;
F01 := x in elg;                                   assume;
F02 := -0 + m = m;                                 is Red;
F03 := x^(-0 + m) = x^m;                           byeq F02;
F1 := x^(-0)*x^m;                                  by  Tintmn0;         //! Tintmn0 := -0 = 0;
F2 := x^0 * x^m;                                   by Texp0,Tle;        // ! Texp0 := A[x:elg, x^0 = e]; // ! Tle := e*a = a;
F3 := x^m;                                         by -F03;
F4 := x^(-0 + m);
  end EqProof Basis;

Step := A[k:nat, A[m:int,x:elg, x^(-k) * x^m = x^(-k + m)] -> (G0 := A[m:int,x:elg, x^(-(k+1)) * x^m = x^(-(k+1) + m)]) ];
  Proof Step;
F0 := k in nat;                                    assume;
F01 := A[m:int,x:elg, x^(-k) * x^m = x^(-k + m)];  assume;
   EqProof G0;
H0 := m in int;                                    assume;
H01 := x in elg;                                   assume; 
H1 := x^(-(k+1)) * x^m;                            by Tint6;            // ! Tint6 := -(k + m) = -k - m;
H2 := x^(-k - 1) * x^m;                            by Lexpmlt4;         // ! Lexpmlt4 := A[x:elg, k:int, x^(k-1) = inv(x) * x^(k)];
H3 := (inv(x) * x^(-k)) * x^m;                     by Associnve;
H4 := inv(x) * (x^(-k) * x^m);                     by F01;
H6 := inv(x) * x^(-k + m);                         by -Lexpmlt4;
H7 := x^(-k + m -1);                               by Tint5;            // ! Tint5 := -k + m -k1 = -(k+k1) + m;
H8 := x^(-(k+1) + m);
   end EqProof G0;
  end Proof Step;
 end Proof Lexpmlt;
                                                  // ! TAA3 := A[x:t,x1:t1,x2:t2, P(x,x1,x2)] == A[x:t, A[x1:t1,x2:t2, P(x,x1,x2)]];
! Lexpmlt0 := A[k:nat, m:int,x:elg, x^(-k)*x^m = x^(-k + m)]; by TAA3; Lexpmlt;

! Texpmlt := A[x:elg,k,m:int, x^k * x^m = x^(k+m)];
 Proof Texpmlt;
F0 := x in elg;                                    assume;
F01 := k in int;                                   assume;
F02 := m in int;                                   assume;
F1 := k>=0 & m>=0 or ~(k>=0) & m>=0 or k>=0 & ~(m>=0) or ~(k>=0) & ~(m>=0); is Taut(p&q or (~p)&q or p&(~q) or (~p)&(~q));
G0 := x^k * x^m = x^(k+m);                         by Case4(F1); L1 & L2 & L3 & L4;

L1 := k>=0 & m>=0 -> G0;
  EqProof L1;
F0 := k>=0;                                        assume; by -Tnat0;   // ! Tnat0 := k in nat == k >= 0;   
F01 := k in nat; 
F02 := m>=0;                                       assume; by -Tnat0;
F03 := m in nat;
F04 := k+m in nat;                                 is Tnatadd;          // ! Tnatadd := A[k,m:nat, k+m in nat];
F1 := x^k * x^m;                                   by Texppw;           // ! Texppw := A[x:elg, n:nat, x^n = pw(x,n)];
F2 := pw(x,k) * pw(x,m);                           by Tpwpr1;           // ! Tpwpr1 := A[n:nat,m:nat,x:elg, pw(x,m) * pw(x,n) = pw(x,m+n)];
F3 := pw(x,k+m);                                   by -Texppw;
F4 := x^(k+m);
  end EqProof L1;

L2 := ~(k>=0) & m>=0 -> G0;
  EqProof L2;
F0 := ~(k>=0);                                     assume; by -Tlt1;    // ! Tlt1 := k < m == ~(k >= m);
F01 := k < 0;
F02 := -k in nat;                                  is Tnat5(F01);       // ! Tnat5 := k<0 -> -k in nat;    
F03 := m>=0;                                       assume;
F04 := -(-k) = k;                                  is Tintmnmn;         // ! Tintmnmn := -(-k) = k;
F1 := x^k * x^m;                                   by -F04;
F2 := x^(-(-k)) * x^m;                             by Lexpmlt0;   // ! Lexpmlt0 := A[k:nat, m:int,x:elg, x^(-k)*x^m = x^(-k + m)];
F3 := x^(-(-k) + m);                               by Tintmnmn;
F4 := x^(k + m);
  end EqProof L2;

L3 := k>=0 & ~(m>=0) -> G0;
  Proof L3;
F0 := k>=0;                                        assume;  by -Tnat0;   // ! Tnat0 := k in nat == k >= 0;
F01 := k in nat; 
F02 :=  ~(m>=0);                                   assume; by -Tlt1;     // ! Tlt1 := k < m == ~(k >= m);
F03 := m < 0;                                         
F04 := -m in nat;                                  is Tnat5(F03);        // ! Tnat5 := k<0 -> -k in nat; 
// F05 := A[x1,x2: dom(inv), x1 = x2 == inv(x1) = inv(x2)]; is Tinj0(inv)(Tinvinj);  // ! Tinvinj := injective(inv); 
F06 := -(-m) = m;                                  is Tintmnmn;          // ! Tintmnmn := -(-k) = k;
G0;                                                by -Tinvinj;          // by F05;
F1 := inv(x^k * x^m) = inv(x^(k+m));               by Tinvmlt;           // ! Tinvmlt := A[x,y:elg, inv(x*y) = inv(y) * inv(x)];
F2 := inv(x^m) * inv(x^k) = inv(x^(k+m));          by Tinvexp2;          // ! Tinvexp2 := A[a:elg, k: int, inv(a^k) = inv(a)^k];
F3 := inv(x)^m * inv(x)^k = inv(x)^(k+m);         // by -F06;
   EqProof F3;
H1 := inv(x)^m * inv(x)^k;                         by -F06;                         // F4 := inv(x)^(-(-m)) * inv(x)^k) = inv(x)^(k+m);
H2 := inv(x)^(-(-m)) * inv(x)^k;                   by Lexpmlt0;
H3 := inv(x)^(-(-m) + k);                          by Tintmnmn,Axiaddcomm; // Axiaddcomm := A[x,y: int, x+y = y+x ]; ! Tintmnmn := -(-k) = k;
H4 := inv(x)^(k+m); 
   end EqProof F3;
  end Proof L3;

L4 := ~(k>=0) & ~(m>=0) -> G0;
  EqProof L4;
F0 := ~(k>=0);                                     assume; by -Tlt1;     // ! Tlt1 := k < m == ~(k >= m);
F01 := k < 0; 
F02 := -k in nat;                                  is Tnat5(F01);        // ! Tnat5 := k<0 -> -k in nat;
F03 :=  ~(m>=0);                                   assume; by -Tlt1;     // ! Tlt1 := k < m == ~(k >= m);
F04 := m < 0;                                       
F05 := -m in nat;                                  is Tnat5(F04);        // ! Tnat5 := k<0 -> -k in nat; 
f06 := -k + -m in nat;                             is Tnatadd;           // ! Tnatadd := A[k,m:nat, k+m in nat];                              
F1 := x^k * x^m;                                   by Texppw1b;          // ! Texppw1b := A[x:elg, n:int, n < 0 -> x^n = pw(inv(x),-n)];    
F2 := pw(inv(x),-k) * pw(inv(x),-m);               by Tpwpr1;            // ! Tpwpr1 := A[n:nat,m:nat,x:elg, pw(x,m) * pw(x,n) = pw(x,m+n)];
F3 := pw(inv(x), -k + -m);                         by -Texppw;           // ! Texppw := A[x:elg, n:nat, x^n = pw(x,n)]
F4 := inv(x) ^ (-k + -m);                          by Tint7;             // ! Tint7 := -k + -m = -(k + m);
F5 := inv(x) ^ -(k + m);                           by Tinvexp1;          // ! Tinvexp1 := A[x:elg, k:int, inv(x)^k = x^(-k)];
F6:= x ^ (-(-(k + m)));                            by Tintmnmn;          // ! Tintmnmn := -(-k) = k;                  
F7 := x ^ (k + m);
  end EqProof L4;
 end Proof Texpmlt;

! Texpexp := A[x:elg,k:int,m:int, (x^k)^m = x^(k*m)];
 Proof Texpexp;
F0 := x in elg;                                    assume;
F01 := k in int;                                   assume;
F02 := m in int;                                   assume;                              
F1 := k>=0 & m>=0 or ~(k>=0) & m>=0 or k>=0 & ~(m>=0) or ~(k>=0) & ~(m>=0); is Taut(p&q or (~p)&q or p&(~q) or (~p)&(~q));
G0 := (x^k)^m = x^(k*m);                           by Case4(F1); L1 & L2 & L3 & L4;
L1 := k>=0 & m>=0 -> G0;
  EqProof L1;
H0 := k>=0;                                        assume; by -Tnat0;  // ! Tnat0 := k in nat == k >= 0;
H01 := k in nat;
H02 := m>=0;                                       assume; by -Tnat0; 
H03 := m in nat;
H04 := k*m in nat;                                 is Tnatmlt;         // ! Tnatmlt := A[k,m:nat, k*m in nat];
H1 := (x^k)^m;                                     by Texppw;          // ! Texppw := A[x:elg, n:nat, x^n = pw(x,n)];
H2 := pw(x^k,m);                                   by Texppw; 
H3 := pw(pw(x,k),m);                               by Tpwpw;           // ! Tpwpw := A[n:nat,m:nat,x:elg, pw(pw(x,m),n) = pw(x, m*n)]; 
H4 := pw(x,k*m);                                   by -Texppw;
H5 := x^(k*m);
  end EqProof L1;

L2 := ~(k>=0) & m>=0 -> G0;                       
  EqProof L2;
H0 := ~(k>=0);                                     assume; by -Tlt1;  // ! Tlt1 := k < m == ~(k >= m);
H01 := k < 0;
H02 := m>=0;                                       assume; by -Tnat0; // ! Tnat0 := k in nat == k >= 0;
H03 := m in nat;
H04 := -k in nat;                                  is Tnat5(H01);     // ! Tnat5 := k<0 -> -k in nat;
H05 := -(k*m) in nat;                              is Tintmlt3(H01 &  H03); // ! Tintmlt3 := k<0 & m in nat -> -(k*m) in nat;  
H06 := (-k)*m in nat;                              is Tintmlt3b(H01 & H03); // ! Tintmlt3b := k<0 & m in nat -> (-k)*m in nat;
H1 := (x^k)^m;                                     by Texppw;         // ! Texppw := A[x:elg, n:nat, x^n = pw(x,n)];
H2 := pw(x^k,m);                                   by Texppw1b;       // Texppw1b := A[x:elg, n:int, n<0 -> x^n = pw(inv(x),-n))];
H3 := pw(pw(inv(x),-k),m);                         by Tpwpw;          // ! Tpwpw := A[n:nat,m:nat,x:elg, pw(pw(x,m), n) = pw(x, m*n)]; 
H4 := pw(inv(x),(-k)*m);                           by Tintmlt2;       // ! Tintmlt2 := (-k)*m = -(k*m);
H5 := pw(inv(x),-(k*m));                           by -Texppw;
H6 := inv(x)^(-(k*m));                             by Tinvexp1;       // ! Tinvexp1 := A[x:elg, k:int, inv(x)^k = x^(-k)];
H7 := x^(-(-(k*m)));                               by Tintmnmn;       // ! Tintmnmn := -(-k) = k;
H8 := x^(k*m);
  end EqProof L2;

L3 := k>=0 & ~(m>=0) -> G0;                            // by Texppw1;         // Texppw1 := A[x:elg, n:int, n<0 -> x^n = inv(pw(x,-n))];
  EqProof L3;
H0 := k>=0;                                        assume; by -Tnat0; // ! Tnat0 := k in nat == k >= 0;
H01 := k in nat;
H02 := ~(m>=0);                                    assume; by -Tlt1;  // ! Tlt1 := k < m == ~(k >= m);
H03 := m < 0;
H04 := -m in nat;                                  is Tnat5(H03);     // ! Tnat5 := k<0 -> -k in nat;
H05 := -(k*m) in nat;                              is Tintmlt3a(H01 &  H03);   // ! Tintmlt3a := k in nat & m < 0 -> -(k*m) in nat;  
H06 := k*(-m) in nat;                              is Tintmlt3a1(H01 &  H03);  // ! Tintmlt3a1 := k in nat & m < 0 -> k*(-m) in nat;                 
H1 := (x^k)^m;                                     by Texppw1;        // Texppw1 := A[x:elg, n:int, n<0 -> x^n = inv(pw(x,-n))];
H2 := inv(pw(x^k,-m));                             by Texppw;         // ! Texppw := A[x:elg, n:nat, x^n = pw(x,n)];
H3 := inv(pw(pw(x,k),-m));                         by Tpwpw;          // ! Tpwpw := A[n:nat,m:nat,x:elg, pw(pw(x,m),n) = pw(x, m*n)];
H4 := inv(pw(x, k*(-m)));                          by Tintmlt5a;      // ! Tintmlt5a := k*(-m) = -(k*m);
H5 := inv(pw(x, -(k*m)));                          by -Texppw;
H6 := inv(x^(-(k*m)));                             by Tinvexp;        // ! Tinvexp := A[x:elg, k:int, G0 := inv(x^k) = x^(-k)];
H7 := x^(-(-(k*m)));                               by Tintmnmn;       // ! Tintmnmn := -(-k) = k;
H8 := x^(k*m);
  end EqProof L3;

L4 := ~(k>=0) & ~(m>=0) -> G0;
  EqProof L4;
H0 := ~(k>=0);                                     assume; by -Tlt1;   // ! Tlt1 := k < m == ~(k >= m);
H01 := k < 0;
H02 := ~(m>=0);                                    assume; by -Tlt1;  
H03 := m < 0;
H04 := -m in nat;                                  is Tnat5(H03);          // ! Tnat5 := k<0 -> -k in nat;
H05 := (k*m) in nat;                               is Tintmlt4(H01 & H03); // ! Tintmlt4 := k < 0 & m < 0 -> k*m in nat;                       
H06 := -k in nat;                                  is Tnat5(H01);
H07 := (-k)*(-m) in nat;                           is Tnatmlt;             // ! Tnatmlt := A[k,m:nat, k*m in nat];
H1 := (x^k)^m;                                     by Texppw1,Tpwinv1;     // ! Tpwinv1 := A[n:nat,x:elg, inv(pw(x,n)) = pw(inv(x), n)];
H2 := pw(inv(x^k),-m);                             by Texppw1;             // Texppw1 := A[x:elg, n:int, n<0 -> x^n = inv(pw(x,-n))];     
H3 := pw(inv(inv(pw(x,-k))),-m);                   by Tinvinv;
H4 := pw(pw(x,-k),-m);                             by Tpwpw;
H5 := pw(x, (-k)*(-m));                            by Tintmlt5;            // ! Tintmlt5 := (-k)*(-m) = k*m;
H6 := pw(x, k*m);                                  by -Texppw;             // ! Texppw := A[x:elg, n:nat, x^n = pw(x,n)];
H7 := x^(k*m);
  end EqProof L4;
 end Proof Texpexp;

! Texp1m := A[x:elg, x^(-1) = inv(x)];
 EqProof Texp1m;
F0 := x in elg;                                    assume;
F1 :=  x^(-1);                                     by -Tinvexp; // ! Tinvexp := A[x:elg, k:int, G0 := inv(x^k) = x^(-k)];
F2 := inv(x^1);                                    by Texp1;
F3 := inv(x);
 end EqProof Texp1m;

! Texp2 := A[x:elg, x^2 = x*x]; 
 EqProof -Texp2;
F0 := x in elg;                                   assume;
F01 := 1+1 = 2;                                   is Red;
F1 := x*x;                                        by -Texp1;               // ! Texp1 := A[a:elg, a^1 = a];
F2 := x^1 * x^1;                                  by Texpmlt;
F3 := x^(1+1);                                    by F01;
F4 := x^2;
 end EqProof -Texp2;

// ! Texp2a := A[x:elg,k:int, k < 0 -> (-k in nat) & x^k = inv(pw(x,-k))]; // not used;
// ! Texpmk := A[a: elg, k: int, a^(-k) = inv(a^k)];    // see ! Tinvexp := A[x:elg, k:int, G0 := inv(x^k) = x^(-k)];
// ! Texpmkc := A[a: elg, k: int, a^k = inv(a^(-k))];   //  a^(k): was error("*(mltSS)"); replaced with a^k; //  -byeq Tpwr1m, Tpwr8;
// ! Texp5 := A[a:elg, p,q:int,  (a^p = a^q) & (p~=q) -> E[k:nat1, a^k = e]];  // not used so far;
// ! Texp6 := A[a:elg, k,m,r:int, a^m = e -> a^(k*m + r) = a^r];               // not used so far;
// ! Texp7 := A[a:elg, k,m: int, a^abs(k-m) = e == a^k = a^m];                 // not used so far;
// ! Texp8 := A[a:elg, k,m: int, (a^k)^m = a^(k*m)];    // see Texpexp;
// ! Texp9 := A[a:elg, k:int, a^k = a * (a^(k-1))];        // easy: use Texpmlt;
// ! Texp9a := A[a:elg, k:int, a^k = a^(k-1) * a];         // easy: use Texpmlt;
// ! Tpwrsubgr := A[H: subgr, a:H, k:int, a^k in H];    // from Tpwrt
// ! Lexpcomm1 := A[k:int, a:elg, b:elg, a*b = b*a -> a^k * b = b * a^k];     // from Lexpcomm1a, Lexpcomm1b;
// ! Lexpcomm1a := A[k:nat, a:elg, b:elg, a*b = b*a -> a^k * b = b * a^k];    // use Mathind;
// ! Lexpcomm1b := A[k:neg, a:elg, b:elg, a*b = b*a -> a^k * b = b * a^k];
// ! Texpcomm1 := A[k:int,a,b:elg, a*b = b*a -> (a*b)^k = (a^k)*(b^k)];       // use Mathind, Lexpcomm1;

]; // group :: [ // 2


group :: [   ////////////////////////////////// 4. Macrooperations //////////////////////////////////
// Def('*eS') is '*eS'= F[a:elg ! B:P[elg], R[b:B, a*b]];   
// (a '*eS' B) can be written as (a * B)
// '*eS':= F[a:elg ! B: P[elg], R[b:B, a*b]];
// '*Se':= F[A: P[elg] ! b:elg, R[a:A, a*b]];
// '*SS':= F[A:P[elg] ! B:P[elg], U[a:A, a*B]];                           // Def(a*B) is a*B = R[b:B, a*b];
! LPelg1 := P[elg] ~= {};                           is TPneqemp;          // ! TPneqemp := P[X] ~= {};
// ! LfnlgP := fn(elg # P[elg], P[elg]) ~= {};                            // for checking meS; checked in bool notempty(elem z);
meS := dcl[*, fn(elg # P[elg], P[elg]) ];                                 // ! fn(elg # P[elg], P[elg]): must !!!
mSe := dcl[*, fn(P[elg] # elg, P[elg]) ];
mSS := dcl[*, fn(P[elg] # P[elg], P[elg]) ];
 var W_elg, W_elg1, welg, Velg, elg;  var  Pelg, P[elg];                  // W_elg, W_elg1: synt (formula) variables;
!! AxmeS := * @ meS = F[a:elg, B:P[elg], R[b:B, a*b]];
! TmeS := A[a:elg, B:P[elg], a * B = R[b:B, a*b]];                        byeq AxmeS, Red;
! TmeSt := * @ meS in fn(elg # P[elg], P[elg]);                           is typeaxiom;

! TmeS1 := A[a:elg, B:P1[elg], a*B ~= {}];                               // use !! TR1 := A ~= {} -> R[x:A, F(x)] ~= {};
 Proof TmeS1;
F0 := a in elg;                             assume;
F01 := B in P1[elg];                        assume;
F02 := B ~= {};                             is TP1nemp(F01);             // !! TP1nemp := x in P1[X] -> x~={};
G1 := a*B ~= {};                            by TmeS;
G2 := R[b:B, a*b] ~= {};                    is TR1(F02);                 // !! TR1 := A ~= {} -> R[x:A, F(x)] ~= {};                     
 end Proof TmeS1;

! LmeSU := A[a:elg, B:P[elg], C:P[elg], a * (B\/C) = a*B \/ a*C];
 EqProof LmeSU;
F0 := a in elg;                             assume;
F01 := B in P[elg];                         assume;
F02 := C in P[elg];                         assume;
F03 := B\/C in P[elg];                      by -TinPU; F01 & F02;         // ! TinPU := X in P[A] & Y in P[A] == X \/ Y in P[A];
F1 := a * (B\/C);                           by TmeS;
F2 := R[x: B\/C, a*x];                      by TRU;                       // ! TRU := R[x: A\/B,F(x)] = R[x:A, F(x)] \/ R[x:B, F(x)];                        
F3 := R[x:B, a*x] \/ R[x:C, a*x];           by -TmeS;
F4 := a*B \/ a*C;
 end EqProof LmeSU;

! LmeSI := A[a:elg, B:P[elg], C:P[elg], a * (B/\C) = (a*B) /\ (a*C)];     //  use TRI; 
 EqProof LmeSI;
F0 := a in elg;                             assume;
F01 := B in P[elg];                         assume;
F02 := C in P[elg];                         assume;
F03 := B/\C in P[elg];                      by -TinPI; F01 & F02;         // ! TinPI := X in P[A] & Y in P[A] == X /\ Y in P[A]; 
F1 := a * (B/\C);                           by TmeS;
F2 := R[x: B/\C, a*x];                      by TRI;                       // ! TRU := R[x: A\/B,F(x)] = R[x:A, F(x)] \/ R[x:B, F(x)];                        
F3 := R[x:B, a*x] /\ R[x:C, a*x];           by -TmeS;
F4 := (a*B) /\ (a*C);
 end EqProof LmeSI;

! LmeSIn := A[a:elg, B:P[elg], a * B <: elg]; 
 Proof LmeSIn;
F0 := a in elg;                             assume;
F01 := B in P[elg];                         assume;
G0 := a * B <: elg;                         by TmeS;                      // ! TmeS := A[a:elg, B:P[elg], a * B = R[b:B, a*b]];
G1 := R[b:B, a*b] <: elg;                   by TRA;                       // ! TRA  := R[d, f] <: B == A[d, f in B];   
G2 := A[b:B, a*b in elg];                   is LCL2;                      // ! LCL2  := A[x,y:elg, x*y in elg]; 
 end Proof LmeSIn;

!! AxmSe := * @ mSe = F[A:P[elg], b:elg, R[a:A, a*b]];
// tmSe := fn(P[elg] # elg, P[elg]);
// ! LmSet := fn(P[elg] # elg, P[elg]) ~= {};
! TmSe := A[A:P[elg], b:elg, A*b = R[a:A, a*b]]; byeq AxmSe, Red; 
! TmSet := * @ mSe in fn(P[elg] # elg, P[elg]);  is typeaxiom;

! TmSe1 := A[A:P1[elg], b:elg, A*b ~= {}];                               // use !! TR1 := A ~= {} -> R[x:A, F(x)] ~= {};
 Proof TmSe1;
F0 := A in P1[elg];                         assume;
F01 := b in elg;                            assume;
F02 := A ~= {};                             is TP1nemp(F0);              // !! TP1nemp := x in P1[X] -> x~={};
G1 := A*b ~= {};                            by TmSe;
G2 := R[a:A, a*b] ~= {};                    is TR1(F02);                 // !! TR1 := A ~= {} -> R[x:A, F(x)] ~= {};                     
 end Proof TmSe1;


! LmSeU := A[B:P[elg], C:P[elg], a:elg, (B\/C)*a = B*a \/ C*a];           //  use TRU; 
 EqProof LmSeU; 
F0 := B in P[elg];                          assume;
F01 := C in P[elg];                         assume;
F02 := a in elg;                            assume;
F03 := B\/C in P[elg];                      by -TinPU; F0 & F01;          // ! TinPU := X in P[A] & Y in P[A] == X \/ Y in P[A];
F1 := (B\/C) * a;                           by TmSe;
F2 := R[x: B\/C, x*a];                      by TRU;                       // ! TRU := R[x: A\/B,F(x)] = R[x:A, F(x)] \/ R[x:B, F(x)];                        
F3 := R[x:B, x*a] \/ R[x:C, x*a];           by -TmSe;
F4 := B*a \/ C*a;
 end EqProof LmSeU;

! LmSeI := A[B:P[elg], C:P[elg], a:elg, (B/\C)*a = (B*a) /\ (C*a)];       //  use TRI;
 EqProof LmSeI;
F0 := B in P[elg];                          assume;
F01 := C in P[elg];                         assume;
F02 := a in elg;                            assume;
F03 := B/\C in P[elg];                      by -TinPI; F0 & F01;          // ! TinPI := X in P[A] & Y in P[A] == X /\ Y in P[A]; 
F1 := (B/\C) * a;                           by TmSe;
F2 := R[x: B/\C, x*a];                      by TRI;                       // ! TRU := R[x: A\/B,F(x)] = R[x:A, F(x)] \/ R[x:B, F(x)];                        
F3 := R[x:B, x*a] /\ R[x:C, x*a];           by -TmSe;
F4 := (B*a) /\ (C*a);
 end EqProof LmSeI;

! LmSeIn := A[A:P[elg], b:elg, A * b <: elg];
 Proof LmSeIn;
F0 := A in P[elg];                          assume;
F01 := b in elg;                            assume;
G0 := A * b <: elg;                         by TmSe;                      // ! TmSe := A[A:P[elg], b:elg, A * b = R[a:A, a*b]];
G1 := R[a:A, a*b] <: elg;                   by TRA;                       // ! TRA  := R[d, f] <: B == A[d, f in B];   
G2 := A[a:A, a*b in elg];                   is LCL2;                      // ! LCL2  := A[x,y:elg, x*y in elg]; 
 end Proof LmSeIn;

!! AxmSS := * @ mSS = F[A:P[elg], B:P[elg], U[a:A, a*B]]; 
// ! LmSSt := fn(P[elg] # elg, P[elg]) ~= {};
! TmSS := A[A:P[elg], B:P[elg], A * B = U[a:A, a*B]];                     byeq AxmSS, Red;    
! TmSSt := * @ mSS in fn(P[elg] # P[elg], P[elg]);                        is typeaxiom;     // z in type(z);
! TmSSdom := dom(* @ mSS) = P[elg] # P[elg];                              is Tfndom(TmSSt); // Tfndom := f in fn(A,B) -> dom(f) = A; 

! LmSSIn := A[A:P[elg], B:P[elg], A * B <: elg];
 Proof LmSSIn;
F0 := A in P[elg];                          assume;
F01 := B in P[elg];                         assume;
G0 := A * B <: elg;                         by TmSS;
G1 := U[a:A, a*B] <: elg;                   by TUA;                       // ! TUA := U[d, w] <: A == A[d, w <: A];  
G2 := A[a:A, a*B <: elg];                   is LmeSIn;                    // ! LmeSIn := A[a:elg, B:P[elg], a * B <: elg]; 
 end Proof LmSSIn;                                                        // ! TmSe := A[A:P[elg], b:elg, A * b = R[a:A, a*b]];  
                                                                          // ! TmeS := A[a:elg, B:P[elg], a * B = R[b:B, a*b]];
! TmSSr := A[A:P[elg], B:P[elg], A * B = U[b:B, A*b]];     byeq TmSS,TmeS,TUR1,-TmSe; // ! TUR1 := U[d,R[d1,f]] = U[d1,R[d,f]];
! TmSSR := A[A:P[elg], B:P[elg], A * B = R[a:A,b:B, a*b]]; byeq TmSS,TmeS,TUR2; // ! TUR2 := U[x:t,R[x1:t1, F(x,x1)]] = R[x:t,x1:t1, F(x,x1)];

! TmSSm := A[A:P[elg], B:P[elg], a:A, b:B, a*b in A*B];   
 Proof TmSSm;
F0 := A in P[elg];                          assume;
F01 := B in P[elg];                         assume;
F02 := a in A;                              assume;
F03 := b in B;                              assume;
G0 := a*b in A*B;                           by TmSSR;
G1 := a*b in R[x:A,y:B, x*y];               by TRin;       // !! TRin := z in R[d,f] == E[d, z = f]
G2 := E[x:A,y:B, a*b = x*y];                is Witness(a,b);
 end Proof TmSSm;

! TmSSP1 := A[A:P1[elg], B:P1[elg], A*B in P1[elg]]; 
 Proof TmSSP1;
F0 := A in P1[elg];                         assume; by TP1P; F0a & F0c;   // ! TP1P := S in P1[Y] == S ~= {} & S in P[Y];
F0a := A ~= {};                             by TinnempE;         // ! TinnempE := All(X, X ~= {} == Exist(x, x in X));
F0b := Existx(a, F0b1 := a in A);
F0c := A in P[elg];
F01 := B in P1[elg];                        assume; by TP1P; F01a & F01c;
F01a := B ~= {};                            by TinnempE;
F01b := Existx(b, F01b1 := b in B);
F01c := B in P[elg]; 
F1 := a*b in A*B;                           is TmSSm(A,B,a,b);          
F2 := A*B ~= {};                            is Tinnemp(F1);      // ! Tinnemp := x in X -> X ~= {};  
F3 := A*B <: elg;                           is LmSSIn; by -AxP;  // ! LmSSIn := A[A:P[elg], B:P[elg], A * B <: elg];
F4 := A*B in P[elg];                                             // !! AxP := Z in P[Y] == Z <: Y;
G0 := A*B in P1[elg];                       by TP1P; F2 & F4;           
 end Proof TmSSP1; 
    
! TmsS  := A[a:elg, B:P[elg], {a} * B = a * B];            byeq TmSS,TUS; // ! TUS := U[x:{a}, F(x)] = F(a); 
! TmsS1  := A[A:P[elg], b:elg, A * {b} = A * b];           byeq TmSSr,TUS;
               
! TUrm := A[B_d: P[elg], a:elg, U[d, B_d] * a = U[d, B_d * a]];
 EqProof TUrm;
F0 := B_d in P[elg];                            assume;
F01 := a in elg;                                assume;
F1 := U[d, B_d] * a;                            by TmSe;       // ! TmSe := A[A:P[elg], b:elg, A * b = R[a:A, a*b]]
F2 := R[x: U[d, B_d], x*a];                     by TRUU;       // ! TRUU   := R[x:U[d,w], F(x)] = U[d, R[x:w, F(x)]];
F3 := U[d, R[x:B_d, x*a]];                      by -TmSe;
F4 := U[d, B_d * a];
 end EqProof TUrm;    
 
! TUlm := A[B_d: P[elg], a:elg, a * U[d, B_d] = U[d, a * B_d]];
 EqProof TUlm;
F0 := B_d in P[elg];                            assume;
F01 := a in elg;                                assume;
F1 := a * U[d, B_d];                            by TmeS;       // ! TmeS := A[a:elg, B:P[elg], a * B = R[b:B, a*b]];
F2 := R[x: U[d, B_d], a*x];                     by TRUU;       // ! TRUU   := R[x:U[d,w], F(x)] = U[d, R[x:w, F(x)]];
F3 := U[d, R[x:B_d, a*x]];                      by -TmeS;
F4 := U[d, a * B_d];
 end EqProof TUlm;    
                 
! TRrm := A[b_d: elg, a:elg, R[d, b_d] * a = R[d, b_d * a]];
 EqProof TRrm;
F0 := b_d in elg;                               assume;
F01 := a in elg;                                assume;
F1 := R[d, b_d] * a;                            by TmSe;       // ! TmSe := A[A:P[elg], b:elg, A * b = R[a:A, a*b]]
F2 := R[x: R[d, b_d], x*a];                     by TRR;        // ! TRR  := R[x:R[d,f], G(x)] = R[d, G(f)]; 
F3 := R[d, b_d*a];
 end EqProof TRrm;    

! TRlm := A[b_d: elg, a:elg, a * R[d, b_d] = R[d, a * b_d]];
 EqProof TRlm;
F0 := b_d in elg;                               assume;
F01 := a in elg;                                assume;
F1 := a * R[d, b_d];                            by TmeS;       //  TmeS := A[a:elg, B:P[elg], a * B = R[b:B, a*b]];
F2 := R[x: R[d, b_d], a*x];                     by TRR;        // ! TRR  := R[x:R[d,f], G(x)] = R[d, G(f)]; 
F3 := R[d, a * b_d];
 end EqProof TRlm;    

! TRrmS := A[b_d: elg, A: P[elg], R[d, b_d] * A = U[d, b_d * A]];
 EqProof TRrmS;
F0 := b_d in elg;                               assume;
F01 := A in P[elg];                             assume;
F1 := R[d, b_d] * A;                            by TmSS;       // ! TmSS := A[A:P[elg], B:P[elg], A * B = U[a:A, a*B]]; 
F2 := U[x: R[d, b_d], x*A];                     by TUR;        // ! TUR := U[x:R[d,w], F(x)] = U[d, F(w)]; 
F3 := U[d, b_d*A];                                       
 end EqProof TRrmS;    

! TRlmS := A[b_d: elg, A: P[elg], A * R[d, b_d] = U[d, A * b_d]];
 EqProof TRlmS;
F0 := b_d in elg;                               assume;
F01 := A in P[elg];                             assume;
F1 := A * R[d, b_d];                            by TmSSr;      // ! TmSSr := A[A:P[elg], B:P[elg], A * B = U[b:B, A*b]];
F2 := U[x: R[d, b_d], A*x];                     by TUR;        // ! TUR := U[x:R[d,w], F(x)] = U[d, F(w)]; 
F3 := U[d, A * b_d];                                       
 end EqProof TRlmS;   
 
A_B_P_elg := {A,B; A in P[elg], B in P[elg]};

! TinmSS := A[A_B_P_elg, z in A*B == E[x:A, z in x*B]];
 EqProof TinmSS;
F0 := A in P[elg];                              assume;
F01 := B in P[elg];                             assume;
F1 := z in A*B;                                 by TmSS;       // ! TmSS := A[A:P[elg], B:P[elg], A * B = U[a:A, a*B]];    
F2 := z in U[x:A, x*B];                         by TUin;       // ! TUin := x in U[d, w] == E[d, x in w]; 
F3 := E[x:A, z in x*B];
 end EqProof TinmSS;

! TinmSS1 := A[A_B_P_elg, z in B*A == E[x:B, z in x*A]]; is TinmSS;     // Proof TUrmS(H3) was not checked with TinmSS;

! TinmSSr := A[A_B_P_elg, z in A*B == E[x:B, z in A*x]];
 EqProof TinmSSr;
F0 := A in P[elg];                              assume;
F01 := B in P[elg];                             assume;
F1 := z in A*B;                                 by TmSSr;      // ! TmSSr := A[A:P[elg], B:P[elg], A * B = U[b:B, A*b]];   
F2 := z in U[x:B, A*x];                         by TUin;       // ! TUin := x in U[d, w] == E[d, x in w]; 
F3 := E[x:B, z in A*x];
 end EqProof TinmSSr;
                                                               // ! TmeS := A[a:elg, B:P[elg], a * B = R[b:B, a*b]]; 
! TinmeS := A[A:P[elg], x,x1:elg, x1 in x*A == E[a:A, x1 = x*a]];  byeq TmeS, TRin;  // !! TRin := z in R[d,f] == E[d, z = f]

! TUrmS := A[A_B_P_elg, U[d, B] * A = U[d, B * A]];                    // right multiplication on set
 Proof TUrmS;
F0 := A in P[elg];                              assume;
F01 := B in P[elg];                             assume;
F1 := U[d,B] * A = U[d, B * A];                 by AxextA;
F2 := All(z, z in U[d,B] * A == z in U[d, B * A]);       
  EqProof F2;
H0 := assume(z);
H1 := z in U[d,B]*A;                            by TmSS;        // ! TmSS := A[A:P[elg], B:P[elg], A * B = U[a:A, a*B]]; 
H2 := z in U[x:U[d, B], x*A];                   by TUUin;       // ! TUUin := z in U[x:U[d1,f1],F(x)] == E[d,E[x:f1,z in F(x)]];
H3 := E[d, E[x:B, z in x*A]];                   by -TinmSS1;     // ! TinmSS := A[A_B_P_elg, z in A*B == E[x:A, z in x*B]];
H4 := E[d, z in B * A];                         by -TUin;       // ! TUin := x in U[d, w] == E[d, x in w]; 
H5 := z in U[d, B * A];
  end EqProof F2;  
 end Proof TUrmS; 

! TUlmS := A[A_B_P_elg, A * U[d,B] = U[d, A*B]];                // right multiplication on set
 Proof TUlmS;
F0 := A in P[elg];                              assume;
F01 := B in P[elg];                             assume;
F1 := A * U[d, B] = U[d, A * B];                by AxextA;
F2 := All(z, z in A * U[d, B] == z in U[d, A*B]);       
  EqProof F2;
H0 := assume(z);  
H1 := z in A * U[d,B];                          by TmSSr;       // ! TmSSr := A[A:P[elg], B:P[elg], A * B = U[b:B, A*b]]; 
H2 := z in U[x:U[d, B], A*x];                   by TUUin;       // ! TUUin := z in U[x:U[d1,f1],F(x)] == E[d,E[x:f1,z in F(x)]];
H3 := E[d, E[x:B, z in A*x]];                   by -TinmSSr;    // ! TinmSSr := A[A,B: P[elg], z in A*B == E[x:B, z in A*x]];
H4 := E[d, z in A * B];                         by -TUin;       // ! TUin := x in U[d, w] == E[d, x in w]; 
H5 := z in U[d, A * B];
  end EqProof F2;  
 end Proof TUlmS; 

! AssoceeS := A[a:elg, b:elg, C:P[elg], a*(b*C) = (a*b)*C];
 EqProof AssoceeS;
F0 := a in elg;                                 assume;
F01 := b in elg;                                assume;
F02 := C in P[elg];                             assume;
F1 := a*(b*C);                                  by TmeS;        //  TmeS := A[a:elg, B:P[elg], a * B = R[b:B, a*b]];
F2 := a * R[c:C, b*c];                          by TRlm;        // ! TRlm := A[b_d: elg, a:elg, a * R[d, b_d] = R[d, a * b_d]];
F3 := R[c:C, a*(b*c)];                          by AxAssoc;     // AxAssoc:= A[x,y,z: elg, x*(y*z) = (x*y)*z ];
F4 := R[c:C, (a*b)*c];                          by -TmeS;
F5 := (a*b)*C;
 end EqProof AssoceeS;

! AssoceSe := A[a:elg, B:P[elg], c:elg, a*(B*c) = (a*B)*c];
 EqProof AssoceSe;
F0 := a in elg;                                 assume;
F01 := B in P[elg];                             assume;
F02 := c in elg;                                assume;
F1 := a*(B*c);                                  by TmSe;        // ! TmSe := A[A:P[elg], b:elg, A * b = R[a:A, a*b]]
F2 := a * R[b:B, b*c];                          by TRlm;        // ! TRlm := A[b_d: elg, a:elg, a * R[d, b_d] = R[d, a * b_d]];
F3 := R[b:B, a*(b*c)];                          by AxAssoc;     // AxAssoc:= A[x,y,z: elg, x*(y*z) = (x*y)*z ];
F4 := R[b:B, (a*b)*c];                          by -TRrm;       // ! TRrm := A[b_d: elg, a:elg, R[d, b_d] * a = R[d, b_d * a]];
F5 := R[b:B, (a*b)] * c;                        by -TmeS;       // ! TmeS := A[a:elg, B:P[elg], a * B = R[b:B, a*b]];
F6 := (a*B)*c; 
 end EqProof AssoceSe;

! AssocSee := A[A:P[elg], b:elg, c:elg, A*(b*c) = (A*b)*c];
 EqProof AssocSee;
F0 := A in P[elg];                              assume;
F01 := b in elg;                                assume;
F02 := c in elg;                                assume;
F1 := A*(b*c);                                  by TmSe;        // ! TmSe := A[A:P[elg], b:elg, A * b = R[a:A, a*b]];
F2 := R[a:A, a*(b*c)];                          by AxAssoc;     // AxAssoc:= A[x,y,z: elg, x*(y*z) = (x*y)*z ];
F3 := R[a:A, (a*b)*c];                          by -TRrm;       // ! TRrm := A[b_d: elg, a:elg, R[d, b_d] * a = R[d, b_d * a]];
F4 := R[a:A, (a*b)]*c;                          by -TmSe;       // ! TmSe := A[A:P[elg], b:elg, A * b = R[a:A, a*b]];
F5 := (A*b)*c;
 end EqProof AssocSee;

! AssoceSS := A[a:elg, B: P[elg], C:P[elg], a*(B*C) = (a*B)*C];
 EqProof AssoceSS;
F0 := a in elg;                                 assume;
F01 := B in P[elg];                             assume;
F02 := C in P[elg];                             assume;
F1 := a*(B*C);                                  by TmSSr;       // ! TmSSr := A[A:P[elg], B:P[elg], A * B = U[b:B, A*b]];
F2 := a * U[c:C, B*c];                          by TUlm;        // ! TUlm := A[B_d: P[elg], a:elg, a * U[d, B_d] = U[d, a * B_d]];
F3 := U[c:C, a*(B*c)];                          by AssoceSe;    // ! AssoceSe := A[a:elg, B:P[elg], c:elg, a*(B*c) = (a*B)*c];
F4 := U[c:C, (a*B)*c];                          by -TmSSr;      // ! TUrmS := A[A, B: P[elg], U[d, B] * A = U[d, B * A]];
F5 := (a*B)*C;
 end EqProof AssoceSS;

! AssocSeS := A[A:P[elg], b:elg, C:P[elg], A*(b*C) = (A*b)*C];
 EqProof AssocSeS;
F0 := A in P[elg];                              assume;
F01 := b in elg;                                assume;
F02 := C in P[elg];                             assume;
F1 := A*(b*C);                                  by TmSS;        // ! TmSS := A[A:P[elg], B:P[elg], A * B = U[a:A, a*B]];
F2 := U[a:A, a*(b*C)];                          by AssoceeS;    // ! AssoceeS := A[a:elg, b:elg, C:P[elg], a*(b*C) = (a*b)*C];
F3 := U[a:A, (a*b)*C];                          by -TRrmS;      // ! TRrmS := A[b_d: elg, A: P[elg], R[d, b_d] * A = U[d, b_d * A]];
F4 := R[a:A, a*b] * C;                          by -TmSe;       // ! TmSe := A[A:P[elg], b:elg, A * b = R[a:A, a*b]];
F5 := (A*b) * C;                            
 end EqProof AssocSeS;

! AssocSSe := A[A:P[elg], B: P[elg], c:elg, A*(B*c) = (A*B)*c];
 EqProof AssocSSe;
F0 := A in P[elg];                              assume;
F01 := B in P[elg];                             assume;
F02 := c in elg;                                assume;
F1 := A*(B*c);                                  by TmSS;        // ! TmSS := A[A:P[elg], B:P[elg], A * B = U[a:A, a*B]];
F2 := U[a:A, a*(B*c)];                          by AssoceSe;    // ! AssoceSe := A[a:elg, B:P[elg], c:elg, a*(B*c) = (a*B)*c];
F3 := U[a:A, (a*B)*c];                          by -TUrm;       // ! TUrm := A[B_d: P[elg], a:elg, U[d, B_d] * a = U[d, B_d * a]];
F4 := U[a:A, a*B] * c;                          by -TmSS;       // ! TmSS := A[A:P[elg], B:P[elg], A * B = U[a:A, a*B]];
F5 := (A*B) * c;                            
 end EqProof AssocSSe;

! AssocSSS := A[A:P[elg], B:P[elg], C:P[elg], A*(B*C) = (A*B)*C];
 EqProof AssocSSS;
F0 := A in P[elg];                              assume;
F01 := B in P[elg];                             assume;
F02 := C in P[elg];                             assume;
F1 := A*(B*C);                                  by TmSS;        // ! TmSS := A[A:P[elg], B:P[elg], A * B = U[a:A, a*B]];
F2 := U[a:A, a*(B*C)];                          by AssoceSS;    // ! AssoceSS := A[a:elg, B: P[elg], C:P[elg], a*(B*C) = (a*B)*C];
F3 := U[a:A, (a*B)*C];                          by -TUrmS;      // ! TUrmS := A[A, B: P[elg], U[d, B] * A = U[d, B * A]]
F4 := U[a:A, a*B] * C;                          by -TmSS;       // ! TmSS := A[A:P[elg], B:P[elg], A * B = U[a:A, a*B]];
F5 := (A*B)*C;                            
 end EqProof AssocSSS;

! Teqpr := A[S:P[elg], g:elg, eqp(S*g, S)];     // equipollent right; // S*g ~ S
 Proof Teqpr;
F0 := S in P[elg];                              assume;
F01 := g in elg;                                assume;
f := F[x:S, x*g];
F1 := dom(f) = S;                               is TFdom1;      // ! TFdom1 := dom(FAGx) = A; // FAGx := F[x:A, G(x)];
F2 := im(f) = S*g;                              by TimF;        // ! TimF   := im(F[d, g]) = R[d, g];
F3 := R[x:S, x*g] = S*g;                        is -TmSe;       // ! TmSe := A[A:P[elg], b:elg, A * b = R[a:A, a*b]];
F4 := injective(f);                             by TFinj;       // ! TFinj := injective(F[x:A, G(x)]) == A[x1,x2:A, G(x1)=G(x2) -> x1=x2];
F5 := A[x1,x2: S, x1*g = x2*g -> x1 = x2];
  Proof F5;
H0 := x1 in S;                                  assume;
H01 := x2 in S;                                 assume;
H02 := x1*g = x2*g;                             assume; by -Tcancel_law1A; // ! Tcancel_law1A := A[a,b,c: elg, a = b == a*c = b*c];
H1 := x1 = x2;
  end Proof F5;
F6 := f in sfn(S,S*g);                          by -F1;          // ! Tsfndomim := A[f:FN, f in sfn(dom(f), im(f))];
F7 := f in sfn(dom(f),S*g);                     by -F2; is Tsfndomim;  // was  by -F1, -F4; // was error(in prpt: maxdepth)
F8 := f in bfn(S,S*g);                          by Tbfnin2; F6 & F4;    // ! Tbfnin2 := f in bfn(A,B) == f in sfn(A,B) & injective(f);
G0 := eqp(S*g, S);                              is Teqp4a(F8);  // ! Teqp4a := f in bfn(A,B) -> eqp(B,A);
 end Proof Teqpr;

! Teqpl := A[S:P[elg], g:elg, eqp(g*S, S)];     // equipollent left; // g*S ~ S
 Proof Teqpl;
F0 := S in P[elg];                              assume;
F01 := g in elg;                                assume;
f := F[x:S, g*x];
F1 := dom(f) = S;                               is TFdom1;      // ! TFdom1 := dom(FAGx) = A; // FAGx := F[x:A, G(x)];
F2 := im(f) = g*S;                              by TimF;        // ! TimF   := im(F[d, g]) = R[d, g];
F3 := R[x:S, g*x] = g*S;                        is -TmeS;       // ! TmeS := A[a:elg, B:P[elg], a * B = R[b:B, a*b]];
F4 := injective(f);                             by TFinj;       // ! TFinj := injective(F[x:A, G(x)]) == A[x1,x2:A, G(x1)=G(x2) -> x1=x2];
F5 := A[x1,x2: S, g*x1 = g*x2 -> x1 = x2];
  Proof F5;
H0 := x1 in S;                                  assume;
H01 := x2 in S;                                 assume;
H02 := g*x1 = g*x2;                             assume; by -Tcancel_law2A; // ! Tcancel_law2A := A[a,b,c: elg,  a = b == c*a = c*b];
H1 := x1 = x2;
  end Proof F5;
F6 := f in sfn(S,g*S);                          by -F1;               // ! Tsfndomim := A[f:FN, f in sfn(dom(f), im(f))];
F7 := f in sfn(dom(f),g*S);                     by -F2; is Tsfndomim; // was  by -F1, -F4; // was error(in prpt: maxdepth)
F8 := f in bfn(S,g*S);                          by Tbfnin2; F6 & F4;  // ! Tbfnin2 := f in bfn(A,B) == f in sfn(A,B) & injective(f);
G0 := eqp(g*S, S);                              is Teqp4a(F8);        // ! Teqp4a := f in bfn(A,B) -> eqp(B,A);
 end Proof Teqpl;

! LrSein   := A[S:P[elg], x:S, g:elg, x * g in S * g];
 Proof LrSein;
F0 := S in P[elg];                              assume;
F01 := x in S;                                  assume;
F02 := g in elg;                                assume;
F1 := x*g in S*g;                               by TmSe;              // ! TmSe := A[A:P[elg], b:elg, A * b = R[a:A, a*b]];
F2 := x*g in R[a:S, a*g];                       by TRin;              // ! TRin := z in R[d,f] == E[d, z = f];
F3 := E[a:S, x*g = a*g];                        is Witness(x);
 end Proof LrSein;

! LrSein1   := A[{A,B,a,c; A in P[elg], B in P[elg], a in A, c in elg, Ax5 := A = B*c}, Exist(b, b in B & a = b*c)];
 Proof LrSein1;
F0 := a in A;                                  assume;  by Ax5;
F1 := a in B*c;                                by TmSe;               // ! TmSe := A[A:P[elg], b:elg, A * b = R[a:A, a*b]];
F2 := a in R[b:B, b*c];                        by TRin;               // !! TRin := z in R[d,f] == E[d, z = f];
F3 := E[b:B, a = b*c];                         by AxEconj;            // !! AxEconj := E[x:B, Q(x)] == Exist(x, x in B & Q(x));
F4 := Exist(b, b in B & a = b*c);
 end Proof LrSein1;

! LlSein1   := A[{A,B,a,c; A in P[elg], B in P[elg], a in A, c in elg, Ax5 := A = c*B}, Exist(b, b in B & a = c*b)];
 Proof LlSein1;
F0 := a in A;                                  assume;  by Ax5;
F1 := a in c*B;                                by TmeS;               // ! TmeS := A[a:elg, B:P[elg], a * B = R[b:B, a*b]];
F2 := a in R[b:B, c*b];                        by TRin;               // !! TRin := z in R[d,f] == E[d, z = f];
F3 := E[b:B, a = c*b];                         by AxEconj;            // !! AxEconj := E[x:B, Q(x)] == Exist(x, x in B & Q(x));
F4 := Exist(b, b in B & a = c*b);
 end Proof LlSein1;

// ! TmSee := A[A:P[elg], A*e = A];             same as LSe;
//  EqProof TmSee;
// F0 := A in P[elg];                           assume;
// F1 := A*e;                                   by TmSe;
// F2 := R[a:A, a*e];                           by Axre;              // Axre   := A[x:elg, x * e = x];
// F3 := R[a:A, a];                             by TRwhole;           // ! TRwhole := R[x:S, x] = S;
// F4 := A;                                    
//  end EqProof TmSee;

// ! LmeSeIn := A[B:P[elg], e*B = B];                    same as LeS;
//  EqProof LmeSeIn;
// F0 := B in P[elg];                           assume;
// F1 := e*B;                                   by TmeS;                 // ! TmeS := A[a:elg, B:P[elg], a * B = R[b:B, a*b]];           
// F2 := R[b:B, e*b];                           by Tle;                  // ! Tle := e*a = a;
// F3 := R[b:B, b];                             by TRwhole;              // ! TRwhole := R[x:S, x] = S;
// F4 := B;                                                                      
//  end EqProof LmeSeIn;                               

! LSe := A[S:P[elg], S * e = S];                byeq TmSe,Axre,TRwhole;   // Axre := A[x:elg, x * e = x];
! LeS := A[S:P[elg], e * S = S];                byeq TmeS,Tle,TRwhole;    // ! TmSe := A[A:P[elg], b:elg, A * b = R[a:A, a*b]];
! Lex := A[x:elg, {e} * x = {x}];               byeq TmSe,TRcol1,Tle;     // ! TRcol1 := R[x:{a}, F(x)] = {F(a)}; 
! Lxe := A[x:elg, x * {e} = {x}];               byeq TmeS,TRcol1,Axre;    // ! TmeS := A[a:elg, B:P[elg], a * B = R[b:B, a*b]];
! LXe := A[X:P[elg], X * {e} = X];              byeq TmSS,Lxe,TUwhole;    // ! TUwhole := U[x:S, {x}] = S;
! LeX := A[X:P[elg], {e} * X = X];              byeq TmSS,TUS,LeS;        // ! TmSS := A[A:P[elg], B:P[elg], A * B = U[a:A, a*B]]; 
                                                                          // !! TUS := U[x:{a}, F(x)] = F(a); 
! TSSIn := A[A,B,C: P[elg], A <: B -> A*C <: B*C];
 Proof TSSIn;
F0 := A in P[elg];                   assume;
F01 := B in P[elg];                  assume;
F02 := C in P[elg];                  assume;
F03 := A <: B;                       assume;
F1 := A*C <: B*C;                    by TmSS;                // ! TmSS := A[A:P[elg], B:P[elg], A * B = U[a:A, a*B]];
F2 := U[x:A, x*C] <: U[x:B, x*C];    is TUm1(F03);           // ! TUm1 := A <: B -> U[x:A, Q(x)] <: U[x:B, Q(x)];     // m: monotone
 end Proof TSSIn;


! TSSIn1 := A[A,B,C: P[elg], A <: B -> C*A <: C*B];
 Proof TSSIn1;
F0 := A in P[elg];                   assume;
F01 := B in P[elg];                  assume;
F02 := C in P[elg];                  assume;
F03 := A <: B;                       assume;
F1 := C*A <: C*B;                    by TmSSr;               // ! TmSSr := A[A:P[elg], B:P[elg], A * B = U[b:B, A*b]];
F2 := U[x:A, C*x] <: U[x:B, C*x];    is TUm1(F03);           // ! TUm1 := A <: B -> U[x:A, Q(x)] <: U[x:B, Q(x)];             // m: monotone
 end Proof TSSIn1; 

! TmSSe := A[A_B_P_elg, e in B -> A <: A*B];
 Proof TmSSe;
F0 := A in P[elg];                   assume;
F00 := e in B;                       assume; by -TSIn;    // TSIn := {a} <: X1 == a in X1; 
F01 := {e} <: B;
F1 := {e} <: B -> A*{e} <: A*B;      is TSSIn1;           // ! TSSIn1 := A[A,B,C: P[elg], A <: B -> C*A <: C*B];
F2 := A*{e} <: A*B;                  is F1(F01); by LXe;
F3 := A <: A*B;
 end  Proof TmSSe;

! TmSSe1 := A[A_B_P_elg, e in B -> A <: B*A];
 Proof TmSSe1;
F0 := A in P[elg];                   assume;
F00 := e in B;                       assume; by -TSIn;    // ! TSIn := {a} <: X1 == a in X1; 
F01 := {e} <: B;
F1 := {e} <: B -> {e}*A <: B*A;      is TSSIn;            // ! TSSIn := A[A,B,C: P[elg], A <: B -> A*C <: B*C];
F2 := {e}*A <: B*A;                  is F1(F01); by LeX; 
F3 := A <: B*A;
 end  Proof TmSSe1;


! TmeSe := A[a:elg, B:P[elg], e in B -> a in a*B];   // ! TmeSe := A[{a,B; a in elg, B in P[elg], e in B}, a in a*B];
 Proof TmeSe;
F0 := a in elg;                      assume;
F01 := B in P[elg];                  assume;
F02 := e in B;                       assume;   
F03 := a*e = a;                      is Axre; by Axsym;  // ! Axre   := A[x:elg, x * e = x]; 
F04 := a = a*e;              
G0 := a in a*B;                      by TmeS;            // ! TmeS := A[a:elg, B:P[elg], a * B = R[b:B, a*b]];                              
G1 := a in  R[b:B, a*b];             by TRin;            // !! TRin := z in R[d,f] == E[d, z = f]; 
G2 := E[b:B, a = a*b];               is Witness(e);
 end Proof TmeSe;

! L01 := elg in P[elg];               is TPin1;          // TPin1 := X in P[X];
! Telgm1 := A[a:elg, a * elg = elg];  byeq TmeS,TRelgl;  // ! TRelgl := R[x:elg, a*x] = elg;
! Telgm2 := A[a:elg, elg * a = elg];  byeq TmSe,TRelgr;  // ! TRelgr := R[x:elg, x*a] = elg;

! Telgm1S := A[A:P1[elg], A * elg = elg];
 EqProof Telgm1S;
F0 := A in P1[elg];                  assume;
F1 := A * elg;                       by TmSS;           // ! TmSS := A[A:P[elg], B:P[elg], A * B = U[a:A, a*B]];
F2 := U[x:A, x*elg];                 by Telgm1;         // ! Telgm1 := A[a:elg, a * elg = elg];
F3 := U[x:A, elg];                   by TUfree1;        // ! TUfree1 := A ~= {} -> U[x:A, G] = G; 
F4 := elg;
 end EqProof Telgm1S;

! Telgm2S := A[A:P1[elg], elg * A = elg];
 EqProof Telgm2S;
F0 := A in P1[elg];                  assume;
F1 := elg * A;                       by TmSSr;         // ! TmSSr := A[A:P[elg], B:P[elg], A * B = U[b:B, A*b]];
F2 := U[x:A, elg*x];                 by Telgm2;        // ! Telgm2 := A[a:elg, elg * a = elg];
F3 := U[x:A, elg];                   by TUfree1;       // ! TUfree1 := A ~= {} -> U[x:A, G] = G; 
F4 := elg;
 end EqProof Telgm2S;

! Telgm   := elg*elg = elg;          is Telgm1S;       // ! Telgm1S := A[A:P1[elg], A * elg = elg];

! TRmfree1 := A[A:P[elg],a:elg, R[x:A, a * W_elg1(x)] = a * R[x:A, W_elg1(x)]];       // scheme: a is free from x, W_elg is not;
 EqProof -TRmfree1;                 // was error in checking of EqProof TmRR (F3-F4), if W_elg(x): not W_elg1(x)
F0 := A in P[elg];                   assume;
F01 := a in elg;                     assume;
F1 := a * R[x:A, W_elg1(x)];         by TmeS;          // ! TmeS := A[a:elg, B:P[elg], a * B = R[b:B, a*b]];
F2 := R[y:R[x:A, W_elg1(x)], a*y];   by TRR;           // ! TRR  := R[x:R[d,f], G(x)] = R[d, G(f)];
F3 := R[x:A, a * W_elg1(x)];
 end EqProof -TRmfree1;

! TRmfree2 := A[A:P[elg],a:elg, R[x:A, W_elg1(x) * a] = R[x:A, W_elg1(x)] * a]; // scheme: a is free from x, W_elg is not;
 EqProof -TRmfree2;
F0 := A in P[elg];                  assume;
F01 := a in elg;                    assume;
F1 := R[x:A, W_elg1(x)] * a;        by TmSe;           // ! TmSe := A[A:P[elg], b:elg, A * b = R[a:A, a*b]];
F2 := R[y:R[x:A, W_elg1(x)], y*a];  by TRR;            // ! TRR  := R[x:R[d,f], G(x)] = R[d, G(f)];
F3 := R[x:A, W_elg1(x) * a];
 end EqProof -TRmfree2;

! TmRR := A[A_B_P_elg, R[a:A,W_elg(a)] * R[b:B,W_elg1(b)] = R[a:A,b:B, W_elg(a) * W_elg1(b)]]; 
 EqProof TmRR;
F0 := A in P[elg];                                 assume;
F01 := B in P[elg];                                assume;
F1 := R[a:A,W_elg(a)] * R[b:B,W_elg1(b)];          by TmSS;       // ! TmSS := A[A:P[elg], B:P[elg], A * B = U[a:A, a*B]];
F2 := U[x:R[a:A, W_elg(a)], x * R[b:B,W_elg1(b)]]; by TUR;        // ! TUR := U[x:R[d,w], F(x)] = U[d, F(w)];
F3 := U[a:A, W_elg(a) * R[b:B, W_elg1(b)]];        by -TRmfree1;  // was an error, no theory of syntactic variables;
F4 := U[a:A, R[b:B, W_elg(a) * W_elg1(b)]];        by TUR2;       // ! TUR2 := U[x:t,R[x1:t1, F(x,x1)]] = R[x:t,x1:t1, F(x,x1)]; 
F5 := R[a:A,b:B, W_elg(a) * W_elg1(b)];
 end EqProof TmRR;

! TminS1 := A[a,x:elg, B:P[elg], a*x in B == a in B*inv(x)];
 EqProof TminS1;
F0 := a in elg;                                 assume;
F01 := x in elg;                                assume;
F02 := B in P[elg];                             assume;
F1 := a*x in B;                                 by TinEeq;    // ! TinEeq := x in A == E[a:A, a = x];
F2 := E[b:B, b = a*x];                          by Teqml1;    // ! ! Teqml1 := A[a,x,b: elg, b = x*a  == x = b * inv(a)];
F3 := E[b:B, a = b*inv(x)];                     by -TRin;     // ! TRin := z in R[d,f] == E[d, z = f];
F4 := a in R[b:B, b*inv(x)];                    by -TmSe;     // ! TmSe := A[A:P[elg], b:elg, A * b = R[a:A, a*b]];
F5 := a in B*inv(x);
 end EqProof TminS1;

! TminS1a := A[a,x:elg, B:P[elg], a*inv(x) in B == a in B*x];           byeq TminS1, Tinvinv;  // ! Tinvinv := A[x:elg, inv(inv(x)) = x];
! TminS1a1 := A[a,x:elg, B:P[elg], a in B*x == a*inv(x) in B];          by Teqvsym; TminS1a;
! TminS2 := A[a,x:elg, B:P[elg], x*a in B == a in inv(x)*B];
 EqProof TminS2;
F0 := a in elg;                                 assume;
F01 := x in elg;                                assume;
F02 := B in P[elg];                             assume;
F1 := x*a in B;                                 by TinEeq;    // ! TinEeq := x in A == E[a:A, a = x];
F2 := E[b:B, b = x*a];                          by Teqmr1;    // ! Teqmr1 := A[a,x,b: elg, b = a*x == x = inv(a)*b];
F3 := E[b:B, a = inv(x)*b];                     by -TRin;     // ! TRin := z in R[d,f] == E[d, z = f];
F4 := a in R[b:B, inv(x)*b];                    by -TmeS;     // ! TmeS := A[a:elg, B:P[elg], a * B = R[b:B, a*b]];
F5 := a in inv(x)*B;
 end EqProof TminS2;

! TminS2a := A[a,x:elg, B:P[elg], inv(x)*a in B == a in x*B];           byeq TminS2, Tinvinv;  
! TminS2a1 := A[a,x:elg, B:P[elg], a in x*B == inv(x)*a in B];          by Teqvsym; TminS2a;  // ! Teqvsym := (p==q) == (q==p);
! TmInS1S := A[x:elg, A,B:P[elg], A*x <: B == A <: B*inv(x)]; 
 EqProof TmInS1S;
F0 := x in elg;                                 assume;
F01 := A in P[elg];                             assume;
F02 := B in P[elg];                             assume;
F1 := A*x <: B;                                 by TmSe;          // ! TmSe := A[A:P[elg], b:elg, A * b = R[a:A, a*b]];
F2 := R[a:A, a*x] <: B;                         by TRA;           // ! TRA  := R[d, f] <: B == A[d, f in B]; 
F3 := A[a:A, a*x in B];                         by TminS1;        // ! TminS1 := A[a,x:elg, B:P[elg], a*x in B == a in B*inv(x)];
F4 := A[a:A, a in B*inv(x)];                    by -TInA;         // ! TInA := A <: B == A[x:A, x in B]; 
F5 := A <: B*inv(x);
 end EqProof TmInS1S;

! TmInS1S1 := A[x:elg, A,B:P[elg], A*inv(x) <: B == A <: B*x];              byeq TmInS1S, Tinvinv; // ! Tinvinv := A[x:elg, inv(inv(x)) = x];

! TmInS2S := A[x:elg, A,B:P[elg], x*A <: B == A <: inv(x)*B];
 EqProof TmInS2S;
F0 := x in elg;                                 assume;
F01 := A in P[elg];                             assume;
F02 := B in P[elg];                             assume;
F1 := x*A <: B;                                 by TmeS;          // ! TmeS := A[a:elg, B:P[elg], a * B = R[b:B, a*b]];
F2 := R[a:A, x*a] <: B;                         by TRA;           // ! TRA  := R[d, f] <: B == A[d, f in B]; 
F3 := A[a:A, x*a in B];                         by TminS2;        // ! TminS2 := A[a,x:elg, B:P[elg], x*a in B == a in inv(x)*B];
F4 := A[a:A, a in inv(x)*B];                    by -TInA;         // ! TInA := A <: B == A[x:A, x in B]; 
F5 := A <: inv(x)*B;
 end EqProof TmInS2S;

! TmInS2S1 := A[x:elg, A,B:P[elg], inv(x)*A <: B == A <: x*B];             byeq TmInS2S, Tinvinv; // ! Tinvinv := A[x:elg, inv(inv(x)) = x];          

! TmInS3S :=  A[x,y:elg, A,B:P[elg], x*A*y <: B == A <: inv(x)*B*inv(y)];  byeq TmInS1S,TmInS2S,AssoceSe;
                                                                           // ! TmInS1S := A[x:elg, A,B:P[elg], A*x <: B == A <: B*inv(x)]; 
! TmInS3S1 :=  A[x,y:elg, A,B:P[elg], x*A*y <: B == A[a:A, x*a*y in B]];
 EqProof TmInS3S1;
F0 := x in elg;                                assume;
F01 := y in elg;                               assume;
F02 := A in P[elg];                            assume;
F03 := B in P[elg];                            assume;
F1 := x*A*y <: B ;                             by TmSe;          // ! TmSe := A[A:P[elg], b:elg, A * b = R[a:A, a*b]];
F2 := R[z: x*A, z*y] <: B;                     by TmeS;          // ! TmeS := A[a:elg, B:P[elg], a * B = R[b:B, a*b]];
F3 := R[z: R[a:A, x*a], z*y] <: B;             by TRR;           // ! TRR  := R[x:R[d,f], G(x)] = R[d, G(f)];
F4 := R[a:A, (x*a)*y] <: B;                    by TRA;           // ! TRA  := R[d, f] <: B == A[d, f in B];
F5 := A[a:A, x*a*y in B];
 end EqProof TmInS3S1;                                                      // ! Tinvinv := A[x:elg, inv(inv(x)) = x];
                                                    
! TmeSinvIn := A[x:elg, A:P[elg], B:P[elg], inv(x)*A*x <: B == A <: x*B*inv(x)];  byeq TmInS3S,Tinvinv; 
! TmeSinvIn1 := A[x:elg, A:P[elg], B:P[elg], x*A*inv(x) <: B == A <: inv(x)*B*x]; byeq TmInS3S,Tinvinv;
! TmeSinvIn2 := A[x:elg, A:P[elg], B:P[elg], x*A*inv(x) <: B == A[a:A, x*a*inv(x) in B]]; is TmInS3S1;

invS := F[A:P[elg], R[a:A, inv(a)]];              // was  dcl[invS,P[elg],P[elg]];
! TinvS_type := invS in fn(P[elg],P[elg]);        is typeaxiom;
! TinvS := A[A:P[elg], invS(A) = R[a:A, inv(a)]]; is Red;           // was: is TFred;

! TinvSml  := A[a:elg, B:P[elg], invS(a*B) = invS(B) * inv(a)];
 EqProof TinvSml;
F0 := a in elg;                   assume;                 // AxinvS := invS(Pelg) = R[a:Pelg, inv(a)]; // var  Pelg, P[elg];
F01 := B in P[elg];               assume;                 // ! TmeS := A[a:elg, B:P[elg], a * B = R[b:B, a*b]];
F1 := invS(a*B);                  by TinvS, TmeS;         // R[x:a*B,inv(x)] = R[x:R[b:B, a*b], inv(x)]; 
F2 := R[x: R[b:B, a*b], inv(x)];  by TRR;                 // TRR  := R[x:R[d,f], G(x)] = R[d, G(f)];
F3 := R[b:B, inv(a*b)];           by Tinvmlt;             // ! Tinvmlt := A[x,y:elg, inv(x*y) = inv(y) * inv(x)];  
F4 := R[b:B, inv(b)*inv(a)];      by TRmfree2;            // ! TRmfree2 := A[A:P[elg],a:elg, R[x:A, W_elg1(x) * a] = R[x:A, W_elg1(x)] * a];
F5 := R[b:B, inv(b)]*inv(a);      by -TinvS;              // ! TinvS := A[A:P[elg], invS(A) = R[a:A, inv(a)]];
F6 := invS(B) * inv(a);                                   // F4: scheme:  a is free from x, W_elg is not;                                       
 end EqProof TinvSml;         
       
! TinvSmr  := A[A:P[elg], b:elg, invS(A*b) = inv(b) * invS(A)];
 EqProof TinvSmr;
F0 := A in P[elg];                assume;                 // AxinvS := invS(Pelg) = R[a:Pelg, inv(a)]; // var  Pelg, P[elg];
F01 := b in elg;                  assume;                 // TmSe := A[A:P[elg], b:elg, A * b = R[a:A, a*b]];
F1 := invS(A*b);                  by TinvS, TmSe;         // R[x:A*b,inv(x)] = R[x:R[a:A, a*b], inv(x)]; 
F2 := R[x: R[a:A, a*b], inv(x)];  by TRR;                 // TRR  := R[x:R[d,f], G(x)] = R[d, G(f)];
F3 := R[a:A, inv(a*b)];           by Tinvmlt;             // ! Tinvmlt := A[x,y:elg, inv(x*y) = inv(y) * inv(x)];
F4 := R[a:A, inv(b)*inv(a)];      by TRmfree1;            // ! TRmfree1 := R[x:elg, W_elg * W_elg1(x)] = W_elg * R[x:elg, W_elg1(x)];
F5 := inv(b)*R[a:A,inv(a)];       by -TinvS;
F6 := inv(b) * invS(A);                                         
 end EqProof TinvSmr;                                         

! TeqSmr   := A[x:elg, A,B:P[elg], A*x = B == A = B*inv(x)];   // byeq Axext,TmInS1S,-TmInS1S1, -Axext; was error: -TmInS1S1;
 EqProof TeqSmr;                     // no error in EqProof TeqSmr: because isbe has additional information: req(V,V1) checked at the beginning;
F0 := x in elg;                      assume;
F01 := A in P[elg];                  assume;
F02 := B in P[elg];                  assume;
F1 := A*x = B;                       by Axext;                 // ! Axext := X = Y == X <: Y & Y <: X;  
F2 := A*x <: B & B <: A*x;           by TmInS1S;               // ! TmInS1S := A[x:elg, A,B:P[elg], A*x <: B == A <: B*inv(x)];
F3 := A <: B*inv(x) & B <: A*x;      by -TmInS1S1;             // ! TmInS1S1 := A[x:elg, A,B:P[elg], A*inv(x) <: B == A <: B*x];
F4 := A <: B*inv(x) & B*inv(x) <: A; by -Axext;
F5 := A = B*inv(x);  
 end EqProof TeqSmr;

! TeqSmr1  := A[x:elg, A,B:P[elg], A = B*x == A*inv(x) = B];   // byeq Axext,-TmInS1S1,TmInS1S, -Axext; was error: -TmInS1S1;
 EqProof TeqSmr1;                                              // A:x*H, B:H => x*H = H*x  == x*H*inv(x) = H   ; for L12;           
F0 := x in elg;                      assume;     
F01 := A in P[elg];                  assume;
F02 := B in P[elg];                  assume;
F1 := A = B*x;                       by Axext;                // ! Axext := X = Y == X <: Y & Y <: X;  
F2 := A <: B*x & B*x <: A;           by -TmInS1S1;            // ! TmInS1S1 := A[x:elg, A,B:P[elg], A*inv(x) <: B == A <: B*x];
F3 := A*inv(x) <: B & B*x <: A;      by TmInS1S;              // ! TmInS1S := A[x:elg, A,B:P[elg], A*x <: B == A <: B*inv(x)];
F4 := A*inv(x) <: B & B <: A*inv(x); by -Axext;
F5 := A*inv(x) = B;                                           // ! TminS2 := A[a,x:elg, B:P[elg], x*a in B == a in inv(x)*B];
 end EqProof TeqSmr1;                                         // ! TminS1 := A[a,x:elg, B:P[elg], a*x in B == a in B*inv(x)];

! TeqSmr2  := A[x:elg, A,B:P[elg], inv(x)*B = A == x*A = B];  
 EqProof -TeqSmr2;                                            
F0 := x in elg;                      assume;
F01 := A in P[elg];                  assume;
F02 := B in P[elg];                  assume;
F1 := x*A = B;                       by Axext;                // ! Axext := X = Y == X <: Y & Y <: X;  
F2 := x*A <: B & B <: x*A;           by TmInS2S;              // ! TmInS2S := A[x:elg, A,B:P[elg], x*A <: B == A <: inv(x)*B];
F3 := A <: inv(x)*B & B <: x*A;      by -TmInS2S1;            //  ! TmInS2S1 := A[x:elg, A,B:P[elg], inv(x)*A <: B == A <: x*B];
F4 := A <: inv(x)*B & inv(x)*B <: A; by -Axext;
F5 := A = inv(x)*B;                  by Axsym;
F6 := inv(x)*B = A;
 end EqProof -TeqSmr2;

! TeqSmr2a := A[x,y:elg, A: P[elg], x*A = y*A == A = inv(x)*y*A];  byeq -TeqSmr2, Axsym, Associnve;  // take B = y*A;

! TeqSmr3  := A[x:elg, H:P[elg], inv(x)*H*x = H == x*H = H*x];
 Proof TeqSmr3;
F0 := x in elg;                      assume;  
F01 := H in P[elg];                  assume;
F1 := inv(x)*(H*x) = (inv(x)*H)*x;   is AssoceSe;             // ! AssoceSe := A[a:elg, B:P[elg], c:elg, a*(B*c) = (a*B)*c];
F2 := inv(x)*(H*x) = H == x*H = H*x; is TeqSmr2; by F1;       // is TeqSmr2(x,H,H*x);
F3 := inv(x)*H*x = H == x*H = H*x;
 end Proof TeqSmr3;

// ! TinvSml  := A[a:elg, x:elg, B:P[elg], a in x*B == inv(a)*x in B]; // same as -TminS2a:= A[a,x:elg,B:P[elg],inv(x)*a in B == a in x*B]; 
// ! Tinmr    := A[a:elg,x:elg, B:P[elg], a in B*x == a*inv(x) in B];  // same as -TminS1a := A[a,x:elg, B:P[elg], a*inv(x) in B == a in B*x; 
// ! TInm1  := A[x:elg, A,B: P[elg], A*x <: B == A <: B*inv(x)];       // same as ! TmInS1S := A[x:elg, A,B:P[elg], A*x <: B == A <: B*inv(x)]; 
// ! TInlm2  := A[x:elg, A,B: P[elg], x*A <: B == A <: inv(x)*B];      // same as ! TmInS2S := A[x:elg, A,B:P[elg], x*A <: B == A <: inv(x)*B];
// ! TInm3  := A[x:elg, A,B: P[elg], A <: B*x == A*inv(x) <: B];       // same as -TmInS1S1 := A[x:elg, A,B:P[elg], A*inv(x) <: B == A <: B*x];
// ! TInm4  := A[x:elg, A,B: P[elg], A <: x*B == inv(x)*A <: B];       // same as -TmInS2S1 := A[x:elg, A,B:P[elg], inv(x)*A <: B == A <: x*B];

! TmmR     := A[a:elg, B:P[elg], c:elg, a*B*c = R[b:B, a*b*c] ];
 EqProof TmmR;
F0 := a in elg;                      assume;
F01 := B in P[elg];                  assume;
F02 := c in elg;                     assume;
F1 := a*B*c;                         by TmSe;                          // ! TmSe := A[A:P[elg], b:elg, A * b = R[a:A, a*b]]
F2 := R[x: a*B, x*c];                by TmeS;                          // ! TmeS := A[a:elg, B:P[elg], a * B = R[b:B, a*b]];
F3 := R[x: R[b:B, a*b], x*c];        by TRR;                           // ! TRR  := R[x:R[d,f], G(x)] = R[d, G(f)];
F4 := R[b:B, a*b*c];
 end EqProof TmmR;

! LInmmA := A[a:elg, B: P[elg], c:elg, D: P[elg], a*B*c <: D == A[b:B, a*b*c in D]]; byeq TmmR, TRA; // ! TRA  := R[d, f] <: B == A[d, f in B];  

! Lminv   := A[a:elg, B:P[elg], a*B*inv(a) <: B] -> A[a:elg, B:P[elg], a*B*inv(a) = B];
 Proof Lminv;
F0 := A[a:elg, B:P[elg], (a*B)*inv(a) <: B]; assume; 
F01 := a in elg;                             assume;
F02 := B in P[elg];                          assume;
F03 := inv(a)*B*inv(inv(a)) <: B;            is F0; by Tinvinv;
F04 := inv(a)*B*a <: B;                      by TmeSinvIn;  // ! TmeSinvIn := A[x:elg, A:P[elg], B:P[elg], inv(x)*A*x <: B == A <: x*B*inv(x)];
F05 := B <: a*B*inv(a);                      
F1 := a*B*inv(a) = B;                        by Axext; F2 & F05;        // ! Axext := X = Y == X <: Y & Y <: X; 
F2 := a*B*inv(a) <: B;                       is F0;
 end Proof Lminv; 

! TmSSIn := A[A,B: P[elg], A*B <: elg];      is typeaxiom;  // type(A*B) = P[elg]; // !! AxP := Z in P[Y] == Z <: Y;                         
                                             
! TinvSm := A[A,B: P[elg], invS(A*B) = invS(B)*invS(A)];
 EqProof TinvSm;
F0 := A in P[elg];                          assume;
F01 := B in P[elg];                         assume;
F1 := invS(A*B);                            by TinvS;     // ! TinvS := A:P[elg], invS(A) = R[a:A, inv(a)]];
F2 := R[x:A*B, inv(x)];                     by TmSSR;     // ! TmSSR := A[A:P[elg], B:P[elg], A * B = R[a:A,b:B, a*b]];
F3 := R[x:R[a:A,b:B, a*b],inv(x)];          by TRR;       // ! TRR  := R[x:R[d,f], G(x)] = R[d, G(f)];
F4 := R[a:A,b:B, inv(a*b)];                 by Tinvmlt;   // ! Tinvmlt := A[x,y:elg, inv(x*y) = inv(y) * inv(x)];
F5 := R[a:A,b:B, inv(b)*inv(a)];            by TR2;       // ! TR2 := R[a:A,b:B, F(a,b)] = R[b:B,a:A, F(a,b)];
F6 := R[b:B,a:A, inv(b)*inv(a)];            by -TmRR;     // ! TmRR := A[A,B: P[elg], R[a:A,W_elg(a)] * R[b:B,W_elg1(b)] = R[a:A,b:B, W_elg(a) * W_elg1(b)]]; 
F7 := R[b:B,inv(b)] * R[a:A,inv(a)];        by -TinvS;
F8 := invS(B) * invS(A);
 end EqProof TinvSm;


];  // group :: [ end 4. Macrooperations //////////////////////////////////
 
/////////////////////////////////// 5.   Closed  subsets ////////////////////////////////
group :: [
var S, P[elg];
dcl[closedmlt,fn(P[elg],bool)];
// closedmlt := F[S:P[elg], A[x,y: S, x*y in S]];
// ! closedmlt_type := closedmlt in fn(P[elg], bool);       is typeaxiom;
dcl[closedinv,fn(P[elg],bool)];
dcl[closed,fn(P[elg],bool)];
// closedmlt := F[S:P[elg], A[x,y: S, x*y in S]];
// ! Tclosedmlt_t := closedmlt in fn(P[elg], bool);       is typeaxiom;
// closedinv := F[S:P[elg], A[x: S, inv(x) in S]];
// ! Tclosedinv_t := closedinv in fn(P[elg], bool);       is typeaxiom;
// closed := F[S:P[elg], closedmlt(S) & closedinv(S)];
// ! Tclosedl_type := closed in fn(P[elg], bool);            is typeaxiom;

// dcl[closedinv,fn(P[elg],bool)];
// dcl[closed,fn(P[elg],bool)];
! L07 := S in P[elg];                                    is typeaxiom; by AxP;
! L02 := S <: elg;
! TclosedP := A in P[elg] & B in P[elg] -> A /\ B in P[elg];  is TPinI; // TPinI := A in P[X] & B in P[X] -> A/\B in P[X];
// !! Axclosedmlt := closedmlt(S) == A[x,y: S, x*y in S];
// !! Axclosedinv := closedinv(S) == A[x: S, inv(x) in S];
// !! Axclosed := closed(S) == closedmlt(S) & closedinv(S); // A[x,y: S, x*y in S];
!! Axclosedmlt := A[S:P[elg], closedmlt(S) == A[x,y: S, x*y in S]];  // byeq Red;   // F[d,G]

! TclosedmltI := A[A,B:P[elg], closedmlt(A) & closedmlt(B) -> closedmlt(A/\B)];
 Proof TclosedmltI;
F0 := A in P[elg];                assume;
F01 := B in P[elg];               assume;
F02 := closedmlt(A);              assume; by Axclosedmlt(A);
F02a := A[x,y: A, x*y in A];
F03 := closedmlt(B);              assume; by Axclosedmlt(B);
F03a := A[x,y: B, x*y in B];
F04 := A/\B <: elg;               is TinPIIn(F0 & F01);  //  ! TinPIIn := X in P[Z] & Y in P[Z] -> X/\Y <: Z;
Goal := closedmlt(A/\B);          by Axclosedmlt(A/\B);
G1 := A[x,y: A/\B, x*y in A/\B];
  Proof G1;                       // !! AxI := a in X1/\Y1 == a in X1 & a in Y1;
G0 := x in A/\B;                  assume; by AxI; G0a & G0b;
G0a := x in A;
G0b := x in B;
G01 := y in A/\B;                 assume; by AxI; G01a & G01b;
G01a := y in A;
G01b := y in B;
G2 := x*y in A;                   is F02a(x,y);
G3 := x*y in B;                   is F03a(x,y);
Goal1 := x*y in A/\B;             by AxI; G2 & G3;
  end Proof G1;
 end Proof TclosedmltI;

! Tclosedmlt1 := A[A:P[elg], closedmlt(A) == A*A <: A];
 EqProof -Tclosedmlt1;
F0 := A in P[elg];               assume;
F1 := A*A <: A;                  by TmSSR;              // ! TmSSR := A[A:P[elg], B:P[elg], A * B = R[a:A,b:B, a*b]];
F2 := R[a:A,b:A, a*b] <: A;      by TRA;                // ! TRA  := R[d, f] <: B == A[d, f in B];
F3 := A[a:A,b:A, a*b in A];      by -Axclosedmlt;       // !! Axclosedmlt := A[S:P[elg], closedmlt(S) == A[x,y: S, x*y in S]];
F4 := closedmlt(A);                                     // a:A,b:A will be replaced with {a,b: a in A, b in A};
 end EqProof -Tclosedmlt1;

!! Axclosedinv := A[S:P[elg], closedinv(S) == A[x: S, inv(x) in S]];

! TclosedinvI := A[A,B:P[elg], closedinv(A) & closedinv(B) -> closedinv(A/\B)];
 Proof TclosedinvI;
F0 := A in P[elg];                assume;
F01 := B in P[elg];               assume;
F02 := closedinv(A);              assume; by Axclosedinv(A);
F02a := A[x: A, inv(x) in A];
F03 := closedinv(B);              assume; by Axclosedinv(B);
F03a := A[x: B, inv(x) in B];
F04 := A/\B <: elg;               is TinPIIn(F0 & F01);  //  ! TinPIIn := X in P[Z] & Y in P[Z] -> X/\Y <: Z;
Goal := closedinv(A/\B);          by Axclosedinv(A/\B);
G1 := A[x: A/\B, inv(x) in A/\B];
  Proof G1;                       // !! AxI := a in X1/\Y1 == a in X1 & a in Y1;
G0 := x in A/\B;                  assume; by AxI; G0a & G0b;
G0a := x in A;
G0b := x in B;
G2 := inv(x) in A;                is F02a(x);
G3 := inv(x) in B;                is F03a(x);
Goal1 := inv(x) in A/\B;          by AxI; G2 & G3;
  end Proof G1;
 end Proof TclosedinvI;

! Tclosedinv1 := A[A:P[elg], closedinv(A) == invS(A) <: A];
 EqProof -Tclosedinv1;
F0 := A in P[elg];               assume;
F1 := invS(A) <: A;              by TinvS;              // ! TinvS := A:P[elg], invS(A) = R[a:A, inv(a)]];
F2 := R[a:A, inv(a)] <: A;       by TRA;                // ! TRA  := R[d, f] <: B == A[d, f in B];
F3 := A[a:A, inv(a) in A];       by -Axclosedinv;       // !! Axclosedinv := A[S:P[elg], closedinv(S) == A[x: S, inv(x) in S]];
F4 := closedinv(A);                                     
 end EqProof -Tclosedinv1;        // !! AxAimp := A[x:X, Q(x)] == All(x, x in X -> Q(x));
                                  // !! Axclosedmlt := A[S:P[elg], closedmlt(S) == A[x,y: S, x*y in S]];
!! Axclosed0 := All(S, S in P[elg] -> (closed(S) == closedmlt(S) & closedinv(S))); by -AxAimp;
! Axclosed := A[S:P[elg], closed(S) == closedmlt(S) & closedinv(S)]; by Axclosedmlt(S@Axclosed), Axclosedinv(S@Axclosed);
! Tclosed := A[S:P[elg], closed(S) == A[x,y:S, x*y in S] & A[x:S, inv(x) in S] ];  by AxAimp;
! Tclosed0 := All(S, S in P[elg] -> (closed(S) ==  A[x,y:S, x*y in S] & A[x:S, inv(x) in S] ));  // !! AxP := Z in P[Y] == Z <: Y;                         
! L03 := {e} in P[elg];           by AxP,TSIn; Axe; L03; by AxP; // TSIn := {a} <: X1 == a in X1; // Axe := e in elg
! L03a := {e} <: elg;  
! LSeNemp := {e} ~= {};           is TSneqemp;                   // ! TSneqemp := {a} ~= {};  
! LSeinP1 := {e} in P1[elg];      by AxP1; L03a & LSeNemp;       // !! AxP1 := S in P1[Y] == S <: Y & S ~= {};
// ! L04 := elg in P[elg];        is TPin1;                      // TPin1 := X in P[X]; // sse  ! L01 := elg in P[elg]; is TPin1;

// !! TAemp1 := A[x:{}, P(x)];
// !! TAemp2 := A[x,y:{}, P(x,y)]; 
// !! TAemp1a := A[x:{}, P(x)] == true;                             // moved to root !!!
// !! TAemp2a := A[x,y:{}, P(x,y)] == true; 
! Tclosed_emp := closed({});      by Tclosed({}),TAemp2a,TAemp1a;                 is Taut;  // true & true;
! Tclosed_e := closed({e});       by Tclosed({e}),TAS2a,Teee,TinS,TAS,Tinve,TinS; is Taut;  // true & true; // TinS := a in {a}; 
! Tclosed_elg := closed(elg);     by Tclosed(elg);                                is LCL2 & LCL1;

! TclosedI := A[A,B: P[elg], closed(A) & closed(B) -> closed(A /\ B)];	
 Proof TclosedI;
F0 := A in P[elg];             assume;
F01 := B in P[elg];            assume;
F1 := closed(A);               assume; by Axclosed(A); F1a & F1b;
F2 := closed(B);               assume; by Axclosed(B); F2a & F2b;
F1a := closedmlt(A);
F1b := closedinv(A);
F2a := closedmlt(B);
F2b := closedinv(B);          // ! TclosedmltI := A[A,B:P[elg], closedmlt(A) & closedmlt(B) -> closedmlt(A/\B)];
F3 := closedmlt(A/\B);        is TclosedmltI(A,B)(F1a & F2a);
F4 := closedinv(A/\B);        is TclosedinvI(A,B)(F1b & F2b);
Goal := closed(A/\B);         by Axclosed(A/\B); F3 & F4;
 end Proof TclosedI;
                              // group :: ! Tclosed := A[S:P[elg], closed(S) == A[x,y: S, x*y in S] & A[x: S, inv(x) in S] ];
!TP1elgNemp := P1[elg]~={};   is TP1Nemp(TelgNemp);  // ! TP1Nemp := X ~= {} -> P1[X] ~= {}; // ! TelgNemp := elg ~= {};    
! P1[P1[elg]] ~= {};          is TP1Nemp(TP1elgNemp);
                              // !! Axclosed0 := All(S, S in P[elg] -> (closed(S) == closedmlt(S) & closedinv(S)));
var V, P[elg];                // ! Tclosed := A[S:P[elg], closed(S) == A[x,y:S, x*y in S] & A[x:S, inv(x) in S] ];        
! AxV := V in P[elg];         is typeaxiom; // ! Tclosed0 := All(S,S in P[elg]->(closed(S)==A[x,y:S,x*y in S] & A[x:S,inv(x) in S]));

///////////////////   6. Subgroups: the definition  //////////////////////////////////////// 2: closed(H) is in subgr !!! AFTER !!!
subgr := {H; AxHt := H in P1[elg], AxclosedH := closed(H) };     // a subgroup is a set, not a group 
! Tsubgr := subgr = {H; H in P1[elg], closed(H) };           is Axrefl;  // AxP1 := S in P1[Y] == S <: Y & S ~= {};
! Tsubgrin := X in subgr == X in P1[elg] & closed(X);        is Axab; by AxP1;
! Tsubgrin0b := X in subgr == X <: elg & X ~= {} & closed(X); 
! Tsubgrin0 := V in subgr == V in P1[elg] & closed(V);       is Axab; by Tclosed,2, Taut(p1&(p2&p3)== p1&p2&p3); 
// ! Tsubgrin0A := A[V:P[elg], V in subgr == V in P1[elg] & closed(V)]; is Tsubgrin0;  // not used; 
! Tsubgrin0a := V in subgr == V in P1[elg] & A[x,y: V, x*y in V] & A[x: V, inv(x) in V]; by AxP1,2; // 2: H in P1[elg] is in subgr !!! 
! Tsubgrin1 := V in subgr == V <: elg & V ~= {} & A[x,y: V, x*y in V] & A[x: V, inv(x) in V]; // error in hnby ???
! Tsubgrin1A := A[V:P[elg], V in subgr == V <: elg & V ~= {} & A[x,y: V, x*y in V] & A[x: V, inv(x) in V]]; is Tsubgrin1;
! Tsubgrin2 := V in P1[elg] -> (V in subgr == closed(V));   is Taut8(Tsubgrin0);  // ! Taut8 := (p == q&r) -> (q -> (p==r)); 
//                                                          was: is Taut((p==q&r) -> (q->(p==r)))(Tsubgrin0); ERROR !!!   
// ! Tsubgr1 := subgr = {H; H <: elg, H ~= {}, A[x,y: H, x*y in H], A[x: H, inv(x) in H] };  by AxextA,Tsubgrin1,Axab; is Taut;
! Tsubgr2 := X in subgr -> X <: elg;   is Taut29a(Tsubgrin0b);           // ! Taut29a := (p == q&q1&q2) -> (p->q);   
! Tsubgr3 := subgr <: P1[elg];         is TInab5a; by -AxP;              // ! TInab5a := {x; x in t; Q} <: t; 
! Tsubgr4 := subgr in P[P1[elg]];      // !! AxP := Z in P[Y] == Z <: Y; // ! TelginP1 := elg in P1[elg];
! Telg := elg in subgr;                by Axab; TelginP1 & Tclosed_elg;  // ! Tclosed_elg := closed(elg); 
! TSe  := {e} in subgr;                by Axab; LSeinP1 & Tclosed_e;     // ! LSeinP1 := {e} in P1[elg];  // ! Tclosed_e := closed({e});
! TSeelg := {{e}, elg} <: subgr;       by Tcoll2In; TSe & Telg;          // ! Tcoll2In := {a,b} <: Z == a in Z & b in Z;
! Tsubgr6 := subgr ~= {};              is Tinnemp(Telg);                 // ! Tinnemp := x in X -> X ~= {};
! Tsubgr_type := subgr in P1[P1[elg]]; by AxP1; Tsubgr3 & Tsubgr6;       // !! AxP1 := S in P1[Y] == S <: Y & S ~= {};
! TP1InPelg := P1[elg] <: P[elg];      is TP1inP;                        // ! TP1inP := P1[Y] <: P[Y];
! Tsubgr3b := subgr <: P[elg];         is TInIn(Tsubgr3 & TP1InPelg);    // ! TInIn := X0 <: Y0 & Y0 <: Z0 -> X0 <: Z0; 

! Tsubgrin1t := A[V:P[elg], V in subgr == V in P1[elg] & A[x,y: V, x*inv(y) in V]];
 Proof Tsubgrin1t;
F0 := V in P[elg];                    assume; 
G01 := V in subgr == V in P1[elg] & A[x,y: V, x*inv(y) in V];  by Deqv; L1 & L2;
L1 := V in subgr -> V in P1[elg] & A[x,y: V, x*inv(y) in V];
  Proof L1;
F0 := V in subgr;                      assume; by Tsubgrin0a; F01 & F02 & F03;
F01 := V in P1[elg];
F02 := A[x,y:V, x*y in V];
F03 := A[x:V, inv(x) in V];
G0 := G1 & G2;
G1 := V in P1[elg];                    is F01;
G2 := A[x,y:V, x*inv(y) in V];
   Proof G2;
K0 := x in V;                          assume;
K01 := y in V;                         assume; 
K1 := inv(y) in V;                     is F03;
K2 := x*inv(y) in V;                   is F02;
   end Proof G2;
  end Proof L1;

L2 := V in P1[elg] & A[x,y: V, x*inv(y) in V] -> V in subgr;
  Proof L2;
F0 := V in P1[elg];                    assume;
F01 := A[x,y: V, x*inv(y) in V];       assume;
F02 := V ~= {};                        is TP1nemp(F0);         // !! TP1nemp := x in P1[X] -> x~={};
z := arb(V);
F1 := z in V;                         is Axarb(F02);           // !! Axarb     := X ~= {} == arb(X) in X;
// F2 := z in elg;                    is TP1inin(F0 & F1);     // !! TP1inin := S in P1[Y] & x in S  -> x in Y; 
F2 := z * inv(z) in V;                is F01(z,z);  by Axrinv; // Axrinv := A[x: elg, x * inv(x) = e])
F3 := e in V;
G0 := V in subgr;                      by Tsubgrin0a; F0 & G2 & G1;
G1 := A[x:V, inv(x) in V];
  Proof G1;
K0 := x in V;                          assume;
K01 := x in elg;                       is TP1inin(F0 & K0);   // !! TP1inin := S in P1[Y] & x in S  -> x in Y; 
K1 := e * inv(x) in V;                 is F01(e,x); by Tle;   // ! Tle := A[a:elg, e*a = a]; 
K2 := inv(x) in V;
  end Proof G1;
G2 := A[x,y:V, x*y in V];
   Proof G2;
K0 := x in V;                          assume;
K01 := y in V;                         assume; 
K1 := inv(y) in V;                     is G1;
K2 := x * inv(inv(y)) in V;            is F01;  by Tinvinv;   // ! Tinvinv := A[x:elg, inv(inv(x)) = x];
K3 := x*y in V;
   end Proof G2;
  end Proof L2;
 end Proof Tsubgrin1t;

! TsubgrinS0 := A[A:P1[elg], A in subgr == A*A <: A & invS(A) <: A];
 EqProof TsubgrinS0;
F0 := A in P1[elg];                    assume;            
F1 := A in subgr;                      by Tsubgrin2;                     // ! Tsubgrin2 := A in P1[elg] -> A in subgr == closed(A);  
F2 := closed(A);                       by Axclosed;       // !! Axclosed := A[S:P[elg], closed(S) == closedmlt(S) & closedinv(S)];
F3 := closedmlt(A) & closedinv(A);     by Tclosedmlt1, Tclosedinv1;      // ! Tclosedmlt1 := A[A:P[elg], closedmlt(A) == A*A <: A];
F4 := A*A <: A & invS(A) <: A;
 end EqProof TsubgrinS0;

// ! TsubgrinS := A[A:P1[elg], A in subgr == A*A = A & invS(A) = A];  see proof below, after TH3;

////////////////////          7. Subgroups: some  H-theorems  ////////////////////////////

subgr :: [   // 1.Subgroups: Basics     // subgr := {H; AxHt := H in P1[elg], AxclosedH := closed(H) };
var A_P1_elg, P1[elg]; var v_H, H;
! AxH := H in subgr;                    by Axab; AxHt & AxclosedH;
x_H := {x; x in H};                     // x_H is x:H;  
// g_elg := {g; g in elg};                 // g_elg is g:elg; moved up, to group;

////////////////////////// 7.1 Gr := [H, *_Gr := *(group)|(H#H)] is a group;  ////////////////////   group :: [   var a,b,c, elg; 

Gr := [H, *_Gr := *(group)|(H#H)];    // Gr is the group(see proof below), corresponding to the subgroup H (H is a set);
! AxGr := Gr = [H, *_Gr];   is Axrefl;  // used only in AxGrK;
AxHt; by AxP1; LHelg & LHnemp;          // !! AxP1 := S in P1[Y] == S <: Y & S ~= {}; // AxHt := H in P1[elg]
! LHelg := H <: elg;                    // was AxH1, LH2;
! LHnemp := H ~= {};                    by Axarb;                 // !! Axarb     := X ~= {} == arb(X) in X;
! LHarb := arb(H) in H;
! LHmnempl := a*H ~= {};                is TmeS1;                 // ! TmeS1 := A[a:elg, B:P1[elg], a*B ~= {};
! LHmnempr := H*a ~= {};                is TmSe1;                 // !! TmSe1 := A[A:P1[elg], b:elg, A*b ~= {}];
// GrH := Gr.H;                         // problems, see NH;
// group :: [   var a,b,c, elg;
! TGrm := A[x,y:H, x *_Gr y = x * y];   is Tre6(Axm & LHelg); // ! Tre6 := f in fn(A#A,A) & B <: A -> A[x,y:B, (f|(B#B))(x,y) = f(x,y)];
AxclosedH; by Tclosed(H); LHm & LHinv;  // ! Tclosed := A[S:P[elg], closed(S) == A[x,y: S, x*y in S] & A[x: S, inv(x) in S] ];
! LHm := A[x,y: H, x*y in H];            // !! Tre4 := f in fn(A#A,A) & B <: A -> (f|(B#B) in fn(B#B,B) == A[x,y:B, f(x,y) in B]);
! LHm1 := A[y: H, v_H*y in H];          is LHm;           
! LHinv := A[x_H, inv(x) in H];         // see above: AxclosedH; by Tclosed(H); LHm & LHinv; // ! TGrm := A[x,y:H, x *_Gr y = x * y];
! LHm_type := *_Gr in fn(H#H, H);       by Tre4(Axm & LHelg); LHm;   // Axm  := * in (typm:=fn(elg#elg, elg));  // ! LHelg := H <: elg;  
! LHmIn := *_Gr <: *(group);            is TreIn2@FN;    
                                       
! LHe := e in H;  
 Proof LHe;
x := arb(H);
F0 := x in H;                           is LHarb;          // ! LHarb := arb(H) in H;  
F1 := inv(x) in H;                      is LHinv;          // ! LHinv := A[x_H, inv(x) in H];
F2 := x * inv(x) in H;                  is LHm; by Axrinv; // ! LHm := A[x,y: H, x*y in H]; !! Axrinv := A[x: elg, x * inv(x) = e];       
LHe;                                     // F3 := e in H;  // error: no merging;
 end Proof LHe;

! LHinvm := A[x:elg, inv(x)*x in H];    by Tlinv, LHe;    is Taut;    // ! Tlinv := inv(a)*a = e;
                                                          
! LHdominv := H <: dom(inv);            by Linvdom; LHelg;  // ! Linvdom := dom(inv) = elg; // needed for checking Tredom(inv,H);

inv_Gr := inv|H;                        // Axinv  := inv in fn(elg,elg); // ! LHelg := H <: elg;  
!! Linv_Gr_type  := inv_Gr in fn(H, H);  // by Tre5(Axinv & LHelg); LHinv;   // ! Tre5 :- f in fn(A,A) & B<:A -> (f|B in fn(B,B) == A[x:B, f(x) in B]);  
// MfA := [inv,H];
// !! LMfA_type  := MfA in fA;
! Linv_Gr_dom := dom(inv_Gr) = H;       is Tredom(inv,H); // .MfA; (inv,H);  adt: was error;   // fA:: ! Tredom := dom(f|A) = A;
! LGrinv := A[x_H, inv_Gr(x) = inv(x)]; is Tre2(Axinv & LHelg);        // Axinv := inv in fn(elg,elg); // "nosimr"; LGrinv;
! LH0 := A[x_H, x *_Gr inv_Gr(x) = e];  by TGrm,LGrinv; is Axrinv;     // ! LGrinv := A[x_H, inv_Gr(x) = inv(x)];
! LGrtype1 := A[x_H, x *_Gr e = x];     by TGrm; is Axre; // ! TGrm := A[x,y:H, x *_Gr y = x * y]; // Axre   := A[x:elg, x * e = x]; 
! LGrtype2 := Exist(inv1, inv1 in fn(H,H) & A[x_H, x *_Gr inv1(x) = e]);  is Witness(inv_Gr);  // ! Linv_Gr_type := inv_Gr in fn(H, H); 
! LHAssoc:= A[x,y,z: H, x*(y*z) = (x*y)*z ];  is TInAA3(LHelg & AxAssoc);   // ! TInAA3 := A <: B & A[x1,x2,x3:B, P(x1,x2,x3)] -> A[x1,x2,x3:A, P(x1,x2,x3)]; 
! LHAssoc1:= A[x,y,z: H, x *_Gr( y*_Gr z) = (x *_Gr y) *_Gr z ]; by TGrm,TGrm,TGrm,TGrm; LHAssoc;  // ! TGHrm := A[x,y:H, x *_Gr y = x * y];
! LEe1inv1 :=  E[e1:H, inv1:fn(H,H),  A[x_H, x *_Gr e1 = x] & A[x_H, x *_Gr inv1(x) = e1]];  is Witness(e,inv_Gr);      
// ! LEinv1 :=  Exist(inv1, inv1 in fn(H,H) &          
//   A[x_H, x *_Gr inv1(x) = e]);        is Witness(inv_Gr); // see LHe := e in H, LGrtype1, LGrtype2;
! TGr_type := Gr in group;              by Axab; LHm_type & LHAssoc1 & LEe1inv1; // ! LHm := A[x,y: H, x*y in H];
! LGrelg := elg.Gr = H;                 byeq Red;   
! LGr1a := *(group).Gr = *_Gr;          byeq Red;                 // ! LHelg := H <: elg; // Axre := A[x_elg, x * e = x];
! LGrm := A[x:H,y:H, x *(group).Gr y = x*y];  by LGr1a; TGrm;     // ! TGrm := A[x,y:H, x *_Gr y = x * y];
///                               7.2 Eliminating dotted Gr-names         

! LGre := e.Gr = e; 
 Proof LGre;
F0 := e.Gr in H;                       is Axe.Gr;                 // Axe := e in elg; 
F1 := A[x_H, x *(group).Gr e.Gr = x];  is Axre.Gr;  by LGrm;      // ! LGrm := A[x:H,y:H, x *(group).Gr y = x*y]; ???? no error ????
F2 := A[x_H, x * e.Gr = x];
F3 := e.Gr * e.Gr = e.Gr;              is F2(e.Gr);
F4 := e.Gr = e;                        is Laaa(F3);               // ! Laaa := a*a = a -> a = e; 
 end Proof LGre;

invGr := inv.Gr;                        // if (inv.Gr) used instead of invGr, then error in pars: F1 := A[x_H, x *(group).Gr invGr(x) = e.Gr]; 
! LinvGr_dom := dom(invGr) = H;         is Tinvdom.Gr;                 // ! Tinvdom := dom(inv) = elg;

! LHinvGr := A[x_H, invGr(x) = inv(x)];  // change notation !!! LHinvGr => LinvGr, LGrinv => Linv_Gr, LGrm => LmGr; 11.28.20
 Proof LHinvGr;                                                       // ! TGrm := A[x,y:H, x *_Gr y = x * y];
F1 := A[x_H, x *(group).Gr invGr(x) = e.Gr]; is Axrinv.Gr; by LGrm;   // ! LGrm := A[x:H,y:H, x *(group).Gr y = x*y];
F2 := A[x_H, x * invGr(x) = e.Gr];           by LGre, Teqer;          // ! LGre := e.Gr = e; ! Teqer := A[x,a:elg, a*x=e == x=inv(a)];
F3 := A[x_H, invGr(x) = inv(x)];                                      // was error: no merging;
 end Proof LHinvGr;
                                                                      // ! LGrinv := A[x_H, inv_Gr(x) = inv(x)]; 
! LHinvGr1 :=  A[x_H, invGr(x)=inv_Gr(x)];   byeq LHinvGr, -LGrinv;   // ! LHinvGr := A[x_H, invGr(x) = inv(x)];
                                                                      // invGr := inv.Gr; inv_Gr := inv|H;  
! LH3a := invGr = inv_Gr;               //  ! Tfneq := A[f,g:FN, f=g == dom(f)=dom(g) & A[x:dom(f), f(x)=g(x)];
 Proof LH3a;                            by Tfneq; L1 & L2; // !! Axrefl := x = x; // ! Linv_Gr_dom := dom(inv_Gr) = H;
L1 := dom(invGr) = dom(inv_Gr);         byeq LinvGr_dom, -Linv_Gr_dom; // ! LinvGr_dom := dom(invGr) = H;  
L2 := A[x:dom(invGr), invGr(x)=inv_Gr(x)]; by LinvGr_dom;  LHinvGr1;
 end Proof LH3a;

! TclosedGr := A[S:P[H], closed.Gr(S) == closed(S)];   // invGr := inv.Gr; // ! LHinvGr := A[x_H, invGr(x) = inv(x)];
 EqProof TclosedGr;               // ! Tclosed := A[S:P[elg], closed(S) == A[x,y:S, x*y in S] & A[x: S, inv(x) in S]];
F0 := S in P[H];                                                assume;
F1 := closed.Gr(S);                                             by Tclosed.Gr;
F2 := A[x,y:S, x *(group).Gr y in S] & A[x:S, invGr(x) in S];   by LGrm, LHinvGr;   
F3 := A[x,y:S, x * y in S] & A[x:S, inv(x) in S];               by -Tclosed; 
F4 := closed(S);
 end EqProof TclosedGr;

! LsubgrGr := subgr.Gr <: subgr;
 Proof LsubgrGr;                        by TInA;            // !! TInA := A <: B == A[x:A, x in B]; ;
G0 := A[X: subgr.Gr, X in subgr];
  Proof G0;
F0 := P1[H] <: P1[elg];                 is TP1m(LHelg);     //  !! TP1m := X <: Y -> P1[X] <: P1[Y]; // LHelg := H <: elg;
F01 := X in subgr.Gr;                   assume; by Axab; F1 & F3;
F1 := X in P1[H];
F2 := X in P1[elg];                     is TinIn(F1 & F0);  // ! TinIn := x in X2 & X2 <: Y2 -> x in Y2;
F3 := closed.Gr(X);                     by TclosedGr;       // ! TclosedGr := A[S:P[H], (closed.Gr)(S) == closed(S)];
F4 := closed(X);
G1 := X in subgr;                       by Axab; F2 & F4;   // subgr := {H; AxHt := H in P1[elg], AxclosedH := closed(H) }; 
  end Proof G0;
 end Proof LsubgrGr;

! LHmSe := A[a:H,B:P[H], B *(mSe).Gr a = B*a];
 EqProof LHmSe;
F0 := a in H;                           assume;
F01 := B in P[H];                       assume;
F02 := A[B:P[H],a:H, B *(mSe).Gr a = R[b:B, b *(group).Gr a]]; is TmSe.Gr;  // ! TmSe := A[A:P[elg], b:elg, A * b = R[a:A, a*b]];
F1 := B *(mSe).Gr a;                    by F02;
F2 := R[b:B, b*(group).Gr a];           by LGrm;                            // ! LGrm := A[x:H,y:H, x *(group).Gr y = x*y];
F3 := R[b:B, b * a];                    by -TmSe;
F4 := B*a;
 end EqProof LHmSe;

! LHmeS := A[a:H,B:P[H],  a*(meS).Gr B = a*B];
 EqProof LHmeS;
F0 := a in H;                           assume;
F01 := B in P[H];                       assume;
F02 := A[a:H,B:P[H], a *(meS).Gr B = R[b:B, a *(group).Gr b]]; is TmeS.Gr;  // ! TmeS := A[a:elg, B:P[elg], a * B = R[b:B, a*b]];
F1 := a *(meS).Gr B;                    by F02;
F2 := R[b:B, a*(group).Gr b];           by LGrm;                         // ! LGrm := A[x:H,y:H, x *(group).Gr y = x*y];
F3 := R[b:B, a * b];                    by -TmeS;
F4 := a*B;
 end EqProof LHmeS;

! LHmSS := A[A:P[H],B:P[H],  A*(mSS).Gr B = A*B];
 EqProof LHmSS;
F0 := A in P[H];                        assume;
F01 := B in P[H];                       assume;                           // ! TmSSR := A[A:P[elg], B:P[elg], A * B = R[a:A,b:B, a*b]];
F02 := A[A:P[H], B:P[H], A *(mSS).Gr B = R[a:A,b:B, a *(group).Gr b]];    is TmSSR.Gr;
F1 := A*(mSS).Gr B;                     by F02;
F2 := R[a:A,b:B, a *(group).Gr b];      by LGrm;
F3 := R[a:A,b:B, a * b];                by -TmSSR;
F4 := A*B;
 end EqProof LHmSS;
                                                                          // !! AxmSS := * @ mSS = F[A:P[elg], B:P[elg], U[a:A, a*B]]; 
! THmSS := *(mSS).Gr = *(mSS)|(P[H]#P[H]);                                // ! TmSSt := * @ mSS in fn(P[elg] # P[elg], P[elg]); 
 EqProof THmSS;                  // !! TFre2 := B1<:A1 & B2<:A2-> F[x:A1,y:A2, G(x,y)] | (B1#B2) = F[x:B1, y:B2, G(x,y)];
F0 := P[H] <: P[elg];                           is TPm(LHelg);  // ! TPm := X1 <: Y1 == P[X1] <: P[Y1];  // ! LHelg := H <: elg; 
F01 := *(mSS)|(P[H]#P[H]) = F[A:P[H], B:P[H], U[a:A, a * B]]; by AxmSS;  is TFre2(F0 & F0);
// F02 := F[A:P[elg], B:P[elg], U[a:A, a*B]] | (P[H]#P[H]) = F[A:P[H], B:P[H], U[a:A, a * B]]; is TFre2(F0 & F0);                 // 2022.11.15
F1 := *(mSS).Gr;                                by AxmSS,Red("dot"); // !! AxmSS := * @ mSS = F[A:P[elg], B:P[elg], U[a:A, a*B]]; // added "dpt"
F2 := F[A:P[H], B:P[H], U[a:A, a *(meS).Gr B]]; by LHmeS;     // ! LHmeS := A[a:H,B:P[H],  a*(meS).Gr B = a*B];
F3 := F[A:P[H], B:P[H], U[a:A, a * B]];         by -F01;
F4 := *(mSS)|(P[H]#P[H]);
 end EqProof THmSS;

! LH2r0 := A[x_H, H *(mSe).Gr x = H];   is Telgm2.Gr; by LHmSe;     // ! Telgm2 := A[a:elg, elg*a = elg]; // *@mSe.Gr
! LH2r := A[x_H, H*x = H];
! LH2l0 := A[x_H, x *(meS).Gr H = H];   is Telgm1.Gr; by LHmeS;     // ! Telgm1 := A[a:elg, a*elg = elg];
! LH2l := A[x_H, x*H = H];  
! LH1r := A[x_H, x in H*x];             by LH2r; is true;
! LH3 := im(invGr) = H;                 is Tinvsurj.Gr;    // ! Tinvsurj := im(inv) = elg; // invGr := inv.Gr;

! LHinv1 := A[x_H, invGr(x) in H];      is LCL1.Gr; // by LHinvGr;         // ! LCL1  := A[x:elg, inv(x) in elg];
! TGr_H := Gr.H = Gr;                   byeq Red;                    // Gr := [H, *_Gr := *(group)|(H#H)];  
! LH5a := im(*(group).Gr) = H;          is Tmsurj.Gr; by LGr1a;  // ! Tmsurj := im(*(group)) = elg;
! LH5 := im(*_Gr) = H;                                           // ! LGr1a := *(group).Gr = *_Gr;
! LH6a := H *(mSS).Gr H = H;            is Telgm.Gr; by LHmSS;   // ! LHmSS := A[A:P[H],B:P[H],  A*(mSS).Gr B = A*B];
! LH6 := H * H = H;                     
! LH2l1 := A[x_H, (x*H)*H = H];         byeq LH2l, LH6;             // ! LH6 := H * H = H; 
!      A[A: P1[H], A *(mSS).Gr H = H];  is Telgm1S.Gr; by LHmSS; // ! LHmSS := A[A:P[H],B:P[H],  A*(mSS).Gr B = A*B];
! Tsbgm2 := A[A: P1[H], A*H = H];                    // ! Telgm1S := A[A:P1[elg], A * elg = elg]; // error, if A *(mSS) H
!      A[A: P1[H], H *(mSS).Gr A = H];  is Telgm2S.Gr; by LHmSS; // ! Telgm2S := A[A:P1[elg], elg * A = elg];
! Tsbgm2a := A[A: P1[H], H*A = H];
! LPHelg := P[H] <: P[elg];             is TPm(LHelg);         // TPm := X1 <: Y1 == P[X1] <: P[Y1];  // LPHelg: was L01;
!      A[A,B:P[H], A *(mSS).Gr B <: H]; is TmSSIn.Gr; by LHmSS;     // TmSSIn := A[A,B:P[elg], A*B <: elg];
! Tsbgm3 := A[A,B: P[H], A*B <: H];

! LH9 := A[x:elg, h:H, (x*h)*H = x*H];  
 EqProof LH9;
F0 := x in elg;                         assume;
F01 := h in H;                          assume;
F1 := (x*h)*H;                          by Associnve;
F2 := x*(h*H);                          by LH2l;               // ! LH2l := A[x_H, x*H = H]; 
F3 := x*H;
 end EqProof LH9;

///////////////////////////             7.3 Some other H-theorems

! LamHelg1 := A[g_elg, g * H <: elg];   is typeaxiom;
! LamHelg2 := A[g_elg, H * g <: elg];   is typeaxiom;

! LHre   := A[x_H, x * e = x];        is TAIn1(LHelg & Axre);      // ! TAIn1 := A <: B & A[x:B, P(x)] -> A[x:A, P(x)]; 
! LHrinv := A[x_H, x * inv(x) = e];   is TAIn1(LHelg & Axrinv);    // !! Axrinv := A[x: elg, x * inv(x) = e] 

! LHinv2 := A[x,y: H, x*y*inv(x) in H]; // is TAIn2(LHelg & LCL3);  // ! TAIn2 := A <: B & A[x,y:B, P(x,y)] -> A[x,y:A, P(x,y)]; 
 Proof LHinv2;
F0 := x in H;                          assume;
F01 := y in H;                         assume;
F1 := inv(x) in H;                     is LHinv;                  // ! LHinv := A[x_H, inv(x) in H];
F2 := x*y in H;                        is LHm;                    // ! LHm := A[x,y: H, x*y in H]; 
F3 := x*y*inv(x) in H;                 is LHm;                    // same as LHm(x*y,inv(x));
 end Proof LHinv2;

! LHinv3 := a in H == inv(a) in H;  
 Proof LHinv3;                        by Deqv; L1 & L2;
L1 := a in H -> inv(a) in H; 
  Proof L1;
F0 := a in H;                         assume;
F1 := inv(a) in H;                    is LHinv;                   //  subgr :: LHinv := A[x:H, inv(x) in H]; 
  end Proof L1;
L2 := inv(a) in H -> a in H;
  Proof L2;
F0 := inv(a) in H;                    assume;
F1 := inv(inv(a)) in H;               is LHinv; by Tinvinv;       // ! LHinv := A[x_H, inv(x) in H];
F2 := a in H;
  end Proof L2;
 end Proof LHinv3;

! LHinv4 := A[x,y: H, x*inv(y) in H];  // Tactic: Closedness;
 Proof LHinv4;
F0 := x in H;                          assume;
F01 := y in H;                         assume;
F1 := inv(y) in H;                     is LHinv;  // ! LHinv := A[x_H, inv(x) in H]; 
F2 := x*inv(y) in H;                   is LHm;    // ! LHm := A[x,y: H, x*y in H];   
 end Proof LHinv4;

! LHinsubgr := H in subgr;             by Axab; AxHt & AxclosedH; //  subgr := {H; AxHt := H in P1[elg], AxclosedH := closed(H) };
// Gr4 := [H, *_Gr, e, inv_Gr];
// ! TGr4 := Gr4 in group4;                // by Def; &(LHnemp, LHe, LHm, LHinv, LHre, LHrinv, LHAssoc);

// ! LHsubgr := H in subgr.Gr;         // moved after ntsbg := H ~= {e} & H ~= elg; because of an error (see below)

! LH4 := invS(H) = H;
 EqProof LH4;
F1 := invS(H);                          by TinvS;        // ! TinvS := A[A:P[elg], invS(A) = R[a:A, inv(a)]]; 
F2 := R[x_H, inv(x)];                   by -TimF;        // ! TimF   := im(F[d, g]) = R[d, g];  // fA := {f, A; f in FN, AxfA1 := A <: dom(f)};  
F3 := im(F[x_H, inv(x)]);               by -TreF(inv,H); // fA :: ! TreF  := f|A = F[x:A, f(x)]; 
F4 := im(inv_Gr);                       by -LH3a, LH3;
F5 := H;
 end EqProof LH4;

! LH7l := A[g_elg, g*H = H == g in H];
 Proof LH7l;
F0 := g in elg;                         assume;
G0 := g*H = H == g in H;                by Deqv;   L1 & L2;
L1 := g*H = H -> g in H;
  Proof L1;
F0 := g*H = H;                          assume;                   // ! TmeS := A[a:elg, B:P[elg], a * B = R[b:B, a*b]];
F1 := g*H <: H;                         is Axext1(F0);  by TmeS;  // ! Axext1 := X=Y -> X<:Y; 
F2 := R[x:H, g*x] <: H;                 by TRA;                   // ! TRA  := R[d, f] <: B == A[d, f in B];                 
F3 := A[x:H, g*x in H];
F4 := g*e in H;                         is F3(e); by Axre;
F5 := g in H;
  end Proof L1;
L2 := g in H ->  g*H = H;
  Proof L2;
F0 := g in H;                           assume;                   // ! LHmeS := A[a:H,B:P[H],  a*(meS).Gr B = a*B];
F1 := A[a:H, a *(meS).Gr H = H];        is Telgm1.Gr; by LHmeS;   // ! Telgm1 := A[a:elg, a*elg = elg];
F2 := A[a:H, a * H = H];
F3 := g*H = H;                          is F2(g);
  end Proof L2;
 end Proof LH7l;
                                                   // ! TeqSmr2  := A[x:elg, A,B:P[elg], inv(x)*B = A == x*A = B];
! LH7 := A[x,y:elg, x*H = y*H == inv(x)*y in H];   // byeq -TeqSmr2, ...
 EqProof LH7;
F0 := x in elg;                         assume;  
F01 := y in elg;                        assume;
F1 := x*H = y*H;                        by -TeqSmr2;      // A = H, B = y*H;
F2 := inv(x)*(y*H) = H;                 by Associnve;     // better: use ! AssoceeS := A[a:elg, b:elg, C:P[elg], a*(b*C) = (a*b)*C];
F3 := (inv(x)*y)*H = H;                 by LH7l;          // ! LH7l := A[g_elg, g*H = H == g in H];
F4 := inv(x)*y in H;
 end EqProof LH7;

! LH7r := A[g_elg, H*g = H == g in H];
 Proof LH7r;
F0 := g in elg;                         assume;
G0 := H*g = H == g in H;                by Deqv;   L1 & L2;
L1 := H*g = H -> g in H;
  Proof L1;
F0 := H*g = H;                          assume;                   // ! TmSe := A[A:P[elg], b:elg, A * b = R[a:A, a*b]];
F1 := H*g <: H;                         is Axext1(F0);  by TmSe;  // ! Axext1 := X=Y -> X<:Y; 
F2 := R[x:H, x*g] <: H;                 by TRA;                   // ! TRA  := R[d, f] <: B == A[d, f in B];                 
F3 := A[x:H, x*g in H];
F4 := e*g in H;                         is F3(e); by Tle;         // ! Tle := e*a = a;
F5 := g in H;
  end Proof L1;
L2 := g in H ->  H*g = H;
  Proof L2;
F0 := g in H;                           assume;                   // ! LHmSe := A[a:H,B:P[H], B *(mSe).Gr a = B*a];
F1 := A[a:H, H *(mSe).Gr a = H];        is Telgm2.Gr; by LHmSe;   // ! Telgm2 := A[a:elg, elg*a = elg];
F2 := A[a:H, H*a = H];
F3 := H*g = H;                          is F2(g);
  end Proof L2;
 end Proof LH7r;

! LH8l := A[g_elg, g in g*H];
 Proof LH8l;
F0 := g in elg;                         assume;
F01 := g = g*e;                         is Axre1;
F1 := g in g*H;                         by TmeS;                  // ! TmeS := A[a:elg, B:P[elg], a * B = R[b:B, a*b]];
F2 := g in R[x_H, g*x];                 by TRin;                  // ! TRin := z in R[d,f] == E[d, z = f];
F3 := E[x_H, g = g*x];                  is Witness(e);
 end Proof LH8l;

! LH8r := A[g_elg, g in H*g];
 Proof LH8r;
F0 := g in elg;                         assume;
F01 := g = e*g;                         is Tle1;
F1 := g in H*g;                         by TmSe;                  // ! TmSe := A[A:P[elg], b:elg, A * b = R[a:A, a*b]];
F2 := g in R[x_H, x*g];                 by TRin;                  // ! TRin := z in R[d,f] == E[d, z = f];
F3 := E[x_H, g = x*g];                  is Witness(e);
 end Proof LH8r;

! LHAP := A[K:P[H], A[x:H, x*K in P[H]]];
 Proof LHAP;
F0 := K in P[H];                       assume;   by AxP;          // !! AxP := Z in P[Y] == Z <: Y;
F01 := K <: H;                                                    // ! LHm1 := A[y:H, v_H*y in H];  
F02 := x in H;                         assume;
G0 := x*K in P[H];                     by TmeS;                   // ! TmeS := A[a:elg, B:P[elg], a * B = R[b:B, a*b]];
G1 := R[k:K, x*k] in P[H];             by AxP;                    // !! AxP := Z in P[Y] == Z <: Y;
G2 := R[k:K, x*k] <: H;                by TRA;                    // !! TRA  := R[d, f] <: B == A[d, f in B]; 
G3 := A[k:K, x*k in H];                is TInAA(F01 & LHm1);      // !! TInAA := A <: B & A[x:B, P(x)] -> A[x:A, P(x)]; 
 end Proof LHAP; 

! L9r := A[g,g1: elg, g in H*g1 == g*inv(g1) in H];  is TminS1a1;  // ! TminS1a1 := A[a,x:elg, B:P[elg], a in B*x == a*inv(x) in B];

! L9r1 := A[g,g1: elg, g in H*g1 == g1*inv(g) in H];  // use L9r; g*inv(g1) in H == inv(g*inv(g1)) in H == g1*inv(g) in H;
 EqProof -L9r1;
F0 := g in elg;                        assume;
F01 := g1 in elg;                      assume;
F1 := g1*inv(g) in H;                  by LHinv3;     // ! LHinv3 := a in H == inv(a) in H;
F2 := inv(g1*inv(g)) in H;             by Tinvmlt;    // ! Tinvmlt := A[x,y:elg, inv(x*y) = inv(y) * inv(x)];
F3 := inv(inv(g))*inv(g1) in H;        by Tinvinv; 
F4 := g*inv(g1) in H;                  by -L9r;
F5 := g in H*g1;
 end EqProof -L9r1;

! L9l := A[g,g1: elg, g in g1*H == inv(g1)*g in H];  is TminS2a1; // ! TminS2a1 := A[a,x:elg, B:P[elg], a in x*B == inv(x)*a in B];

! L10 := A[x:elg, A[h:H, inv(x)*h*x in H] == inv(x)*H*x <: H];
 EqProof -L10;
F0 := x in elg;                       assume;
F1 := inv(x)*H*x <: H;                by TmeS;
F2 := R[h:H, inv(x)*h] * x <: H;      by -TRmfree2; // ! TRmfree2 := A[A:P[elg],a:elg, R[x:A, W_elg1(x) * a] = R[x:A, W_elg1(x)] * a]; 
F3 := R[h:H, inv(x)*h*x] <: H;        by TRA;       // ! TRA  := R[d, f] <: B == A[d, f in B]; 
F4 := A[h:H, inv(x)*h*x in H];
 end EqProof -L10;

! L11 := A[x:elg, A[h:H, x*h*inv(x) in H] == x*H*inv(x) <: H];
 EqProof -L11;
F0 := x in elg;                       assume;
F1 := x*H*inv(x) <: H;                by TmeS;
F2 := R[h:H, x*h] * inv(x) <: H;      by -TRmfree2; // ! TRmfree2 := A[A:P[elg],a:elg, R[x:A, W_elg1(x) * a] = R[x:A, W_elg1(x)] * a]; 
F3 := R[h:H, x*h*inv(x)] <: H;        by TRA;       // ! TRA  := R[d, f] <: B == A[d, f in B]; 
F4 := A[h:H, x*h*inv(x) in H];
 end EqProof -L11;

! L12 := A[x:elg, x*H=H*x == x*H*inv(x)=H ]; is TeqSmr1; // ! TeqSmr1  := A[x:elg, A,B:P[elg], A = B*x == A*inv(x) = B]; A: x*H, B:H;

! LHU1 := U[g_elg, g*H] = elg;          // ! LamHelg1 := A[g_elg, g * H <: elg]; // ! LH8l := A[g_elg, g in g*H];
 Proof LHU1;   
F0 := A[g_elg, g*H <: elg & g in g*H];  by TAconj1; LamHelg1 & LH8l;  // ! TAconj1 := A[x:A, P(x) & Q(x)] == A[x:A, P(x)] & A[x:A, Q(x)];
LHU1;                                   is TUA1(F0);          // ! TUA1 := A[x:A, F(x) <: A & x in F(x)] -> U[x:A, F(x)] = A;
 end Proof LHU1;

! LHU2 := U[g:elg, H*g] = elg;          // ! LamHelg2 := A[g_elg, H * g <: elg]; // ! LH8r := A[g_elg, g in H*g];
 Proof LHU2;
F0 := A[g_elg, H*g <: elg & g in H*g];  by TAconj1; LamHelg2 & LH8r;  // ! TAconj1 := A[x:A, P(x) & Q(x)] == A[x:A, P(x)] & A[x:A, Q(x)];
LHU2;                                   is TUA1(F0);          // ! TUA1 := A[x:A, F(x) <: A & x in F(x)] -> U[x:A, F(x)] = A;
 end Proof LHU2;

! TGre0  := elg = {e} -> H = {e};        
 Proof TGre0;
F0 := elg = {e};                        assume;
F01 := H <: elg;                        is LHelg; by F0;      //  ! LHelg := H <: elg;  
F1 := H <: {e};
F2 := H = {e};                          is TSIn4(F1 & LHnemp); // ! TSIn4 := X <: {a} & X ~= {} -> X = {a}; // ! LHnemp := H ~= {};
 end Proof TGre0;                       by CP;              // ! CP := p->q == ~q -> ~p;     // ContraPosition
 
! TGre1  := H ~= {e} -> elg ~= {e};   // by CP; TGre1;         // ! CP := p->q == ~q -> ~p;     // ContraPosition
! TGre1a := H ~= {e} -> E[x:H, x ~= e]; is TSeq3(LHnemp);     // ! TSeq3 :=  X ~= {} -> (X ~= {a} -> E[x:X, x ~= a]);

// ! TGr2   := A[k:int, A[a:elg, a^k in H == a^abs(k) in H]]; // not used; use int-induction: A[k:int,P(k)]==P(0) & A[k:nat, P(k)&P(-k)-> 
// ! TGr3   := subgr.Gr = {S; S in subgr, S <: H};            // not used; // subgr:: Gr := [H, *(group)|(H#H)];// P(k+1) & P(-k-1)];
// ! Tsbg1_ := A[H: subgr, subgr(Gr(H)) = {S; S in subgr, S <: H}]; // same as TGr3;
! LH1 := H in P[elg];                 by AxP; LHelg;          // !! AxP := Z in P[Y] == Z <: Y;  // ! LHelg := H <: elg; 
! L00 := P1[H] <: P[elg];             is TP1m1(LHelg);        // ! TP1m1 := X <: Y -> P1[X] <: P[Y];  // see prf case 14;

! Tsbgm1 := A[A: P[elg], A <: H*A];      // ! LmeSeIn := A[B:P[elg], e*B = B];
 Proof Tsbgm1;
F0 := A in P[elg];                    assume;
F1 := A <: H*A;                       by TmSS;                // ! TmSS := A[A:P[elg], B:P[elg], A * B = U[a:A, a*B]];
F2 := A <: U[x_H, x*A];               by TInA;                // ! TInA := A <: B == A[x:A, x in B];
F3 := A[a:A, a in U[x_H, x*A]]; 
  Proof F3;
F0 := a in A;                         assume;
// F01 := e in H;                     is LHe;                 // Witness handler should find LHe; 
F01 := a in e*A;                      by LeS; F0;             // ! LeS := A[S:P[elg], e * S = S]; 
G0 := a in U[x_H, x*A];               by TUin;    // ! TUin := x in U[d, w] == E[d, x in w];        
G1 := E[x_H, a in x*A];               is Witness(e);
  end Proof F3;
 end Proof Tsbgm1;

! Tsbg1 := A[a,b:H, x:elg, a*x = b -> x in H];                // because H is a subgroup;
 Proof Tsbg1;
F0 := a in H;                         assume;  
F0a := inv(a) in H;                   is LHinv;               // ! LHinv := A[x_H, inv(x) in H];
F01 := b in H;                        assume;
F01a := inv(a) * b in H;              is LHm;                 // ! LHm := A[x,y: H, x*y in H]; 
F02 := x in elg;                      assume;
F03 := a*x = b;                       assume;  by Teqmr;
F1 := x = inv(a) * b;
F2 := x in H;                         by F1; F01a;
 end Proof Tsbg1;

! L02 := A_P1_elg * H <: elg;         is typeaxiom;  // A_P1_elg * H in P[elg];
! TsbgR    := A[A:P1[elg], Goal := R[g: A*H, g*H] = R[g:A, g*H] ];
 EqProof TsbgR;
F0 := A in P1[elg];                    assume; // add to lot: A <: elg; A ~= {}, because A in P1[elg] == A <: elg & A ~= {};
// ! F01 := A*H <: elg;                   // because typ(H) = typ(R[a:A,h:H,a*h]) must be P1[elg]; 
// ! F02 := A <: elg;                     // should be add to lot automatically, check !!!
// ! F03 := H <: elg;                     // because typ(H) = P1[elg];
// ! F04 := R[a:A, k:H, a*k] <: elg;      // ! AssoceeS := A[a:elg, b:elg, C:P[elg], a*(b*C) = (a*b)*C];
// ! F05 := H ~= {};                      // because typ(H) = P1[elg];
// EqProof Goal;                          // ! TmSSR := A[A:P[elg], B:P[elg], A * B = R[a:A,b:B, a*b]];
F1 := R[g: A*H, g*H];                  by TmSSR(A,H);    // Def(A*H); // make:  by TmSSR(A,H); !!!
F2 := R[g: R[a:A, k:H, a*k], g*H];     by TRR;             // ! TRR  := R[x:R[d,f], G(x)] = R[d, G(f)]; 
F3 := R[a:A, k:H, (a*k)*H];            by -AssoceeS;       // ! AssoceeS := A[a:elg, b:elg, C:P[elg], a*(b*C) = (a*b)*C];
F4 := R[a:A, k:H, a*(k*H)];            by LH2l(k@F4);      // ! LH2l := A[h:H, h*H = H];   
F5 := R[a:A, k:H, a*H];                by Red("free", 2);  // a*H if free of k; !!! add istr2 !!! 2 is #k in abterm {a,k; a in A ...},f:free;
F6 := R[a:A, a*H];                             // free-reduction of A[d,Q], E[d,Q], R[d,Q]: result A[d1,Q1], ...;
//  end EqProof Goal;                          // if Q does not depend from d.m then replace d with d1 by removing d.m from d;
 end EqProof TsbgR;
                                      // ! TSneqemp := {a} ~= {};  // ! L03 := {e} in P[elg]; 
! LHmunion := A[z:elg, z*H in B -> z in union(B)];
 Proof LHmunion;
F0 := z in elg;                       assume;
F01 := z*H in B;                      assume;
F1 := z in z*H;                       is TmeSe;               // ! TmeSe := A[a:elg, B in P[elg], e in B -> a in a*B];
F2 := z in union(B);                  is Tunion2a(F01 & F1);  // !! Tunion2a := Z in A & x in Z -> x in union(A);         ///
 end Proof LHmunion;

// ! L07 := A[h:H,k:elg, h*k in H -> k in H]; // subgr: L9,L9l,L9r,L21,L20,L19,L12,L11,L10,L0r,L06-L00;
// ! L08 := A[h:elg,k:H, h*k in H -> h in H];
];  // subgr :: [ 1.Basics // subgr := {H; AxHt := H in P1[elg], AxclosedH := closed(H) };  // a subgroup is a set, not a group !

/////////////////////////////////  8. Leaving subgr, back to group: more theorems
 
! LH9A := A[H:subgr, x:elg, h:H, (x*h)*H = x*H];  // wrong: byeq LH9; // !! LH9 := A[x:elg, h:H, (x*h)*H = x*H];
 EqProof LH9A;
F0 := H in subgr;                         assume;
F01 := x in elg;                          assume;
F02 := h in H;                            assume;
F03 := A[x:elg, h:H, (x*h)*H = x*H];      is LH9.H;
F1 := (x*h)*H;                            by F03;
F2 := x*H;
 end EqProof LH9A;

! LH2lA := A[K:subgr,k:K, k*K = K];       // is LH2l@subgr;       // ! LH2l := A[h:H, h*H = H];
 EqProof LH2lA;
F0 := K in subgr;                         assume;
F01 := k in K;                            assume;
F02 := A[x:K, x*K = K];                   is LH2l.K;
F1 := k*K;                                by F02;
F2 := K;
 end EqProof LH2lA;

! TsubgrinS := A[A:P1[elg], A in subgr == A*A = A & invS(A) = A];
 Proof TsubgrinS;
F0 := A in P1[elg];                        assume;
G0 := A in subgr == A*A = A & invS(A) = A; by Deqv; L1 & L2;
L1 := A in subgr -> A*A = A & invS(A) = A;
  Proof L1;
H0 := A in subgr;                          assume;
H1 := A*A = A;                             is LH6.A;                     // subgr :: ! LH6 := H*H = H; 
H2 := invS(A) = A;                         is LH4.A;                     // subgr :: ! LH4 := invS(H) = H;
  end Proof L1;
L2 :=  A*A = A & invS(A) = A -> A in subgr;
  Proof L2;
H0 := A*A = A;                             assume;
H01 := A*A <: A;                           is Axext1(H0);                 // ! Axext1 := X=Y -> X<:Y;
H02 := invS(A) = A;                        assume;
H03 := invS(A) <: A;                       is Axext1(H02); 
H1 := A in subgr;                          by TsubgrinS0; H01 & H03;
  end Proof L2;                            // ! TsubgrinS0 := A[A:P1[elg], A in subgr == A*A <: A & invS(A) <: A];
 end Proof TsubgrinS;


! TH3 := A[H:subgr, x,y: H, x*y in H];   // see ! LHm := A[x,y: H, x*y in H];
 Proof TH3;                              //       LHm.H is A[x,y: H, x*y in H], but here H is from  TH3;
F0 := H in subgr;                    assume;
F01 := x in H;                       assume; 
F02 := y in H;                       assume;
F1 := x*y in H;                      is LHm.H(x,y);     // ??? (x,y) ???
 end Proof TH3;

! TH4 := A[H:subgr, x: H, y:elg, x*y in H -> y in H];
 Proof TH4;
H1 :=  A[x:H, inv(x) in H];          is LHinv.H;                   // ! LHinv := A[x_H, inv(x) in H];
H2 :=  A[x,y: H, x*y in H];          is LHm.H;                     // ! LHm := A[x,y: H, x*y in H];
F0 := H in subgr;                    assume;
F01 := x in H;                       assume; 
F02 := y in elg;                     assume;
F03 := x*y in H;                     assume; by TinExist;          // ! TinExist := a in X == Exist(x, x=a & x in X); ??? h = x*y; 11.23.20
F1 := Existx(h, (F1a := h=x*y) & (F1b := h in H));
F2 := y = inv(x)*h;                  by -Teqmr1;  F1a;             // ! Teqmr1 := A[a,x,b: elg, b = a*x == x = inv(a)*b];
F3 := inv(x) in H;                   is H1;                        // was is (LHinv.H)(inv(x)): ERROR, needs research;         
F4 := inv(x)*h in H;                 is H2; by -F2;                // was is (LHm.H)(inv(x),h): ERROR, needs research  
F5 := y in H;               
 end Proof TH4;

! TH4a := A[H:subgr, x: elg, y:H, x*y in H -> x in H];
 Proof TH4a;
H1 :=  A[x:H, inv(x) in H];          is LHinv.H;                   // ! LHinv := A[x_H, inv(x) in H];
H2 :=  A[x,y: H, x*y in H];          is LHm.H;                     // ! LHm := A[x,y: H, x*y in H];
F0 := H in subgr;                    assume;
F01 := x in elg;                     assume; 
F02 := y in H;                       assume;
F03 := x*y in H;                     assume; by TinExist;          // ! TinExist := a in X == Exist(x, x=a & x in X);
F1 := Existx(h, (F1a := h=x*y) & (F1b := h in H));
F2 := x = h*inv(y);                  by -Teqml1;  F1a;             // ! Teqml1 := A[a,x,b:elg, b=x*a == x = b*inv(a)]; 
F3 := inv(y) in H;                   is H1;                    
F4 := h*inv(y) in H;                 is H2; by -F2;
F5 := x in H;               
 end Proof TH4a;

////////////////////                9.  The theory HK about two subgroups H and K  

HK := subgr && {K;  AxK := K in subgr}; // HK := {H,K ; AxH := H in subgr, AxK := K in subgr};
// explain what  d && d1 means          // subgr := {H; AxHt := H in P1[elg], AxclosedH := closed(H) };
HK :: [  // HK.1                        // going inside the theory HK 
////////////////                         8.1 Some K-theorems            
! LH1K := K in P[elg];                  is LH1.K;                  // ! LH1 := H in P[elg];
! LKelg := K <: elg;                    is LHelg.K;   // was LK2;
! LHeK := e in K;                       is LHe.K;                  // ! LHe := e in H; 
! LclosedK := closed(K);                is AxclosedH.K;            //  AxclosedH := closed(H) };
! LKinv2 := A[x,y: K, x*y*inv(x) in K]; is LHinv2.K;               // ! LHinv2 := A[x,y: H, x*y*inv(x) in H];
GrK := Gr.K;         // val = [K, *_K := *(group)|(K#K)];          // subgr :: Gr := [H, *(group)|(H#H)];
! AxGrK := GrK = [K, *_K := *(group)|(K#K)];   is AxGr.K;          // was L18; subgr:: ! AxGr := Gr = [H, *(group)|(H#H)];
! TGrKelg := elg.GrK = K;               is Red;                    // standard reduction, using isst: F[d,f](z), A[d,P](z), Q.M, ...
! TGrK_type := GrK in group;            is TGr_type.K;             // ! TGr_type := Gr in group;
! TclosedGrK := A[S:P[K], closed.GrK(S) == closed(S)]; is TclosedGr.K;  //subgr  ! TclosedGr := A[S:P[H], (closed.Gr)(S) == closed(S)];
! LsubgrGrK :=  subgr.GrK = {H; H in P1[K], closed.GrK(H); };      is Tsubgr.GrK; by TclosedGrK;
! TsubgrGrK := subgr.GrK = {H; H in P1[K]; closed(H); };           // ! Tsubgr := subgr = {H; H in P1[elg], closed(H) };
!! Lm_K_type := *_K in fn(K#K,K);

! L25 := H in subgr.GrK == H <: K;
 EqProof L25;
F1 := H in subgr.GrK;                          by TsubgrGrK;    
F2 := H in {H; H in P1[K], closed(H); };       by Axab;           // 
F3 := H in P1[K] & closed(H);                  by AxP1;           // !! AxP1 := S in P1[Y] == S <: Y & S ~= {};
F4 := H <: K & H ~= {} & closed(H);            by LHnemp;         // ! LHnemp := H ~= {};
F5 := H <: K & true & closed(H);               by AxclosedH;      // AxclosedH := closed(H);
F6 := H <: K & true & true;                    by Taut(p & true & true == p);
F7 := H <: K;
 end EqProof L25;

*_eS_K := *(meS).GrK;
! L20_type := *_eS_K in fn(K # P[K], P[K]);          is TmeSt.GrK;       // ! TmeSt := *(mlteS) in fn(elg # P[elg], P[elg]);
*_Se_K := *(mSe).GrK;
! L21_type := *_Se_K in fn(P[K] # K, P[K]);          is TmSet.GrK;       // ! TmSet := *(mltSe) in fn(P[elg] # elg, P[elg]);
// *_K := *(group).GrK;                              // very simple dot term, can be replaced with *(group)|(K#K)
// ! L22_type := *_K in fn(K#K);

! LsbgIP := H/\K in P[elg];          is TclosedP(LH1 & LH1K);      // ! TclosedP := A in P[elg] & B in P[elg] -> A /\ B in P[elg];
! LsbgInemp := H/\K ~= {};           is TinIemp1(LHe & LHeK);      // ! TinIemp1 := a in X1 & a in Y1 -> X1/\Y1 ~= {};
! LsbgIP1 := H/\K in P1[elg];        by TP1P; LsbgInemp & LsbgIP;  // ! TP1P := S in P1[Y] == S ~= {} & S in P[Y];  
! LclosedHIK := closed(H/\K);        is TclosedI(H,K)( AxclosedH & LclosedK);
! TsbgI := H/\K in subgr;            by Axab; LsbgIP1 & LclosedHIK;// ! TclosedI := A[A,B:P[elg],closed(A)&closed(B) -> closed(/\ B)];
! TsbgI1 := K/\H in subgr;           by TIcomm;  TsbgI;            // ! TIcomm := X/\Y = Y/\X;      
! LsbgInm := H <: H*K;               is TmSSe(H,K)(LHeK);          // ! TmSSe := A[A_B_P_elg, e in B -> A <: A*B]; // ! LHeK := e in K; 
! LsbgInm1 := H <: K*H;              is TmSSe1(H,K)(LHeK);         // !! TmSSe1 := A[A_B_P_elg, e in B -> A <: B*A];
! L13 := H/\K in P[elg];             is TclosedP(LH1 & LH1K);      // ! TclosedP := A in P[elg] & B in P[elg] -> A /\ B in P[elg];
! LK3 := H\/K <: elg;                by TUIn2; LHelg & LKelg;      // ! TUIn2 := X \/ Y <: Z == X <: Z & Y <: Z; 
! L07 := H*K in P1[elg];             is TmSSP1;                    // ! TmSSP1 := A[A:P1[elg], B:P1[elg], A*B in P1[elg]]; 

// ! TsbgIn := H <: K -> H in subgr(GrK);
// Proof TsbgIn;
//F0 := 
//F0 := H <: K;                           assume;  ! Tsubgrin0 := A in subgr == A in P1[elg] & closed(A);  
// F1 : 


// ! TsbgI2 := H in subgr(GrK) == H <: K;
// ! TsbgI3 := H /\ K in subgr(GrK);                               // ! LH1 := H in P[elg];  //  LH1K := K in P[elg];

// ------------------8.2  The union of two subgroups is a subgroup iff one of the subgroup is a subset of other
! TsbgU := H\/K in subgr == H<:K or K<:H;
 Proof TsbgU;              by Deqv; M1 & M2;         // Deqv := (p==q) == (p->q) & (q->p);
M1 := H\/K in subgr -> H<:K or K<:H;
  Proof M1;                                          // by reductio ad absurdum;
F0 := H\/K in subgr;    assume;
F01 := ~(H<:K or K<:H); assume; by TNor; F1 & F2;    // TNor := ~(p or q) == (~p) & (~q);
F1 := ~(H<:K);          by -TDempIn1;                // TDempIn1 := C -- D ~= {} ==  ~(C <: D);
F1a := H--K ~= {};      by Axarb; F1b;               // Axarb := X ~= {} == arb(X) in X; 
h := arb(H--K); 
F1b := h in H--K;       by AxD1; F1c & F1e;          // AxD1 := a1 in X -- Y == a1 in X & ~(a1 in Y); 
F1c := h in H;          with TinU1;                  // TinU1 := a in X0 -> a in X0 \/ Y0; 
F1d := h in H\/K;       
F1e := ~(h in K);
F2 := ~(K<:H);          by -TDempIn1;                // TDempIn1 := C -- D ~= {} ==  ~(C <: D);
F2a := K--H ~= {};      by Axarb; F2b;               // Axarb := X ~= {} == arb(X) in X; 
k := arb(K--H);  
F2b := k in K--H;       by AxD1; F2c & F2e;          // AxD1 := a1 in X -- Y == a1 in X & ~(a1 in Y); 
F2c := k in K;          with TinU1;                  // TinU1 := a in X0 -> a in X0 \/ Y0; 
F2d := k in K\/H;       by TUcomm;                   // TUcomm := X \/ Y = Y \/ X;   
F2d1 := k in H\/K;
F2e := ~(k in H); 
! L08 := h in elg;                                   // AxU := a in X1\/Y1 == a in X1 or a in Y1 ;
! L09 := k in elg;
! L10 := H\/K <: elg;
F3 := A[x,y:H\/K, x*y in H\/K];                      is LHm.((H\/K):subgr); //subgr :: LHm := A[x,y: H, x*y in H];
F3a := h*k in H\/K;                                  is F3(h,k); by AxU;
F4 := h*k in H or h*k in K;
false;                  by Case2(F4); L1 & L2;       // Case2 := p1 or p2 -> (_q == (p1 -> _q) & (p2 -> _q));
L1 :=  h*k in H -> false;
   Proof L1;
G0 := h*k in H;         assume;
G1 := k in H;           is TH4(H,h,k)(G0);   with F2e; false; // ! TH4 := A[H:subgr, x: H, y:elg, x*y in H -> y in H]; 
   end Proof L1;
L2 :=  h*k in K -> false;
   Proof L2;
G0 := h*k in K;         assume;       
G1 := h in K;           is TH4a(K,h,k)(G0);  with F1e; false; // ! TH4a := A[H:subgr, x: elg, y:H, x*y in H -> x in H];
   end Proof L2;
  end Proof M1;
M2 := H<:K or K<:H -> H\/K in subgr;                 // use H<:K -> H\/K = K, AxK;  K<:H -> H\/K = H, AxK;
  Proof M2;
F0 := H<:K or K<:H;     assume;
Goal := H\/K in subgr;  by Case2(F0); L1 & L2;       // Case2 := p1 or p2 -> (_q == (p1 -> _q) & (p2 -> _q));

L1 := H<:K -> H\/K in subgr;
   Proof L1;
F0 := H<:K;             assume;   by TU2;   // TU2 := X <: Y == X\/Y = Y; 
F1 := H\/K = K;         with AxK;           // AxK := K in subgr;  // almost same as: F2; by F1; AxK;
F2 := H\/K in subgr;    // !! Axeqconj := a=b & Q -> Sb(Q,a,b);  !! Axeqconj1 := a=b & Q -> Sb(Q,b,a);
   end Proof L1;
 
L2 := K<:H -> H\/K in subgr;
   Proof L2;
F0 := K<:H;            assume;    by TU2a;  // TU2a := X <: Y == Y\/X = Y
F1 := H\/K = H;        with AxH;
F2 := H\/K in subgr;
   end Proof L2;
  end Proof M2;
 end Proof TsbgU;
/*              // currently only one proof can be 7.19.21  prf must not only h->t = 0, but also remove T from tabt;
// Another proof of TsbgU
 Proof TsbgU;              by Deqv; M1 & M2;       // Deqv := (p==q) == (p->q) & (q->p);
M1 := H\/K in subgr -> H<:K or K<:H;
  Proof M1;                                        // by reductio ad absurdum;
F0 := H\/K in subgr;    assume;
F01 := ~(H<:K or K<:H); assume; by TNor; F1 & F2;  // TNor := ~(p or q) == (~p) & (~q);
F1 := ~(H<:K);          by TNIn;                   // TNIn := ~(X2 <: Y2) == Exist(x, x in X2 & ~(x in Y2));
F1a := Existx(h, (Lh1 := h in H) & (Lh2 := ~(h in K)));  // Existx(h, ...) means Exist(h,...) and h is visible in the enclosing scope;                
F1b := h in H\/K;       is TinU1(Lh1);             // TinU1 := a in X0 -> a in X0 \/ Y0;
F1c := h in elg;        is TinIn(Lh1 & LHelg);       // TinIn := x in X2 & X2 <: Y2 -> x in Y2; // LHelg := H <: elg;
F2 := ~(K<:H);          by TNIn;                   // TNIn := ~(X2 <: Y2) == Exist(x, x in X2 & ~(x in Y2));  
F2a := Existx(k, (Lk1 := k in K) & (Lk2 := ~(k in H)));  // Existx(k, ...) means Exist(k,...) and k is visible in the enclosing scope;                
F2b := k in H\/K;       is TinU1a(Lk1);            // TinU1a := a in X0 -> a in Y0 \/ X0;
F2c := k in elg;        is TinIn(Lk1 & LKelg);       // TinIn := x in X2 & X2 <: Y2 -> x in Y2; // ! LKelg := K <: elg;  
F3 := h*k in H\/K;      is TH3(H\/K,h,k); by AxU;  // ! TH3 := A[H:subgr, x,y: H, x*y in H];  // !! AxU := a in X1\/Y1 == a in X1 or a in Y1 ;             
F4 := h*k in H or h*k in K;
false;                  by Case2(F4); L1 & L2;     // Case2 := p1 or p2 -> (_q == (p1 -> _q) & (p2 -> _q));
L1 :=  h*k in H -> false;
   Proof L1;
G0 := h*k in H;         assume;     
G1 := k in H;           is TH4(H,h,k)(G0);  with Lk2; // ! TH4 := A[H:subgr, x: H, y:elg, x*y in H -> y in H]
false;                 
   end Proof L1;
L2 :=  h*k in K -> false;
   Proof L2;
G0 := h*k in K;         assume;                    // with L08.H(h,k);
G1 := h in K;           is TH4a(K,h,k)(G0); with Lh2;  // ! TH4a := A[H:subgr, x: elg, y:elg, x*y in H -> x in H]
false;  
   end Proof L2;
  end Proof M1;
M2 := H<:K or K<:H -> H\/K in subgr;                 // use H<:K -> H\/K = K, AxK;  K<:H -> H\/K = H, AxK;
  Proof M2;
F0 := H<:K or K<:H;     assume;     by TU2, TU2a;    // TU2 := X <: Y == X\/Y = Y; TU2a := X <: Y == Y\/X = Y;
F1 := H\/K = K or H\/K = H;
Goal := H\/K in subgr;  by Case2(F1); L1 & L2;       // Case2 := p1 or p2 -> (_q == (p1 -> _q) & (p2 -> _q));

L1 := H\/K = K -> H\/K in subgr;
   Proof L1;
F0 :=  H\/K = K;             assume;  
Goal := H\/K in subgr;       by F0; AxK;             // AxK := K in subgr;
   end Proof L1;
 
L2 := H\/K = H -> H\/K in subgr;
   Proof L2;
F0 := H\/K = H;             assume;     
Goal := H\/K in subgr;      by F0;  AxH;            // AxH := H in subgr;
   end Proof L2;
  end Proof M2;
 end Proof TsbgU;
*/
! LSSass1 := (H*K)*(H*K) = H*(K*H)*K;       is Associnve;
! LSSass2 := H*(H*K)*K = (H*H)*(K*K);       is Associnve;

! Tsbgmlt := H*K in subgr == H*K = K*H;   // H*K in subgr -> inv(H*K) = inv(K)*inv(H) == H*K = K*H;
 Proof Tsbgmlt;                        by Deqv;  Goal1 & Goal2;  // Deqv := (p==q) == (p->q) & (q->p);
Goal1 := H*K in subgr -> H*K = K*H;
  Proof Goal1;
G0 := H*K in subgr;                    assume;  // subgr :: ! LH4 := invS(H) = H;  // LH4.H => invS(H) = H;
G1 := invS(H*K) = invS(K)*invS(H);     is TinvSm(H,K); by LH4.(H*K), LH4.K, LH4.H; // LH4.K => invS(K) = K;  // LH4.(H*K) => invS(H*K) = H*K;
G2 := H*K = K*H;                       // ! TinvSm := A[A,B: P[elg], invS(A*B) = invS(B)*invS(A)];
  end Proof Goal1;
Goal2 := H*K = K*H -> H*K in subgr;
  Proof Goal2;
G0 := H*K = K*H;                       assume;  
Goal3 := H*K in subgr;                 by TsubgrinS; G1 & G2;    // was by TsubgrinS(H*K);
G1 := (H*K)*(H*K) = H*K;               // ! TsubgrinS := A[A:P1[elg], A in subgr == A*A = A & invS(A) = A];
   EqProof G1;
H1 := (H*K)*(H*K);                     by LSSass1;       // ! LSSass1 := (H*K)*(H*K) = H*(K*H)*K;
H2 := H*(K*H)*K;                       by -G0;
H3 := H*(H*K)*K;                       by LSSass2;       //  LSSass2 := H*(H*K)*K = (H*H)*(K*K); 
H4 := (H*H)*(K*K);                     by LH6.H, LH6.K;  // subgr :: ! LH6 := H * H = H;
H5 := H*K;
   end EqProof G1;
G2 := invS(H*K) = H*K;
   EqProof G2;
H1 := invS(H*K);                       by TinvSm(H,K);
H2 := invS(K)*invS(H);                 by LH4.K, LH4.H;
H3 := K*H;                             by -G0;
H4 := H*K;
   end EqProof G2;
  end Proof Goal2;
 end Proof Tsbgmlt;
]; // HK :: [  HK.1

! L25A := A[H,K: subgr, H in subgr.(Gr.K) == H <: K];  is L25@HK;   // HK :: ! L25 := H in subgr.GrK == H <: K;
]; // group :: [           // Subgroups: 1.Basics;

abelgroup := {elag, +; Ax1 := elag in set; Ax2 := + in fn(elag#elag,elag);  Axcomm := A[x,y:elag, x+y = y+x] };  // (abelgroup)

!! Axabelgroup := abelgroup <: group;   // AxEe   := Existx(e, (Axe := e in elg) &  

abelgroup :: [
G := [elag, +];
!! AxG_type := G in group;                                 // AxG_type is an axiom !!!
0z := e.G;                      // dcl[0z, elag]; 
! Ax0a := 0z = e.G;             is Axrefl;                 // Axrefl := x = x;
invab := dcl[-,fn(elag,elag)];                            //#9277
!! Axinv := -(invab) = inv.G;                               // '-1' := inv.G;
subt := dcl[-, fn(elag#elag, elag)];                      // '-' := div.G;
Axadd  := (+) in fn(elag#elag, elag);                     is Axm.G;     // Axm    := * in fn(elg#elg, elg); 
AxAssoc := A[x,y,z: elag, x+(y+z) = (x+y)+z ];            is AxAssoc.G;
Axz    := 0z in elag;                                     is Axe.G;     // error: Axe.G => e in elag; (e ~= 0z);
Tinvtabel := -(invab) in fn(elag, elag);                  is Axinv.G;   // Axinv  := inv in fn(elg, elg))// Tinvtabel:t: type;
Axrz   := A[x:elag, x + 0z = x];                          is Axre.G;    // 5: bvar, 6: con
Axrinvabel := A[x: elag, x + (-x) = 0z];                  is Axrinv.G;  // Axrinv := A[x: elg, x * inv(x) = e]))))
// actually, if G = (A,f) is an abelgroup, then (A,f) is a group and all theorems of group theory are applicable to G.
Zf := F[f:FN, A[x:dom(f), f(x) = 0z] ];      
! TZf1 := A[f:FN, Zf(f) == im(f) = {0z}];
Nz := F[f:FN, E[x:dom(f), f(x) ~= 0z] ];
! TNZf1 := A[f:FN, ~Zf(f) == Nz(f)];
! TNz1 := A[f:FN, Nz(f) == im(f) ~= {0z} ]; 
! TNNz := A[f:FN, ~Nz(f) == Zf(f)];

! Tabelsbg := A[K: subgr.G, abel.(Gr.K)];             // abel.(Gr(K)) ??? 2023.04.06 

]; // abelgroup :: [

group :: [  // 3
// dcl[rcosets, fn(subgr,P[P[elg]] ];   // check: rcosets := F[subgr, R[g:elg, H*g]];
// dcl[lcosets,subgr,P[P[elg]] ];
subgr :: [  // 2. cosets
rc := F[g:elg, H*g];                                           // right cosets;        //  rcosets = im(F[g:elg, H*g]);
lc := F[g:elg, g*H];                                           // left cosets;
Lrc_type := rc in fn(elg, P[elg]);                             is typeaxiom;           // type(F[d,Q]) = fn(Q, type(Q)                              
Llc_type := lc in fn(elg, P[elg]);                             is typeaxiom;
rcosets := im(rc);
lcosets := im(lc);
! LrcosetsInP := rcosets <: P[elg];                            is Tfnim(Lrc_type);     // !! Tfnim := f in fn(A,B) -> im(f) <: B;
! LlcosetsInP := lcosets <: P[elg];                            is Tfnim(Llc_type); 
// ! Axrcosets := rcosets = im(rc);                               is Axrefl;    // x = x;
// ! Axlcosets := lcosets = im(lc);                               is Axrefl;
! Lrcosets1 := rcosets = R[g:elg, H*g];                        byeq TimF;               // ! TimF   := im(F[d, G]) = R[d, G]; 
! Llcosets1 := lcosets = R[g:elg, g*H];                        byeq TimF;               // same as byeq Axlcosets, Timf;
! Lrcosets2 := A[g:elg, H*g in rcosets];                       by Lrcosets1; is TAinR;  // TAinR := A[d, f in R[d,f]];
! Llcosets2 := A[g:elg, g*H in lcosets];                       by Llcosets1; is TAinR;  // TAinR := A[d, f in R[d,f]];
! Llcosetsin := X in lcosets == E[g:elg, X = g*H];             byeq Llcosets1,TRin;     // ! TRin := z in R[d,f] == E[d, z = f];
! Llcosetsin1 := X in lcosets == Exist(g, g in elg & X = g*H); byeq Llcosetsin,AxEconj; // !! AxEconj := E[x:B, Q(x)] == Exist(x, x in B & Q(x));
! Lrcosetsin := X in rcosets == E[g:elg, X = H*g];             byeq Lrcosets1,TRin;  
! Lrcosetsin1 := X in rcosets == Exist(g, g in elg & X = H*g); byeq Lrcosetsin,AxEconj; 
// ! LHme := H*e = H;                                             is LSe;               // is LSe(H) 
! L20 := H*e in rcosets;                                       is Lrcosets2; by LSe;    // ! LSe := A[S:P[elg], S*e = S]; 
! Lrcosets3 := H in rcosets;    
! L20a := e*H in lcosets;                                      is Llcosets2; by LeS;    // ! LeS := A[S:P[elg], e * S = S];
! Llcosets3 := H in lcosets;                                                 
! LrcosetsN := rcosets ~= {};                                  is Tinnemp(Lrcosets3);   // Tinnemp := x in X -> X ~= {};
! Llcosets4 := A[g:elg, invS(H*g) in lcosets];                 // not used;                                             

! LrcosetseqpH := A[Q: rcosets, eqp(Q,H)];                     // !! Teqp4 := f in bfn(A,B) -> eqp(A,B); ! TUunion := U[d,w] = union(R[d,w]);
 Proof LrcosetseqpH;
F0 := Q in rcosets;                                            assume; by Lrcosetsin1;
F01 := Existx(g, g in elg & (F01a := Q = H*g));
F1 := eqp(H*g,H);                                              is Teqpr; by -F01a;       // ! Teqpr := A[S:P[elg], g:elg, eqp(S*g, S)];
F2 := eqp(Q,H);
 end Proof LrcosetseqpH;

! LlcosetseqpH := A[Q: lcosets, eqp(Q,H)];                     // !! Teqp4 := f in bfn(A,B) -> eqp(A,B); 
 Proof LlcosetseqpH;
F0 := Q in lcosets;                                            assume; by Llcosetsin1;
F01 := Existx(g, g in elg & (F01a := Q = g*H));
F1 := eqp(g*H,H);                                              is Teqpl; by -F01a;    // ! Teqpl := A[S:P[elg], g:elg, eqp(g*S, S)];
F2 := eqp(Q,H);
 end Proof LlcosetseqpH;                                       // ! TUunion := U[d,w] = union(R[d,w]);
                                                               // ! Lrcosets1 := rcosets = R[g:elg, H*g]; 
! LrcosetsunionU := union(rcosets) = U[g:elg, H*g];            byeq Lrcosets1, -TUunion;  by LHU2;
! Lrcosets6 := union(rcosets) = elg;                           // ! LHU2 := U[g:elg, H*g] = elg; // ! LHU1 := U[g_elg, g*H] = elg;  
! LlcosetsunionU := union(lcosets) = U[g:elg, g*H];            byeq Llcosets1, -TUunion;  by LHU1;
! Llcosets6 := union(lcosets) = elg;                           // !! TUunion := U[d,w] = union(R[d,w]); 
                                                               // ! Llcosets1 := lcosets = R[g:elg, g*HH]; 
! Lrcosets7 := A[Q: rcosets, Q ~= {}];
 Proof Lrcosets7;                                              // ! Lrcosetsin1 := X in rcosets == Exist(g, g in elg & X = H*g)
F0 := Q in rcosets;                                            assume; by Lrcosetsin1;
F01 := Existx(x, x in elg & (F01a := Q = H*x));
G0 := Q ~= {};                                                 by F01a;
G1 := H*x ~= {};                                               is LHmnempr;             // ! LHmnempr := H*a ~= {}; 
 end Proof Lrcosets7;

! Llcosets7 := A[Q: lcosets, Q ~= {}];
 Proof Llcosets7;                                              // ! Lrcosetsin1 := X in rcosets == Exist(g, g in elg & X = H*g)
F0 := Q in lcosets;                                            assume; by Llcosetsin1;
F01 := Existx(x, x in elg & (F01a := Q = x*H));
G0 := Q ~= {};                                                 by F01a;
G1 := x*H ~= {};                                               is LHmnempl;             // ! LHmnempl := H*a ~= {}; 
 end Proof Llcosets7;

! Lrcosets10 := A[Q: rcosets, x:Q, Q = H*x];
 EqProof -Lrcosets10;
F0 := Q in rcosets;                                            assume; by Lrcosetsin1;
F01 := Existx(x1, x1 in elg & (F01a := Q = H*x1));
F02 := x in Q;  assume;    // ! LrSein1   := A[{A,B,a,c; A in P[elg], B in P[elg], a in A, c in elg, A = B*c}, Exist(b, b in B & a = b*c)];
F03 := Existx(h, h in H & (F03a := x = h*x1));                 is LrSein1(Q,H,x,x1);
F1 := H*x;                                                     by F03a;
F2 := H*(h*x1);                                                by Associnve;    
F3 := (H*h)*x1;                                                by LH2r;         // ! LH2r := A[x_H, H*x = H];
F4 := H*x1;                                                    by -F01a;
F5 := Q;
 end EqProof -Lrcosets10;

! Llcosets10 := A[Q: lcosets, x:Q, Q = x*H];
 EqProof -Llcosets10;
F0 := Q in lcosets;                                            assume; by Llcosetsin1;
F01 := Existx(x1, x1 in elg & (F01a := Q = x1*H));
F02 := x in Q;  assume;  // ! LlSein1 := A[{A,B,a,c; A in P[elg],B in P[elg],a in A,c in elg,Ax5 := A = c*B},Exist(b, b in B & a = c*b)];
F03 := Existx(h, h in H & (F03a := x = x1*h));                 is LlSein1(Q,H,x,x1);
F1 := x*H;                                                     by F03a;
F2 := (x1*h)*H;                                                by Associnve;    
F3 := x1*(h*H);                                                by LH2l;         // ! LH2l := A[x_H, x*H = H]; 
F4 := x1*H;                                                    by -F01a;
F5 := Q;
 end EqProof -Llcosets10;

! LrcosetsNI := A[Q1,Q2: rcosets, Q1/\Q2 ~= {} -> Q1=Q2];
 Proof LrcosetsNI;
F0 := Q1 in rcosets;                assume;
F01 := Q2 in rcosets;               assume;
F02 := Q1/\Q2 ~= {};                assume;  by TinnempE;  // ! TinnempE := All(X, X ~= {} == Exist(x, x in X));
F1 := Existx(x, F1a := x in Q1/\Q2);        
F1a;                                 by AxI;  F2 & F3;     // !! AxI := a in X1/\Y1 == a in X1 & a in Y1;
F2 := x in Q1;
F3 := x in Q2;                                                   // ! TininP := x in X2 & X2 in P[Y2] -> x in Y2;
F03 := Q1 in P[elg];                is TinIn(F0 &  LrcosetsInP); // TinIn := x in X2 & X2 <: Y2 -> x in Y2;
F04 := x in elg;                    is TininP(F2 & F03);         // ! LrcosetsInP := rcosets <: P[elg];  // for checking H*x in F4,F5;
F4 := Q1 = H*x;                     is Lrcosets10;               // ! Lrcosets10 := A[Q: rcosets, x:Q, Q = H*x];
F5 := Q2 = H*x;                     is Lrcosets10;
F6 := Q1 = Q2;                      is  Axeq2(F4 & F5);    // !! Axeq2 := x=a & y=a -> x=y;
 end Proof LrcosetsNI;

! Llcosetsineq := A[Q1,Q2: lcosets, x:elg, x in Q1 & x in Q2 -> Q1=Q2];     // was LlcosetsNI;
 Proof Llcosetsineq;
F0 := Q1 in lcosets;                assume;
F01 := Q2 in lcosets;               assume;
F02 := x in elg;                    assume;
F1 := x in Q1;                      assume;
F2 := x in Q2;                      assume;
F3 := Q1 = x*H;                     is Llcosets10;
F4 := Q2 = x*H;                     is Llcosets10;
F5 := Q1 = Q2;                      is  Axeq2(F3 & F4);    // !! Axeq2 := x=a & y=a -> x=y;
 end Proof Llcosetsineq;

! LlcosetsNI := A[Q1,Q2: lcosets, Q1/\Q2 ~= {} -> Q1=Q2];
 Proof LlcosetsNI;
F0 := Q1 in lcosets;                assume;
F01 := Q2 in lcosets;               assume;
F02 := Q1/\Q2 ~= {};                assume;  by TinnempE;  // ! TinnempE := All(X, X ~= {} == Exist(x, x in X));
F1 := Existx(x, F1a := x in Q1/\Q2);
F1a;                                by AxI; F2 & F3;       // !! AxI := a in X1/\Y1 == a in X1 & a in Y1;
F2 := x in Q1;
F3 := x in Q2;
F4 := Q1 = Q2;                      is Llcosetsineq(Q1,Q2,x);       // Llcosetsineq(Q1,Q2,x)(F02);  
 end Proof LlcosetsNI;

! Lrcosets9 := A[Q:rcosets, H*Q = Q]; 
 EqProof Lrcosets9;
F0 := Q in rcosets;                 assume; by Lrcosetsin; // ! Lrcosetsin := X in rcosets == E[g:elg, X = H*g];
F01 := Ex[g:elg, F02 := Q = H*g];
F1 := H*Q;                          by F02;
F2 := H*(H*g);                      by Associnve;
F3 := (H*H)*g;                      by LH6;                // ! LH6 := H * H = H;
F4 := H*g;                          by -F02;
F5 := Q;
 end EqProof Lrcosets9;
                                                           // ! Teqpr := A[S:P[elg], g:elg, eqp(S*g, S)];
! Lrcosetseqp :=  A[Q1,Q2: rcosets, eqp(Q1,Q2)];
 Proof Lrcosetseqp;
F0 := Q1 in rcosets;                assume;
F01 := Q2 in rcosets;               assume;
F1 := eqp(Q1,H);                    is LrcosetseqpH;       // ! LrcosetseqpH := A[Q: rcosets, eqp(Q,H)];
F2 := eqp(Q2,H);                    is LrcosetseqpH;
F3 := eqp(Q1,Q2);                   is Teqp3(F1 & F2);     // ! Teqp3 := eqp(A,C) & eqp(B,C) -> eqp(A,B);
 end Proof Lrcosetseqp;
                            // !! Tprtin := [A,B] in partition == union(B)=A & A[Q:B, Q ~= {}] & A[Q1,Q2:B,  Q1/\Q2 ~= {} -> Q1=Q2];  
! Lrcosetspart := [elg, rcosets] in partition;   by Tprtin; Lrcosets6 & Lrcosets7 & LrcosetsNI; // ! Lrcosets6 := union(rcosets) = elg; 
! Llcosetspart := [elg, lcosets] in partition;   by Tprtin; Llcosets6 & Llcosets7 & LlcosetsNI;
 
! Llcosets9 := A[Q:lcosets, Q*H = Q];
 EqProof Llcosets9;
F0 := Q in lcosets;                 assume; by Llcosetsin; // ! Llcosetsin := X in lcosets == E[g:elg, X = g*H];
F01 := Ex[g:elg, F02 := Q = g*H];
F1 := Q*H;                          by F02;
F2 := (g*H)*H;                      by Associnve;
F3 := g*(H*H);                      by LH6;                // ! LH6 := H * H = H;
F4 := g*H;                          by -F02;
F5 := Q;
 end EqProof Llcosets9;

! Lrc1 := A[x:elg, x in rc(x)];                            // byA(Def(rc(x)), LH1r(x));
! Lrc2 := A[Q:rcosets, x:Q,  rc(x) = Q];

! L21 := A[g,g1: elg, g*H = H*g1 ->g*H = H*g];
 Proof L21;
F0 := g in elg;                     assume;
F01 := g1 in elg;                   assume;
F02 := g*H = H*g1;                  assume;
F03 := g in g*H;                    is LH8l(g); by F02;    // ! LH8l := A[g:elg, g in g*H];
F04 := g in H*g1;                   by L9r1;               // ! L9r1 := A[g,g1: elg, g in H*g1 == g1*inv(g) in H];
F05 := g1*inv(g) in H;
Goal := g*H = H*g;
  EqProof Goal;
F1 := g*H;                          by F02;
F2 := H*g1;                         by Associnve;
F3 := (H*(g1*inv(g)))*g;            by LH2r(g1*inv(g));    // ! LH2r := A[h:H, H*h = H]; 
F4 := H*g;
  end EqProof Goal;
 end Proof L21;
];  // subgr :: [  // 2.cosets
];  // group :: [  // 3
///////////////////////////  Normal subgroups  ///////////////////////////////  
ggg := group @ "1_group";
 group :: [                                                        // 4 normal, <| ;  // dcl[<|,fn(subgr#subgr,bool) ];
dcl[normal, fn(subgr, bool)];                                            // normal(H) == H <| elg;
!! Axnormal0 := A[H:subgr, normal(H) == A[x:elg, x*H = H*x]];
subgr :: [     // 3. normal
// normal := A[x:elg, x*H = H*x]; // H is a normal subgroup
// ! L03 := H in subgr;                                            // see LHinsubgr;
! Axnormal := normal(H) == A[x:elg, x*H = H*x];                    is Axnormal0(H);
! Lnormale := normal({e});   by Axnormal0, Lxe, Lex; is Taut; // ! Lxe := A[x:elg, x * {e} = {x}]; ! Lex := A[x:elg, {e} * x = {x}];    
! Tnormal0 := normal(H) == H in nsubgr; by Axab,LHinsubgr; is Taut; // p==(true&p); // group :: nsubgr := {N; N in subgr; normal(N)};

! Tnormal1 := normal(H) == (AS := A[S:P[elg], SHS := S*H = H*S]);  // use {s}*H = s*H, S*H = U[s:S, s*H];
 Proof Tnormal1;     by Deqv;   L1 & L2;
L1 := normal(H) -> AS;
  Proof L1;
F0 := normal(H);     assume;  by Axnormal;
F01 := A[x:elg, x*H = H*x];
// Goal := A[S:P[elg], S*H = H*S ];
   Proof AS;
G0 := S in P[elg];   assume;
// Goal1 := S*H = H*S;
    EqProof SHS;
G1 := S*H;           by TmSS;              // TmSS := A[A:P[elg], B:P[elg], A * B = U[a:A, a*B]]; 
G2 := U[s:S,s*H];    by F01(s@G2);
G3 := U[s:S,H*s];    by -TmSSr;            // TmSSr := A[A:P[elg], B:P[elg], A * B = U[b:B, A*b]];
G4 := H*S;
    end EqProof SHS;
   end Proof AS;
  end Proof L1;

L2 := AS -> normal(H);
  Proof L2;
AS;                  assume;                      // AS := A[S:P[elg], SHS := S*H = H*S];
Goal := normal(H);   by Axnormal;
G0 := A[x:elg, x*H = H*x];
  Proof G0;
F0 := x in elg;      assume;                      // TmsS1  := A[A:P[elg], b:elg, A * {b} = A * b];
F1 := {x}*H = H*{x}; is AS({x}); by TmsS,TmsS1;   // TmsS  := A[a:elg, B:P[elg], {a} * B = a * B];
F2 := x*H = H*x;
   end Proof G0;
  end Proof L2;
 end Proof Tnormal1;

! Tnormal2 := normal(H) == A[x:elg, x*H*inv(x) = H];       // use ! TeqSmr1  := A[x:elg, A,B:P[elg], A = B*x == A * inv(x) = B];
 EqProof Tnormal2;
F1 := normal(H);                 by Axnormal;
F2 := A[x:elg, x*H = H*x];       by TeqSmr1(x@F2, x@F2 * H, H);
F3 := A[x:elg, x*H*inv(x) = H];
 end EqProof Tnormal2;
                                                           // F0 := A[x:elg, x*H*inv(x) <: H];
! Tnormal3 := normal(H) == A[x:elg, x*H*inv(x) <: H];      // assume; let h in H; find h1 in H, such that h = x*h1*inv(x); 
 Proof Tnormal3;                 by Deqv; L1 & L2;         // take h1 = inv(x)*h*x; by F0, h1 in H;
L1 := normal(H) -> A[x:elg, x*H*inv(x) <: H]; 
  Proof L1;
F0 := normal(H);                 assume;  by Tnormal2;
F1 := A[x:elg, x*H*inv(x) = H]; 
F2 := A[x:elg, x*H*inv(x) <: H]; is TAdeqIn(F1);          // ! TAdeqIn := A[d, A = B ] -> A[d, A <: B];
  end Proof L1;
L2 := A[x:elg, x*H*inv(x) <: H] -> normal(H); 
  Proof L2;
F0 := A[x:elg, x*H*inv(x) <: H];   assume;
Goal := normal(H);                 by Tnormal2;             // ! Tnormal2 := normal(H) == A[x:elg, x*H*inv(x) = H];
G0 := A[x:elg, x*H*inv(x) = H];    by TAdeqAA; F0 & G1;     // ! TAdeqAA := A[d, A=B] == A[d, A<:B] & A[d, B<:A];
G1 := A[x:elg, H <: x*H*inv(x)];
  Proof G1;
F01 := x in elg;                   assume;
F1 := inv(x)*H*inv(inv(x)) <: H;   is F0(inv(x)); by Tinvinv, TmeSinvIn(x,H,H);
F2 := H <: x*H*inv(x);                // TmeSinvIn := A[x:elg, A:P[elg], B:P[elg], inv(x)*A*x <: B == A <: x*B*inv(x)];
   end Proof G1;
  end Proof L2;
 end Proof Tnormal3;
                                      // TmeSinvIn2 := A[x:elg, A:P[elg], B:P[elg], x*A*inv(x) <: B == A[a:A, x*a*inv(x) in B]];
! Tnormal4 := normal(H) == A[x:elg, h:H, x*h*inv(x) in H];
 EqProof -Tnormal4;
F1 := A[x:elg, h:H, x*h*inv(x) in H];               by TAA2;
F2 := A[x:elg, A[h:H, x*h*inv(x) in H]];            by -TmeSinvIn2;
F3 := A[x:elg, x*H*inv(x) <: H];                    by -Tnormal3;
F4 := normal(H);
 end EqProof -Tnormal4;

! Tnormal5 := normal(H) == lcosets <: rcosets;     // because lcosets  inside subgr means lcosets(H);
 Proof Tnormal5;                                    by Deqv; L1 & L2;
L1 :=  normal(H) -> lcosets <: rcosets;
  Proof L1;
F0 := normal(H);                                    assume; by Axnormal;   // !! Axnormal := normal(H) == A[x:elg, x*H = H*x];
F1 := A[x:elg, x*H = H*x];
G0 := lcosets <: rcosets;                           by AxIn;
G1 := All(X, X in lcosets -> X in rcosets);
   Proof G1;
assume(X);
F2 := X in lcosets;                                 assume; by Llcosetsin; // ! Llcosetsin := X in lcosets == E[g:elg, X = g*H];
F3 := E[g:elg, X = g*H];                            by F1;                 // F1 := A[x:elg, x*H = H*x];       
F4 := E[g:elg, X = H*g];                            by -Lrcosetsin;        // ! Lrcosetsin := X in rcosets == E[g:elg, X = H*g];
F5 := X in rcosets;
   end Proof G1;
  end Proof L1;

L2 :=  lcosets <: rcosets -> normal(H); 
  Proof L2;
F0 := lcosets <: rcosets;                           assume;
G0 := normal(H);                                    by Axnormal;
G1 := A[g:elg, g*H = H*g];
  Proof G1;
F1 := g in elg;                                     assume;              // Goal: g*H = H*g;
F2 := g*H in lcosets;                               is Llcosets2(g);     // Llcosets2 := A[g:elg, g*H in lcosets]; 
F3 := g*H in rcosets;                               is TinIn(F2 & F0);   by Lrcosetsin1;  // TinIn := x in X2 & X2 <: Y2 -> x in Y2;
F4 := Existx(h, (F4a := h in elg)&(F4b := g*H = H*h));                   // Lrcosetsin1 := X in rcosets(H) == Exist(g, g in elg & X = H*g];
F5 := g*H = H*g;                                    is L21(g,h)(F4b);    // ! L21 := A[g,g1: elg, g*H = H*g1 ->g*H = H*g];
   end Proof G1;
  end Proof L2;
 end Proof Tnormal5;

! Tnormal6 := normal(H) == lcosets = rcosets;
 Proof Tnormal6;                                    by Deqv; L1 & L2;
L1 := normal(H) -> lcosets = rcosets;
  Proof L1;
F0 := normal(H);                                    assume; by Tnormal5;
F01 := lcosets <: rcosets;
F02 := A[x:elg, x*H = H*x];                         is Axnormal(F0);
G0 := lcosets = rcosets;                            by Axext; F01 & G1;
G1 := rcosets <: lcosets;                           by AxIn;
G2 := All(X, X in rcosets -> X in lcosets);
   Proof G2;
assume(X);
F03 := X in rcosets;                                assume; by Lrcosetsin; // Lrcosetsin1 := X in rcosets(H) == Exist(g, g in elg & X = H*g];
F1 := Ex[g:elg, F1a:= X = H*g];                      // Ex can occur only in proof scopes; scope(g) = scope(F1) = Proof(G2:...);
F2 := g*H in lcosets;                               is Llcosets2(g);
F3 := g*H = H*g;                                    is F02(g);
F4 := H*g in lcosets;                               is F3(F2); by -F1a;
F5 := X in lcosets;          
   end Proof G2;
  end Proof L1;

L2 := lcosets = rcosets -> normal(H);
  Proof L2;
F0 := lcosets = rcosets;                      assume;
F1 := lcosets <: rcosets;                     is Axext1(F0); by -Tnormal5;   // ! Axext1 := X=Y -> X<:Y;  
F2 := normal(H);
  end Proof L2;
 end Proof Tnormal6;

! Tnormal7 := normal(H) == A[x:elg,y:elg, x*y*inv(x) in H == y in H];  
 Proof Tnormal7;                                    by Deqv; L1 & L2;
L1 := normal(H) -> A[x:elg,y:elg, x*y*inv(x) in H == y in H];
  Proof L1;
F0 := normal(H);                                    assume; by Tnormal4;
F1 := A[x:elg, h:H, x*h*inv(x) in H];
G0 := A[x:elg,y:elg, x*y*inv(x) in H == y in H];
   Proof G0;
F01 := x in elg;                                    assume;
F02 := y in elg;                                    assume;
G1 := x*y*inv(x) in H == y in H;                    by Deqv; L3 & L4;
L3 :=  x*y*inv(x) in H -> y in H;
    Proof L3;
F03 := x*y*inv(x) in H;                             assume;
F2 := inv(x)*(x*y*inv(x))*inv(inv(x)) in H;         is F1(inv(x), x*y*inv(x)); by Associnve;
F3 := y in H;
    end Proof L3;
L4 :=  y in H -> x*y*inv(x) in H;
    Proof L4;
F04 := y in H;                                      assume;
F4 := x*y*inv(x) in H;                              is F1(x,y);
    end Proof L4;
   end Proof G0;
  end Proof L1;

L2 := A[x:elg,y:elg, x*y*inv(x) in H == y in H] ->  normal(H);  
  Proof L2;
F0 := A[x:elg,y:elg, x*y*inv(x) in H == y in H];    assume;
G0 := normal(H);                                    by Tnormal4;
G1 := A[x:elg, h:H, x*h*inv(x) in H];
   Proof G1;
F01 := x in elg;                                    assume;
F02 := h in H;                                      assume;
F1 := x*h*inv(x) in H == h in H;                    is F0(x,h); by F02;
F2 :=  x*h*inv(x) in H == true;                     by Taut((p==true)==p);
F3 :=  x*h*inv(x) in H;
   end Proof G1;
  end Proof L2;
 end Proof Tnormal7;

! Tnormal8 := normal(H) == A[x,y:elg, x*y in H == y*x in H];
 Proof Tnormal8;                                    by Deqv; L1 & L2;
L1 := normal(H) -> A[x,y:elg, x*y in H == y*x in H];
  Proof L1;
F0 := normal(H);                                    assume; by Tnormal7;
F1 := A[x:elg,y:elg, x*y*inv(x) in H == y in H];
G0 :=  A[x,y:elg, x*y in H == y*x in H];
   Proof G0;
F01 := x in elg;                                    assume;
F02 := y in elg;                                    assume;
F2 := x*(y*x)*inv(x) in H == y*x in H;              is F1(x,y*x); by Associnve;
F3 := x*y in H == y*x in H;
   end Proof G0;
  end Proof L1;

L2 := A[x,y:elg, x*y in H == y*x in H] -> normal(H);
  Proof L2;
F0 := A[x,y:elg, x*y in H == y*x in H];             assume;
G0 := normal(H);                                    by Tnormal7;
G1 := A[x:elg,y:elg, x*y*inv(x) in H == y in H];
   Proof G1;
F01 := x in elg;                                    assume;
F02 := y in elg;                                    assume;
F1 := (x*y)*inv(x) in H == inv(x)*(x*y) in H;       is F0(x*y, inv(x)); by Associnve;
F2 :=  x*y*inv(x) in H == y in H;
   end Proof G1;
  end Proof L2;
 end Proof Tnormal8;

]; // subgr :: [   // 3. normal  // now in group ::

isnormal := dcl[<|, fn(subgr#subgr,bool) ];  // H <| K : H is normal in K;
!! Axisnorm := A[H,K:subgr, H<|K == H<:K & A[x:K, x*H = H*x]];

! Tisnormalelg := A[H:subgr, normal(H) == H <| elg];            // !! Axnormal0 := A[H:subgr, normal(H) == A[x:elg, x*H = H*x]];
 EqProof -Tisnormalelg;                                         // ! Axnormal := normal(H) == A[x:elg, x*H = H*x];
F0 := H in subgr;                         assume;               // the absence of assume was discovered !!! 
F01 := H <: elg;                          is LHelg@subgr;       // ! LHelg := H <: elg; 
F1 := H <| elg;                           by Axisnorm;          // !! Axisnorm := H<|K == H<:K & A[x:K, x*H = H*x]; 
F2 := H <: elg & A[x:elg, x*H = H*x];     by F01;              
F3 := true & A[x:elg, x*H = H*x];         by Taut(true & p == p);
F4 := A[x:elg, x*H = H*x];                by -Axnormal0; 
F5 := normal(H);
 end EqProof -Tisnormalelg;

! Tisnormelg := A[H:subgr, H in nsubgr == H <| elg];  by -(Tnormal0@subgr); Tisnormalelg;   // ! Tnormal0 := normal(H) == H in nsubgr;

// <| := F[HK, H<:K & A[x:K, x*H = H*x]]; // *(group) in fn(subgr#subgr, bool) was handled in Rnam as "*(group)" not as a simple name * @ group;
! Tisnorm := <| @ group in fn(subgr#subgr, bool); is typeaxiom;   // because "<|" defined also for sequences, and ron can't resolve the ambiguity  yet; 
// ! Tisnorm_ax := A[HK, Axisnorm];                    // !! Axisnorm := H<|K == H<:K & A[x:K, x*H = H*x]; 
HK :: [    // HK.2                                  // HK := subgr && {K; AxK := K in subgr};

! TisnormHK := H<|K == H<:K & A[x:K, x*H = H*x];    is Axisnorm;


// ! L08 := H/\K in subgr;                          by TIcomm;    // TIcomm := X/\Y = Y/\X;
// ! L08a := K/\H in subgr;
// ! L15 := H <: H*K;          // because {e} <: K;
// ! L16 := [H, H*K] in HK;
! LHKIn := H <| K -> H <: K;                            is Taut((p == q&r) -> (p->q))(TisnormHK);
// ! LK0 := K <: elg;
// GrK := Gr.K;                                         // subgr :: Gr := [H, *(group)|(H#H)];
// ! L18 := GrK = [K, *_K := *(group)|(K#K)];           is AxGr.K;          // subgr:: ! AxGr := Gr = [H, *(group)|(H#H)];
// ! L19 := elg.GrK = K;                                is Red;             // standard reduction, using isst: F[d,f](z), A[d,P](z), Q.M, ... 
// *_eS_K := *@meS.GrK;
// ! L20_type := *_eS_K in fn(K # P[K], P[K]);          is TmeSt.GrK;       // ! TmeSt := *(mlteS) in fn(elg # P[elg], P[elg]);
// *_Se_K := *@mSe.GrK;
// ! L21_type := *_Se_K in fn(P[K] # K, P[K]);          is TmSet.GrK;       // ! TmSet := *(mltSe) in fn(P[elg] # elg, P[elg]);
// *_K := *(group).GrK;                              // very simple dot term, can be replaced with *(group)|(K#K)
// ! L22_type := *_K in fn(K#K,K);
// ! L22a := *_K = *(group)|(K#K);                      is Red;

! L22 := H <: K -> (G22 := A[x:K, x *_eS_K H = x * H]);
 Proof L22;
F0 := H <: K;                                        assume;            // *_K := *(group)|(K#K);
F01 := A[a:K, B:P[K], a *_eS_K B = R[b:B, a *_K b]]; is TmeS.GrK;       // TmeS := A[a:elg, B:P[elg], a * B = R[b:B, a*b]];
F02 := A[x,y:K, x *_K y = x * y];                    is TGrm.K;         // TGrm := A[x,y:G, x *_Gr y = x * y]
  EqProof G22;
F0 := x in K;                                        assume;            // *_Gr := *(group)|(H#H); ??? assume not needed ???
F1 := x *_eS_K H;                                    by F01;      
F2 := R[h:H, x *_K h];                               by F02;            // *(group).GrK was replaced with *(group)|(K#K), eqt must check!!!
F3 := R[h:H, x * h];                                 by -TmeS;          // but Gr.K =  was NOT replaced with *(group)|(K#K) !!!
F4 := x * H;                                                            // Solution: eqt must check case: simple dotterm like *(group).Grk
  end EqProof G22;
 end Proof L22;

! L23 := H <: K -> (G23 := A[x:K, H *_Se_K x = H * x]);   
 Proof L23;
F0 := H <: K;                                        assume;
F01 := A[A:P[K],b:K, A *_Se_K b = R[a:A, a *_K b]]; is TmSe.GrK;        // group :: ! TmSe := A[A:P[elg], b:elg, A * b = R[a:A, a*b]];
F02 := A[x,y:K, x *_K y = x * y];                    is TGrm.K;         // TGrm := A[x,y:G, x *_Gr y = x * y];
  EqProof G23; 
F0 := x in K;                                        assume;                 // *_Gr := *(group)|(H#H); ??? assume not needed ???
F1 := H *_Se_K x;                                    by F01;      
F2 := R[h:H, h *_K x];                               by F02;            // *(group).GrK was replaced with *(group)|(K#K), eqt must check!!!
F3 := R[h:H, h * x];                                 by -TmSe;          // but Gr.K =  was NOT replaced with *(group)|(K#K) !!!
F4 := H * x;                                                            // Solution: eqt must check case: simple dotterm like *(group).Grk
  end EqProof G23;
 end Proof L23;
                                                                        // !! Axnormal0 := A[H:subgr, normal(H) == A[x:elg, x*H = H*x]];
! L26 := H <: K -> (normal.GrK(H) == A[x:K, x * H = H * x]);  // ??? is (Axnormal0.GrK)(H);
 Proof L26;                                                          // subgr :: ! Axnormal := normal(H) == A[x:elg, x*H = H*x];
F0 := H <: K;                                        assume; by -L25;
F01 := H in subgr.GrK;  
! F02 := subgr.GrK <: P[K];               
F1 := A[H:subgr.GrK, normal.GrK(H) == A[x:K, x *_eS_K H = H *_Se_K x]];  is Axnormal0.GrK;
F2 := normal.GrK(H) == A[x:K, x *_eS_K H = H *_Se_K x];                  is F1(H); by L22(F0), L23(F0);    // *_eS_K := *@meS.GrK;
F3 := normal.GrK(H) == A[x:K, x * H = H * x];
 end Proof L26;

! L27 := H <| K == H <: K & normal.GrK(H);      // GrK := Gr.K
 EqProof -L27;
F1 :=  H <: K & normal.GrK(H);                  by  L26;  // CHECK !!! MUST BE WRONG !!! 5.10.20
F2 := H<:K & A[x:K, x*H = H*x];                 by -Axisnorm;
F3 := H <| K;
 end EqProof -L27;

! TnormalI := normal(H) & normal(K) -> normal(H/\K);      // x*(H/\K) = (x*H) /\ (x*K) = (H*x) /\ (K*x) = (H/\K)*x; // use LMeS,Axnormal,LMeSU1; 
 Proof TnormalI;
F0 := normal(H);                              assume; by Axnormal;     // !! Axnormal := normal(H) == A[x:elg, x*H = H*x];
F01 :=  A[x:elg, x*H = H*x];
F02 := normal(K);                             assume; by Axnormal.K;
F03 :=  A[x:elg, x*K = K*x];
G1 := normal(H/\K);                           by Axnormal.(H/\K);
G2 := A[x:elg, x*(H/\K) = (H/\K)*x];
  EqProof G2;
F00 := x in elg;                              assume;
F1 := x*(H/\K);                               by LmeSI; // ! LmeSI := A[a:elg, B:P[elg], C:P[elg], a * (B/\C) = (a*B) /\ (a*C)]; 
F2 := (x*H) /\ (x*K);                         by F01, F03;
F3 := (H*x) /\ (K*x);                         by -LmSeI; // ! LmSeI := A[B:P[elg], C:P[elg], a:elg, (B/\C)*a = (B*a) /\ (C*a)];  
F4 := (H/\K)*x;
  end EqProof G2;
 end Proof TnormalI;

! L04 := A[x:K, x*H*inv(x) <: H] == A[x:K, x*H*inv(x) = H];  
 Proof L04;               by Deqv; L1 & L2;
L1 := A[x:K, x*H*inv(x) <: H] -> A[x:K, x*H*inv(x) = H];
  Proof L1;
F0 := A[x:K, x*H*inv(x) <: H];                              assume;
G1 := A[x:K, x*H*inv(x) = H];
   Proof G1; 
F00 := x in K;                                              assume;
F0a := A[x: K, inv(x) in K];                                is LHinv.K;     // ! LHinv := A[x: H, inv(x) in H];
F01 := inv(x) in K;                                         is F0a(x); 
F02 := x*H*inv(x) <: H;                                     is F0(x);
F03 := inv(x)*H*inv(inv(x)) <: H;                           is F0(inv(x)); by Tinvinv, TmeSinvIn;
F04 := H <: x*H*inv(x);           // ! TmeSinvIn := A[x:elg, A:P[elg], B:P[elg], inv(x)*A*x <: B == A <: x*B*inv(x)];
G2 := x*H*inv(x) = H;                                       by Axext; F02 & F04;    // ! Axext := X = Y == X <: Y & Y <: X; 
   end Proof G1;
  end Proof L1;
L2 := A[x:K, x*H*inv(x) = H] -> A[x:K, x*H*inv(x) <: H];    is TAdeqIn;     // ! TAdeqIn := A[d, A = B ] -> A[d, A <: B];
 end Proof L04;

// !! Axisnorm := H<|K == H<:K & A[x:K, x*H = H*x];   //  byeq Red;     // <| := F[HK, H<:K & A[x:K, x*H = H*x]];

! L05 := A[x:K, x*H = H*x] == A[x:K, h:H, x*h*inv(x) in H];
 EqProof -L05;
F1 := A[x:K,h:H, x*h*inv(x) in H];             by TAA2;
F2 := A[x:K, A[h:H, x*h*inv(x) in H]];         by L11;   // ! L11 := A[x:elg, A[h:H, x*h*inv(x) in H] == x*H*inv(x) <: H];
F3 := A[x:K, x*H*inv(x) <: H];                 by L04;   // ! L04 := A[x:K, x*H*inv(x) <: H] == A[x:K, x*H*inv(x) = H];  
F4 := A[x:K, x*H*inv(x) = H];                  by -L12;  // ! L12 := A[x:elg, x*H=H*x == x*H*inv(x)=H ];
F5 := A[x:K, x*H = H*x];
 end EqProof -L05;

! Tisnorm0 := H<|K == H<:K & A[x:K,h:H, x*h*inv(x) in H]; by -L05; TisnormHK;

! Tisnorm1 := H<|K == H in nsubgr.GrK;
 EqProof -Tisnorm1;
F1 := H in nsubgr.GrK;                         by Axab;   // nsubgr := {N ; AxN0 := N in subgr; AxN1 := normal(N)};
F2 := H in subgr.GrK & normal.GrK(H);          by L25;    // ! L25 := H in subgr.GrK == H <: K;
F3 := H <: K & normal.GrK(H);                  by -L27;   // ! L27 := H <| K == H <: K & (normal.GrK)(H);
F4 := H<|K;
 end EqProof -Tisnorm1; 

// ! Tisnorm2 := H <| K == H<:K & normal(Gr.K, H);
! Tisnorm4 := normal(H) & H <: K -> H <| K;    // H <: K <: elg; use Axisnorm, TInAA: from A[x:elg, x*H = H*x] follows A[x:K, x*H = H*x];
 Proof Tisnorm4;
F0 := normal(H);                               assume; by Axnormal;     //  Axnormal := normal(H) == A[x:elg, x*H = H*x];
F01 := A[x:elg, x*H = H*x];
F02 := H <: K;                                 assume;  
G1 :=  H <| K;                                 by TisnormHK; F02 & G2;   // TisnormHK := H<|K == H<:K & A[x:K, x*H = H*x]; 
G2 := A[x:K, x*H = H*x];                       is TInAA(LKelg & F01); // ! TInAA := A <: B & A[x:B, P(x)] -> A[x:A, P(x)];
 end Proof Tisnorm4;                           // ! LKelg := K <: elg;                 is LHelg.K;   // was LK2;

! Tisnorm4a := normal(H)->(H <: K -> H <| K);  by Taut( (p->(q->r)) == (p&q ->r) ); Tisnorm4;
 
! L06 := normal(H) -> H*K in subgr;            // because K*H = H*K and Tsbgmlt;
 Proof L06;                                    // Tnormal1 := normal(H) == (AS := A[S:P[elg], SHS := S*H = H*S]); 
F0 := normal(H);                               assume; by Tnormal1;
F01 := A[S:P[elg], S*H = H*S];
F1 := K*H = H*K;                               is F01(K); by Axsym;  // !! Axsym := u=v == v=u;
F2 := H*K = K*H;                               by -Tsbgmlt;          // ! Tsbgmlt := H*K in subgr == H*K = K*H; 
F3 := H*K in subgr;
 end Proof L06;

! Tisnorm5 := normal(H) -> H <| H*K;           // because H <: H*K <: elg; use Tisnorm4: K = K*H;
 Proof Tisnorm5;
F0 := normal(H);                               assume;
// M := [H, H*K];
F1 := H <: H*K;                                is LsbgInm;  // ! LsbgInm := H <: H*K;          // because {e} <: K;
F2 := H <| H*K;                                is Tisnorm4(H, H*K)(F0 & F1);        // ! Tisnorm4 := normal(H) & H <: K -> H <| K;
 end Proof Tisnorm5;
 
// Let G be a group. https://proofwiki.org/wiki/Intersection_with_Normal_Subgroup_is_Normal
// Let K be a subgroup of G, and let H be a normal subgroup of G.   H=>K, N=>H
// Then KnH is a normal subgroup of K.  ----------------------------K/\H <| K;      // ??? Tnormal0.H: was also an error;

! Tisnorm6 := normal(H) -> (H/\K) <| K;   // for another proof see ! Lg6 := (H/\N) <| H;  // ker(canhom(N)|H)=H/\N; ??? there is a simpler proof!
 Proof Tisnorm6;                          // ??? Tnormal0(H): was an error.       
F0 := normal(H);                           assume; by Tnormal4;      // ! Tnormal4 := normal(H) == A[x:elg, h:H, x*h*inv(x) in H];
F01 := A[x:elg, h:H, x*h*inv(x) in H];                                               
G0 := (H/\K) <| K;                        by Tisnorm0(H/\K,K); G1 & G2; // ! Tisnorm0 := H<|K == H<:K & A[x:K,h:H, x*h*inv(x) in H];
G1 := (H/\K) <: K;                        is TIIn2;                 // ! TIIn2 := X/\Y <: Y; 
G2 := A[x:K,z:H/\K, x*z*inv(x) in H/\K];
  Proof G2;
F02 := x in K;                            assume;                   //  ! LKelg := K <: elg;
F03 := x in elg;                          is TinIn(F02 & LKelg);    // ! TinIn := x in X2 & X2 <: Y2 -> x in Y2; 
F04 := z in H/\K;                         assume; by AxI; F1 & F2;  // !! AxI := a in X1/\Y1 == a in X1 & a in Y1;
F1 := z in H;
F2 := z in K;
G3 := x*z*inv(x) in H/\K;                 by AxI; G4 & G5;
G4 := x*z*inv(x) in H;                    is F01;  // F01(x,z);          
G5 := x*z*inv(x) in K;                    is LKinv2;                // ! LKinv2 := A[x,y: K, x*y*inv(x) in K];
  end Proof G2;
 end Proof Tisnorm6;

]; // HK :: [ // HK.2

! Tisnorm0A := A[H,K:subgr, H<|K == H<:K & A[x:K,h:H, x*h*inv(x) in H]]; is Tisnorm0@HK;
! Tisnorm1A := A[H,K:subgr, H<|K == H in nsubgr.(Gr.K)];                 is Tisnorm1@HK;    // GrK := Gr.K;
! Tisnorm4A := A[H,K:subgr, normal(H) & H <: K -> H <| K]; is Tisnorm4@HK; by Tnormal0@subgr;  // HK :: ! Tisnorm4 := normal(H) & H <: K -> H <| K;
! Tisnorm4A1 := A[H,K:subgr, H in nsubgr & H <: K -> H <| K];              // ! Tnormal0 := normal(H) == H in nsubgr;           

HK1 := HK && (AxHK1 := H <: K);
HK1 :: [
dcl[rcosets, fn(subgr#subgr, P[P[elg]]) ];
dcl[lcosets, fn(subgr#subgr, P[P[elg]]) ];
dcl[cosets, fn(subgr#subgr, P[P[elg]]) ];

!! Axrcosets := rcosets(K,H) = R[x:K, H*x];
!! Axlcosets := lcosets(K,H) = R[x:K, x*H];                     // Gr := [H, *(group)|(H#H)];  // Gr := Gr(H)
                                                                // ! Taut30 := (p==q)&q -> p;  // AxHK1 := H <: K;
! LHK1_H :=  H in subgr.GrK;             is Taut30(L25 & AxHK1);   // HK :: ! L25 := H in subgr.GrK == H <: K;      
! LHK1_0 := K in subgr.GrK == K <: K;    is L25(K,K); by TInrefl, Taut((p==true)==p);  // ! TInrefl := X <: X;
! LHK1_K := K in subgr.GrK;                                     // line 8114, not 8118;
! LHK1_PK := H in P[K];                  by AxP; AxHK1;         // !! AxP := Z in P[Y] == Z <: Y;
                                                                // group :: HK := subgr && {K; AxK := K in subgr};
! LHK1_1 := H <|.GrK K == H <| K;                                   // group :: !! Axisnorm := A[H,K:subgr,H<|K == H<:K & A[x:K, x*H = H*x];
 EqProof LHK1_1;                                                    // ! L23 := H <: K -> A[x:K, H *_Se_K x = H * x];  
F01 := A[H,K:subgr.GrK, H <|.GrK K == H <: K & A[x:K, x *_eS_K H = H *_Se_K x]]; is Axisnorm.GrK; // ! Tisnorm_ax := A[HK, Axisnorm];
// F01 := H <|.GrK K == H <: K & A[x:K, x *_eS_K H = H *_Se_K x];  is Axisnorm.GrK; // !! Axisnorm := A[H,K:subgr, H<|K == H<:K & A[x:K, x*H = H*x];
F02 := A[x:K, x *_eS_K H = x * H];          is L22(AxHK1);      // *_eS_K := *@meS.GrK;  // GrK := Gr.K;
F03 := A[x:K, H *_Se_K x = H * x];          is L23(AxHK1);      // *_Se_K := *@mSe.GrK;  // Gr := [H, *(group)|(H#H)];;
F0 := H <|.GrK K == H <: K & A[x:K, x *_eS_K H = H *_Se_K x];   is F01(H,K); // group :: !! Axisnorm := A[H,K:subgr,H<|K == H<:K & A[x:K, x*H = H*x]
F1 := H <|.GrK K;                                               by F0;
F2 := H <: K & A[x:K, x *_eS_K H = H *_Se_K x];                 by F02,F03;
F3 := H <: K & A[x:K, x*H = H*x];                               by -Axisnorm;
F4 := H <| K;
 end EqProof LHK1_1;
]; // end HK1 :: [

HKL := HK && {L;  AxL := L in subgr};          // HKL := {H,K,L ; AxH := H in subgr, AxK := K in subgr, AxL := L in subgr};
HKL :: [
! L01 := L <: elg;
// ! L1 := K/\H in subgr;                      // HK :: ! TsbgI := H/\K in subgr; ! TsbgI1 := K/\H in subgr;
// ! L2 := H in P[elg];                        // subgr :: ! LH1 := H in P[elg];
M := [L,H];
M1 := [L,K];                                   // AxL := L in subgr;     // HK := subgr && {K; AxK := K in subgr};
! L3_type := M in HK;                          by Axab,Axab; AxL & AxH;  // H in {K; K in subgr} == H in subgr;
! L4_type := M1 in HK;                         by Axab,Axab; AxL & AxK; 
! L0 := L/\H in subgr;                         is TsbgI.M;               // moved from the beginning of HKL: did not work there;
! L1 := L/\H <: elg;                           is Tsubgr2(L0);           // group :: ! Tsubgr2 := H in subgr -> H <: elg;
! L2 := K/\H <: elg;                           is Tsubgr2(TsbgI1);       // HK :: ! TsbgI1 := K/\H in subgr;

! Tisnorm3 :=  L <| H & L <: K & K <: H -> L <| K;   // L <| H & between(L,K,H) -> L <| K;
 Proof Tisnorm3;
F0 := L <| H;                                  assume; by TisnormHK.M; F01 & F02; // !! Axisnorm := A[H,K:subgr, H<|K == H<:K & A[x:K, x*H = H*x]; 
F01 := L <: H;
F02 := A[x:H, x*L = L*x];
F03 := L <: K;                                 assume;
F04 := K <: H;                                 assume;
G0 := L <| K;                                  by TisnormHK.M1; F03 & G1;
G1 := A[x:K, x*L = L*x];                       is TInAA(F04 & F02);  // ! TInAA := A <: B & A[x:B, P(x)] -> A[x:A, P(x)];
 end Proof Tisnorm3;

! Tisnorm7 := L<|K  -> L/\H <| K/\H;
 Proof Tisnorm7;                               // Tisnorm0 := H<|K == H<:K & A[x:K,h:H, x*h*inv(x) in H];
// ! [L,K] in HK;
// F0 := L <| K == L<:K & A[x:K,y:L, inv(x)*y*x in L]; is Tisnorm0.[L,K];
F00 := L <| K;                                 assume; by Tisnorm0(L,K); F01 & F02; // was by F0;
F01 := L <: K;                                 
F02 := A[x:K,y:L, x*y*inv(x) in L];
// ! M in HK;
// F03 := G1 == F1 & G2;                       is Tisnorm0.M;
G1 := L/\H <| K/\H;                            by Tisnorm0(L/\H,K/\H); F1 & G2;   // by F03; 
F1 := L/\H <: K/\H;                            is TImr(F01);    //  TImr := X1 <: X2 -> X1/\B <: X2/\B;
G2 := A[x:K/\H, y:L/\H, x*y*inv(x) in L/\H];
  Proof G2;
M0 := x in K/\H;                               assume; by AxI; M01 & M02;  // AxI := a in X1/\Y1 == a in X1 & a in Y1;
M01 := x in K;
M02 := x in H;
M00 := y in L/\H;                              assume; by AxI; M03 & M04;
M03 := y in L;
M04 := y in H;
G3 := x*y*inv(x) in L/\H;                      by AxI; G3a & G3b;
G3a := x*y*inv(x) in L;                        is F02(x,y);
G3b := x*y*inv(x) in H;                        is LHinv2(x,y);  // subgr :: ! LHinv2 := A[x,y: H, x*y*inv(x) in H];
  end Proof G2;
 end Proof Tisnorm7;
   
];  // HKL :: [

! Tisnorm8 := elg <| elg;                                      // HK :: !! Axisnorm := A[H,K:subgr, H<|K == H<:K & A[x:K, x*H = H*x];       
 Proof Tisnorm8;                               by Axisnorm(elg,elg);  F1 & F2;    
F1 := elg <: elg;                              is  TInrefl;     // ! TInrefl := X <: X;  
F2 := A[x:elg, x*elg = elg*x];                 by Telgm1,Telgm2; //  Telgm1 := A[a:elg, a * elg = elg]; ! Telgm2 := A[a:elg, elg * a = elg];
F3 := A[x:elg, elg = elg];                     is Taut;         
 end Proof Tisnorm8;
                     
! Tisnorm9 := {e} <| elg;
 Proof Tisnorm9;                               by Axisnorm({e},elg);  F1&F2;  // group :: !! Axisnorm := A[H,K:subgr,H<|K == H<:K & A[x:K, x*H = H*x];       
F1 := {e} <: elg;                              is L03a;     // ! L03a := {e] <: elg;  
F2 := A[x:elg, x*{e} = {e}*x];                 by Lxe, Lex; // ! Lxe := A[x:elg, x * {e] = {x}]; ! Lex := A[x:elg, {e} * x = {x}];
F3 := A[x:elg, {x} = {x}];                     is Taut;         
 end Proof Tisnorm9;

]; // group :: [                 // 4 normal, <| ;  // dcl[<|,fn(subgr#subgr,bool) ];

 group :: [                      // 5 nsubgr              // next line: 8199, not 8203;      // ! TP1InPelg := P1[elg] <: P[elg];
nsubgr := {N ; AxN0 := N in subgr; AxN1 := normal(N)};    // not using subgr && normal(H) because we want use the name N for normal subgroup;
! Tnsubgr1 := nsubgr <: subgr;                            by AxIn, Axab; is Taut;            // AxIn := X2 <: Y2 == All(x, x in X2 -> x in Y2);      
! Tnsubgr2 := nsubgr <: P1[elg];                          is TInIn(Tnsubgr1 & Tsubgr3);      // TInIn := X0 <: Y0 & Y0 <: Z0 -> X0 <: Z0;
! Tnsubgr2a := nsubgr <: P[elg];                          is TInIn(Tnsubgr2 & TP1InPelg);    // ! Tsubgr3b := subgr <: P[elg]; 
! Tnsubgrin := A[H:subgr, H in nsubgr == normal(H)];      by Axab,2, Bred; is Taut;          // ! Tsubgr3 := subgr <: P1[elg];
// All(H, H in subgr -> H in subgr & normal(H));  is Taut;  // ! TInIn := X0 <: Y0 & Y0 <: Z0 -> X0 <: Z0; ??? did not work: 
//! L06 := subgr <: P[elg];   is TInIn(Tsubgr3 & TP1inP);   // ! Tsubgr3 := subgr <: P1[elg]; // ! TP1inP := P1[Y] <: P[Y];
! Tnsubgre := {e} in nsubgr; by Tnsubgrin;  Lnormale@subgr;    // subgr :: ! Lnormale := normal({e});
! Tnsubgr3 := A[H,K:subgr, H in nsubgr & H<:K -> H <| K];   by Tnsubgrin; Tisnorm4A; // ! Tisnorm4A := A[H,K:subgr, normal(H) & H <: K -> H <| K];
! TN7 := All(K, Goal := K in nsubgr == K in subgr & A[x:elg, z:K, x*z*inv(x) in K]);
 Proof TN7;                                  // EqProof did not work;
assume(K);
Goal @ TN7;                                    by Deqv; L1 & L2;
L1 := K in nsubgr -> K in subgr & A[x:elg, z:K, x*z*inv(x) in K];
  Proof L1;
F0 := K in nsubgr;                             assume; by Axab;
F1 := K in subgr & normal(K);                  by Tnormal4.K;   // Tnormal4 := normal(H) == A[x:elg, h:H, x*h*inv(x) in H];
F2 := K in subgr & A[x:elg, k:K, x*k*inv(x) in K];
  end Proof L1;
L2 := K in subgr & A[x:elg, z:K, x*z*inv(x) in K] -> K in nsubgr;
  Proof L2;
F0 := K in subgr;                             assume;
F01 := A[x:elg, z:K, x*z*inv(x) in K];        assume; 
G1 := K in nsubgr;                            by Axab; F0 & G2;
G2 := normal(K);                              by Tnormal4.K; F01;
  end Proof L2;
 end Proof TN7;
                                             // !! Axconj := A[x,y:elg, conj(x,y) = x*y*inv(x)];
! TN7a := All(K, K in nsubgr == K in subgr & A[x:elg,z:K, conj(x,z) in K]);  by Axconj;  TN7;   // ??? Make TN7 (main) ???
                                              // ! Tnsubgrin := A[H:subgr, H in nsubgr == normal(H)];
! TN8 := All(K, Goal := K in nsubgr == K in subgr & A[x:elg, x*K*inv(x) = K]);  
 Proof TN8;
assume(K);
Goal @ TN8;                                    by Deqv; L1 & L2;
L1 := K in nsubgr -> K in subgr & A[x:elg, x*K*inv(x) = K];
  Proof L1;
F0 := K in nsubgr;                             assume; by Axab;
F1 := K in subgr & normal(K);                  by Tnormal2.K;      // ! Tnormal2 := normal(H) == A[x:elg, x*H*inv(x) = H];
F2 := K in subgr & A[x:elg, x*K*inv(x) = K];
  end Proof L1;
L2 := K in subgr & A[x:elg, x*K*inv(x) = K] -> K in nsubgr;
  Proof L2;
F0 := K in subgr;                             assume;
F01 := A[x:elg, x*K*inv(x) = K];              assume; 
G1 := K in nsubgr;                            by Axab; F0 & G2;
G2 := normal(K);                              by Tnormal2.K; F01;
  end Proof L2;
 end Proof TN8;

! TN9 := A[x:elg, N: nsubgr, x*N = N*x];       // ! Axnormal := normal(H) == A[x:elg, x*H = H*x];
 Proof TN9;
F0 := x in elg;                               assume;
F01 := N in nsubgr;                           assume; by -(Tnormal0@subgr);   // ! Tnormal0 := normal(H) == H in nsubgr;
F02 := normal(N);                             by  Axnormal0;                  // group ::!! Axnormal0 := A[H:subgr, normal(H) == A[x:elg, x*H = H*x]]
F1 := A[x:elg, x*N = N*x];
F2 := x*N = N*x;                              is F1;
 end Proof TN9;  

// dcl[CS, fn(nsubgr, P[P[elg]]) ];        

nsubgr :: [                                   // nsubgr := {N ; AxN0 := N in subgr; AxN1 := normal(N)}; 
! Tnsubgr0 := N in nsubgr.G;                                         // group :: G := [elg, *(group)]; 
! L0 := N <: elg;                             is LHelg.N; by -AxP;   // subgr :: ! LHelg := H <: elg;   
! LNinPelg := N in P[elg];                                           // !! AxP := Z in P[Y] == Z <: Y;
! L00 := N in nsubgr;                         by Axab; AxN0 & AxN1;
! L00a := normal(N) == A[S:P[elg], S*N = N*S]; is Tnormal1.N  ; // because Tnormal1 has internal labels ???
! TN0 := A[x:elg, x*N = N*x];                 is Axnormal.N(AxN1); // subgr :: ! Axnormal := normal(H) == A[x:elg, x*H = H*x];
! TN1 := A[S:P[elg], S*N = N*S];              is L00a(AxN1); // subgr :: Tnormal1 := normal(H)==(AS := A[S:P[elg], SHS := S*H = H*S]);
! TN2 := A[x:elg, x*N*inv(x) = N];            is Tnormal2.N(AxN1); // subgr :: ! Tnormal2 := normal(H) == A[x:elg, x*H*inv(x) = H];
! TN3 := A[x:elg, h:N, x*h*inv(x) in N];      is Tnormal4.N(AxN1);                        // $$$ more: find )(

! TN4 := A[x:elg, h:N, (inv(x)*h)*x in N]; 
 Proof TN4;
F0 := x in elg;                            assume;
F01 := h in N;                             assume;
F02 := inv(x)*h*inv(inv(x)) in N;          is TN3(inv(x),h); by Tinvinv;  // Tinvinv := A[x:elg, inv(inv(x)) = x];
F1 := (inv(x)*h)*x in N; 
 end Proof TN4;

! TN5 := N <| elg;                         by Tisnorm0(N,elg); L0 & TN3; // ! Tisnorm0 := H<|K == H<:K & A[x:K,h:H, x*h*inv(x) in H]; 
! TN6 := lcosets.N = rcosets.N;            is Tnormal6.N(AxN1);          // ! Tnormal6 := normal(H) == lcosets = rcosets;     // $$$
                                                                         // ! AxN1 := normal(N), see nsubgr :=
! LN6r := A[g1,g2:elg, (N*g1) * (N*g2) = N * (g1*g2)];
 EqProof LN6r;
F0 := g1 in elg;                             assume;
F01 := g2 in elg;                            assume;
F1 := (N*g1) * (N*g2);                       by Associnve; 
F2 := N*(g1*N)*g2;                           by TN0(g1);            // ! TN0 := A[x:elg, x*N = N*x];             
F3 := N*(N*g1)*g2;                           by Associnve;
F4 := (N*N)*(g1*g2);                         by LH6.N;              // ! LH6 := H * H = H;  
F5 := N * (g1*g2);  
 end EqProof LN6r;

! LN6l := A[g1,g2:elg, (g1*N) * (g2*N) = (g1*g2) * N];
 EqProof LN6l;
F0 := g1 in elg;                             assume;
F01 := g2 in elg;                            assume;
F1 := (g1*N) * (g2*N);                       by Associnve; 
F2 := g1*(N*g2)*N;                           by -TN0(g2);           // ! TN0 := A[x:elg, x*N = N*x];             
F3 := g1*(g2*N)*N;                           by Associnve;
F4 := (g1*g2)*(N*N);                         by LH6.N;              // ! LH6 := H * H = H;  
F5 := (g1*g2) * N;  
 end EqProof LN6l;

! LN7r  := A[g: elg, (N*g) * invS(N*g) = N];
 EqProof LN7r;
F0 := g in elg;                              assume;
F1 := (N*g) * invS(N*g);                     by TinvSmr;            // ! TinvSmr  := A[A:P[elg], b:elg, invS(A*b) = inv(b) * invS(A)];
F2 := (N*g) * (inv(g) * invS(N));            by Associnve;
F3 := N * invS(N);                           by LH4.N, LH6.N;       // ! LH4 := invS(H) = H; // ! LH6 := H * H = H; 
F4 := N;                                 
 end EqProof LN7r;

! LN8l := A[g:elg, invS(g*N) = inv(g) * N];
 EqProof LN8l;
F0 := g in elg;                              assume;
F1 := invS(g*N);                             by TinvSml;            // ! TinvSml  := A[a:elg, B:P[elg], invS(a*B) = invS(B) * inv(a)];                   
F2 := invS(N)*inv(g);                        by LH4.N;              // ! LH4 := invS(H) = H;
F3 := N * inv(g);                            by -TN0;               // ! TN0 := A[x:elg, x*N = N*x];
F4 := inv(g) * N;
 end EqProof LN8l;

! LN10 := A[x:elg, x in x*N];               is LH8l.N;                // ! LH8l := A[g_elg, g in g*H];

! LN9 := A[g,x:elg, g in x*N == x*N=g*N];
 Proof LN9;
F0 :=  g in elg;                            assume;
F01 := x in elg;                            assume;
G0 := g in x*N == x*N=g*N;                  by Deqv; L1 & L2;
L1 := g in x*N -> x*N=g*N;
  Proof L1;
H0 := g in x*N;                             assume;     // ! Llcosetsineq := A[Q1,Q2: lcosets, x:elg, x:in Q1 & x in Q2 -> Q1=Q2];
H01 := A[Q1,Q2: lcosets.N, x:elg, x in Q1 & x in Q2 -> Q1=Q2];     is Llcosetsineq.N;
H02 := A[g:elg, g*N in lcosets.N];          is Llcosets2.N;        // Llcosets2 := A[g:elg, g*H in lcosets];
H03 := x*N in lcosets.N;                    is H02;   
H04 := g*N in lcosets.N;                    is H02;
H1 := g in g*N;                             is LN10;
H2 := x*N=g*N;                              is H01(x*N,g*N,g);      // waHs LlcosetsNI;
  end Proof L1;
L2 := x*N=g*N -> g in x*N;
  Proof L2;
H0 := x*N = g*N;                            assume;
H1 := g in g*N;                             is LN10; by -H0;
H2 := g in x*N;
  end Proof L2;
 end Proof LN9;

! LN9a := A[g,x:elg, x in g*N == x*N=g*N];
 Proof LN9a;
F0 := g in elg;                             assume;
F01 := x in elg;                            assume;
F1 := x in g*N == g*N=x*N;                  is LN9(x,g); by Axsym;  // !! Axsym := u=v == v=u;
f2 := x in g*N == x*N=g*N;
 end Proof LN9a;

! LN11 := A[g:elg, {x:elg; x*N = g*N} = g*N];
 EqProof LN11;
F0 := g in elg;                             assume;
F01 := g*N <: elg;                          is typeaxiom;
F02 := {x:elg; x in g*N} = g*N;             is TInab6(F01);     // !! TInab6 := B <: t -> {x:t; x in B} = B;
F1 := {x:elg; x*N = g*N};                   by -LN9a;
F2 := {x:elg; x in g*N};                    by F02; 
F3 := g*N;
 end EqProof LN11;

! LN12 := A[g,g1: elg, g*N = g1*N -> E[n:N, g1 = g*n]];
 Proof LN12;
F0 := g in elg;                            assume;
F01 := g1 in elg;                          assume;
F02 := g*N = g1*N;                         assume; by -LN9;   // ! LN9 := A[g,x:elg, g in x*N == x*N=g*N];
F1 := g1 in g*N; 
F2 := E[n:N, g1 = g*n];                    is TinmeS(F1);     // !! TinmeS := A[A:P[elg], x,x1:elg, x1 in x*A -> E[a:A, x1 = x*a]];                          
 end Proof LN12;
 
CS := lcosets.N;                          // we are in nsubgr: nsubgr :: [ ...  CS := lcosets.N; ... ];
Q_CS := {Q; Q in CS};                                                  // CS : CoSets, dcl[CS, nsubgr, P[P[elg]] ];
! AxCS := CS = lcosets.N;                 is Axrefl;                   // !! Axrefl := x = x;
! LCSInP := CS <: P[elg];                 by AxCS; is LlcosetsInP.N;   // subgr :: ! LlcosetsInP := lcosetsH <: P[elg];

// ! LCS5 := CS = R[g:elg, N*g];             byeq AxCS, Lrcosets1.N;      // subgr :: Lrcosets1 := rcosets = R[g:elg, H*g]
! LCS1 := CS = rcosets.N;                 byeq AxCS,TN6;               // ! TN6 := lcosets.N = rcosets.N;
! L01a := lcosets.N <: P[elg];            by -AxCS; LCSInP;            // ! LCSInP := CS <: P[elg];
! LCS2 := CS = R[g:elg, g*N];             byeq AxCS, Llcosets1.N;      // subgr :: Llcosets1 := lcosets(H) = R[g:elg, g*H];
! LCSl := A[g:elg, g*N in CS];            by AxCS; is Llcosets2.N;     // subgr :: ! Llcosets2 := A[g:elg, g*H in lcosets(H)];!
! LCSr := A[g:elg, N*g in CS];            by LCS1; is Lrcosets2.N;     // subgr :: ! Lrcosets2 := A[g:elg, H*g in rcosets(H)];
! LCSunion := union(CS) = elg;            is Llcosets6.N;              // ! Llcosets6 := union(lcosets) = elg; // !! Axsym := u=v == v=u; 
! LCSunion0 := elg = union(CS);           by Axsym; LCSunion;          // ! Llcosets7 := A[Q: lcosets, Q ~= {}];
! LCSnemp := A[Q: CS, Q ~= {}];           is Llcosets7.N; by -TAnin;   // !! TAnin := z nin X == A[x:X, x ~= z];
! LCSnemp1 := {} nin CS;    // !  Axneqr := ~(z = z1) == z ~= z1;      // !  TNneq := ~(u ~= v) == u = v;
! LCSNI := A[Q1,Q2:CS, Q1/\Q2 ~= {} -> Q1=Q2]; is LlcosetsNI.N; by CP,Axneqr,TNneq; // ! LrcosetsNI := A[Q1,Q2:rcosets, Q1/\Q2 ~= {} -> Q1=Q2];
! LCSNI1 := A[Q1,Q2: CS, Q1 ~= Q2 -> Q1/\Q2 = {}];                     // ! CP := p->q == ~q -> ~p;

elgCS := [elg,CS];         // !! Tprtin := [A,B] in partition == union(B)=A & A[Q:B, Q ~= {}] & A[Q1,Q2:B,  Q1/\Q2 ~= {} -> Q1=Q2];  
! LCSpart_type := elgCS in partition;     by Tprtin; LCSunion & LCSnemp & LCSNI;

Q_PCS := {Q; AxQ := Q in P[CS] };
// ! LCSP := A[Q_PCS, union(Q) <: elg];      by -LCSunion; is TunionmP; // !! TunionmP := A[A:P[B], union(A) <: union(B)];
Q_PCS :: [
! L0 := Q <: CS;                          is AxP(AxQ);                  // !! AxP := Z in P[Y] == Z <: Y;  
! LCSP := union(Q) <: elg;                by -LCSunion; is Tunionm(L0); // !! Tunionm := A <: B -> union(A) <: union(B); 

! LCSunion1 := A[x: union(Q), x*N in Q];
 Proof LCSunion1;
F0 := x in union(Q);      assume;         by Tunionin;                  // !! Tunionin := x in union(A) == Exist(Y, Y in A & x in Y);
F01 := Existx(X, (F01a := X in Q) & (F01b := x in X));                  //  LCSP := union(Q) <: elg; 
F02 := x in elg;                          is TinIn(F0 & LCSP);
F03 := lcosets.N <: P[elg];               is L01a;    // ??? remove ???
F04 := A[Z: lcosets.N, x1:Z, Z = x1*N];   is Llcosets10.N;              // ! Llcosets10 := A[Q: lcosets, x:Q, Q = x*H];
F1 := X in CS;                            is TinIn(F01a & L0); by AxCS; // TinIn := x in X2 & X2 <: Y2 -> x in Y2;
F2 := X in lcosets.N;                                                   // ! AxCS := CS = lcosets.N; 
F3 := X = x*N;                            is F04(X,x);
F01a;                                     by F3;
F4 := x*N in Q;
 end Proof LCSunion1;
]; // Q_PCS :: [

! LCSin := A[Q_CS, E[g:elg, Q = N*g]];
 Proof LCSin;
F1 :=  X in rcosets.N == E[g:elg, X = N*g]; is Lrcosetsin.N;           // ! Lrcosetsin := X in rcosets(H) == E[g:elg, X = H*g];
F0 := Q in CS;                           assume; by LCS1;              // ! LCS1 := CS = rcosets.N;
F01 := Q in rcosets.N;                   by F1;                        // was by Lrcosetsin.N: ERROR in insteqt: X is con !!!   
F2 := E[g:elg, Q = N*g];
 end Proof LCSin;

! LCS3  := A[Q1,Q2: CS, Q1*Q2 in CS];
 Proof LCS3;
F0 := Q1 in CS;                          assume;  
F01 := Ex[g1:elg, F01a := Q1 = N*g1];    is LCSin(Q1);           // ! LCSin := A[Q:CS(N), E[g:elg, Q = N*g]]; 
F02 := Q2 in CS;                         assume;
F03 := Ex[g2:elg, F03a := Q2 = N*g2];    is LCSin(Q2); 
F04 := g1*g2 in elg;                     is LCL2(g1,g2);         // ! LCL2  := A[x,y:elg, x*y in elg]; 
G0 := Q1*Q2 in CS;                       by F01a,F03a;
G1 := (N*g1)*(N*g2) in CS;               by LN6r(g1,g2);         // ! LN6r := A[g1,g2:elg, (N*g1) * (N*g2) = N * (g1*g2)]
G2 := N*(g1*g2) in CS;                   is LCSr(g1*g2);         // ! LCSr := := A[g:elg, N*g in CS(N)];
//  Was: 
// G0 := Q1*Q2 in CS(N);                        by LCSin1;              // ! LCSin1 := X in CS(N) == E[g:elg, X = N*g];
// G1 := E[g:elg, Q1*Q2 = N*g];                 by F01a,F03a;
// G2 := E[g:elg, (N*g1)*(N*g2) = N*g];         by LN6r(g1,g2);         // ! LN6r := A[g1,g2:elg, (N*g1) * (N*g2) = N * (g1*g2)];
// G3 := E[g:elg, N*(g1*g2) = N*g];             is Witness(g1*g2);      // ??? findtabt did not discovered N*(g1*g2) = N*(g1*g2); ???
 end Proof LCS3;

! LCS4  := A[Q_CS, invS(Q) in CS];
 Proof LCS4;
F0 := Q in CS;                           assume;
F01 := Ex[g:elg, F01a := Q = N*g];       is LCSin(Q);            // ! LCSin := A[Q:CS(N), E[g:elg, Q = N*g]]; 
F02 := inv(g) in elg;                    is LCL1(g);             // ! LCL1  := A[x:elg, inv(x) in elg];
G0 := invS(Q) in CS;                     by F01a;
G1 := invS(N*g) in CS;                   by TinvSmr(N,g);        // ! TinvSmr  := A[A:P[elg], b:elg, invS(A*b) = inv(b) * invS(A)];
G2 := inv(g) * invS(N) in CS;            by LH4.N;               // group :: ! LH4 := invS(H) = H;
G3 := inv(g) * N in CS;                  is LCSl(inv(g));        // ! LCSl := := A[g:elg, g*N in CS(N)];
 end Proof LCS4;
 
! LCSin1 := X in CS == E[g:elg, X = N*g]; by LCS1; is Lrcosetsin.N; // ! LCS1 := CS = rcosets.N; 
! LCSin2 := X in CS == E[g:elg, X = g*N]; by AxCS; is Llcosetsin.N; // ! AxCS := CS = lcosets(N);  
                                                                    // ! Llcosetsin := X in lcosets == E[g:elg, X = g*H];
! LN5   := A[g: elg, N * (g*N) = g*N];      
 EqProof LN5;
F0 := g in elg;                          assume;
F1 := N * (g*N);                         by TN0(g);             // ! TN0 := A[x:elg, x*N = N*x];            
F2 := N * (N*g);                         by Associnve;  
F3 := (N*N) * g;                         by LH6.N;              // ! LH6 := H * H = H; 
F4 := N*g;                               by -TN0(g);
F5 := g*N;                                                      // ! LCSInP := CS <: P[elg]; 
 end EqProof LN5;                                               // ! Taut30 := (p==q)&q -> p;
                                                                                              
invS_CS := invS | CS;                     // !! Tre5 := f in fn(A,A) & B <: A -> (f|B in fn(B,B) == A[x:B, f(x) in B]);              
! L02 := invS_CS in fn(CS,CS) == LCS4;    is Tre5(TinvS_type & LCSInP);   // ! TinvS_type := invS in fn(P[elg],P[elg]);
! LinvS_CS_type := invS_CS in fn(CS,CS);  is Taut30(L02@nsubgr & LCS4);   // ! LCS4  := A[Q_CS, invS(Q) in CS]; ??? L02@this ???
! LCSinv := A[Q_CS,invS_CS(Q) = invS(Q)]; is Tre2(TinvS_type & LCSInP);   // ! Tre2 := f in fn(A,B) & C <: A -> A[x:C, (f|C)(x) = f(x)];

*_CS := *@mSS | (CS # CS);                // !! Tre4 := f in fn(A#A,A) & B <: A -> (f|(B#B) in fn(B#B,B) == A[x,y:B, f(x,y) in B]);           
! AxmCS := *_CS = *@mSS | (CS # CS);      is Axrefl;                    // Axrefl := x = x;
! L03 := *_CS in fn(CS#CS,CS) == LCS3;    is Tre4(TmSSt & LCSInP);      // ! TmSSt := * @ mSS in fn(P[elg] # P[elg], P[elg]); 
! LmCS1_type := *_CS in fn(CS # CS, CS);  is Taut30(L03@nsubgr & LCS3); // ! LCS3  := A[Q1,Q2: CS, Q1*Q2 in CS];
! LCSm := A[Q1,Q2:CS, Q1 *_CS Q2 = Q1*Q2];is Tre6(TmSSt & LCSInP); // ! Tre6 := f in fn(A#A,A) & B <: A -> A[x,y:B, (f|(B#B))(x,y) = f(x,y)];	
! LmCS0 := N in CS;                       is Llcosets3.N;               // ! Llcosets3 := H in lcosets; 
! LCS1r := A[Q_CS, Q *_CS N = Q];         by LCSm, AxCS; is Llcosets9.N;  // subgr :: ! Llcosets9 := A[Q:lcosets, Q*H = Q];;
                                                                        // ! AxCS := CS = lcosets(N); 
! LCS2r := A[Q_CS, Q *_CS invS_CS(Q) = N];
 EqProof LCS2r;                              // Lrcosetsin1 := X in rcosets == Exist(g, g in elg & X = H*g);
F1 := X in rcosets.N == Exist(g, g in elg & X = N*g);          is Lrcosetsin1.N;
F0 := Q in CS;                              assume; by LCS1;   // ! LCS1 := CS = rcosets.N; 
F01 := Q in rcosets.N;                      by F1;             // was by Lrcosetsin1.N: ERROR in insteqt, see Proof LCSin; 
F02 := Existx(g, (F02a := g in elg) & (F02b := Q = N*g));
F2 := Q *_CS invS_CS(Q);                    by LCSm,LCSinv;      
F3 := Q * invS(Q);                          by F02b;
F4 := (N*g)*invS(N*g);                      by LN7r;           // ! LN7r  := A[g: elg, (N*g) * invS(N*g) = N];
F5 := N;
 end EqProof LCS2r;
                                            // ! LCSunion := union(CS) = elg;
Fgr := [CS, *_CS];                          // factor group H/N   // CS := lcosets.N;    
// ! LmCS2a := A[x,y,z: CS, x *(y * z) = (x * y) * z ]; is AssocSSS; // ! AssocSSS := A[A:P[elg],B:P[elg],C:P[elg], A*(B*C) = (A*B)*C];
! LmCS2 := A[x,y,z: CS, x *_CS(y *_CS z) = (x *_CS y) *_CS z ]; by LCSm,LCSm,LCSm,LCSm; is AssocSSS;   // LmCS2a; 
! LmCS3  := E[E:CS, Inv:fn(CS,CS), A[Q_CS, Q *_CS E = Q] & A[Q_CS, Q *_CS Inv(Q) = E]];   is Witness(N,invS_CS); // see LCS1r, LCS2r; 
                   //! LmCS4  := Exist(Inv, Inv in fn(CS,CS) & A[x_CS, x *_CS Inv(x) = N]);   is Witness(invS_CS);
! TFgr_type := Fgr in group;             by Axab; LmCS1_type & LmCS2 & LmCS3;  // ! LCS1r := A[Q_CS, Q *_CS N = Q]; // Fgr := [CS, *_CS]; 

! TFgre := e.Fgr = N;                       //   (nsubgr ::) Fgr := [CS, *_CS];                            
 Proof TFgre;
F1 := A[Z:CS, A[Q_CS, Q *_CS Z = Q] -> e.Fgr = Z];  is TeUnique.Fgr;    // ! TeUnique := A[z:elg, A[x:elg, x * z = x] -> e = z];
F2 :=  A[Q_CS, Q *_CS N = Q] -> e.Fgr = N;          is F1(N);
F3 := e.Fgr = N;                                    is F2(LCS1r);
 end Proof TFgre;

! TFgrinv := inv.Fgr = invS_CS;
 Proof TFgrinv;                                            //  ! TinvUnique := A[f:fn(elg,elg), A[x:elg, x * f(x) = e] -> inv = f];
F1 := A[f:fn(CS,CS), A[Q_CS, Q *_CS f(Q) = N] -> inv.Fgr = f]; is TinvUnique.Fgr;
F2 := A[Q_CS, Q *_CS invS_CS(Q) = N] -> inv.Fgr = invS_CS;     is F1(invS_CS);
F3 := inv.Fgr = invS_CS;                                       is F2(LCS2r);       // ! LCS2r := A[Q_CS, Q *_CS invS_CS(Q) = N];
 end Proof TFgrinv;

! TFgrsubgr := subgr.Fgr <: P[P[elg]];
 Proof TFgrsubgr;                                                       // ! LCSInP := CS <: P[elg];
F1 := subgr.Fgr <: P[CS];                           is Tsubgr3b.Fgr;    // ! Tsubgr3b := subgr <: P[elg]; 
F2 := P[CS] <: P[P[elg]];                           is TPm(LCSInP);     // ! TPm := X1 <: Y1 == P[X1] <: P[Y1]; 
F3 := subgr.Fgr <: P[P[elg]];                       is TInIn(F1&F2);    // ! TInIn := X0 <: Y0 & Y0 <: Z0 -> X0 <: Z0; 
 end Proof TFgrsubgr;
                      // ! Tsubgrin1A := A[V:P[elg], V in subgr == V <: elg & V ~= {} & A[x,y: V, x*y in V] & A[x: V, inv(x) in V]];
! TFgr5 := A[Q: subgr.Fgr, (UQ := union(Q)) in subgr];
 Proof TFgr5;                // ! Tsubgrin1 := V in subgr == V <: elg & V ~= {} & A[x,y: V, x*y in V] & A[x: V, inv(x) in V];
F0 := Q in subgr.Fgr;             assume;  by Tsubgrin1A.Fgr; F01 & F02 & F03 & F05;
F01 := Q <: CS;                   
F02 := Q ~= {};                               // *_CS := *@mSS | (CS # CS);  
F03 := A[X,Y: Q, X *_CS Y in Q];  by LCSm;    // ! LCSm := A[Q1,Q2:CS, Q1 *_CS Q2 = Q1*Q2];
F04 := A[X,Y: Q, X * Y in Q];
F05 := A[X:Q, inv.Fgr(X) in Q];   by TFgrinv, LCSinv;                                                               // $$$
F06 := A[X:Q, invS(X) in Q];                             // !!! F07:REMOVE !!! insert into moddot (ismd)!!! 6.22.21
F07 := Q in Q_PCS;                by Axab,AxP; F01;  // Q_PCS := {Q; AxQ := Q in P[CS] }; !! AxP := Z in P[Y] == Z <: Y;
L1 := UQ <: elg;                  by -LCSunion; is Tunionm(F01); // !! Tunionm := A <: B -> union(A) <: union(B);
H01:= A[x: union(Q), x * N in Q]; is LCSunion1.Q;                  // Q_PCS :: ! LCSunion1 := A[x: union(Q), x*N in Q]; 
H04 := A[z:elg, z*N in B -> z in union(B)];   is LHmunion.N;       // !! LHmunion := A[z:elg, z*H in B -> z in union(B)]

G0 := UQ in subgr;                by  Tsubgrin1; L1 & L2 & L3 & L4;  
L2 := UQ ~= {};                   is Tprt5.elgCS(F01 & F02);       // !! Tprt5 := B1 <: B & B1 ~= {} -> union(B1) ~= {}; $$$ 
L3 := A[x,y: UQ, x*y in UQ];
  Proof L3;
H0 := x in UQ;                    assume;                          // (was Q:subgr.Fgr); 
// H01:= A[x: union(Q), x * N in Q]; is LCSunion1.Q;                  // Q_PCS :: !! LCSunion1 := A[x: union(Q), x*N in Q]; 
H02 := x*N in Q;                  is H01;                          // Q_PCS := {Q; AxQ := Q in P[CS] };         
H03 := y in UQ;                   assume;                            
// H04 := A[z:elg, z*N in B -> z in union(B)];   is LHmunion.N;       // !! LHmunion := A[z:elg, z*H in B -> z in union(B)]
H05 := (x*y)*N in B -> x*y in union(B);       is H04(x*y);
H1 := y*N in Q;                   is H01; 
H2 := (x*N) * (y*N) in Q;         is F04;      by LN6l;            // ! LN6l := A[g1,g2:elg, (g1*N) * (g2*N) = (g1*g2) * N];
H3 := (x*y)*N in Q;                    
G0 := x*y in UQ;                  is H05(H3);        // !! LHmunion := A[z:elg, z*H in B -> z in union(B)]; $$$
// G0 := x*y in UQ;                  is (LHmunion.N)(x*y)(F3);        // !! LHmunion := A[z:elg, z*H in B -> z in union(B)]; $$$
  end Proof L3;

L4 := A[x: UQ, inv(x) in UQ];
  Proof L4;
H0 := x in UQ;                    assume;                          // (was Q:subgr.Fgr); 
// H01:= A[x: union(Q), x * N in Q]; is LCSunion1.Q;                  // Q_PCS :: !! LCSunion1 := A[x: union(Q), x*N in Q]; 
H02 := x*N in Q;                  is H01;                          // Q_PCS := {Q; AxQ := Q in P[CS] };         
// H03 := y in UQ;                   assume;                            
// H04 := A[z:elg, z*N in B -> z in union(B)];   is LHmunion.N;    // !! LHmunion := A[z:elg, z*H in B -> z in union(B)]
H05 := inv(x)*N in B -> inv(x) in union(B);      is H04(inv(x));
// H1 := y*N in Q;                   is H01; 
H2 := invS(x*N) in Q;                is F06;     by LN8l;             // ! LN8l := A[g:elg, invS(g*N) = inv(g) * N];
H3 := inv(x)*N in Q;                    
G0 := inv(x) in UQ;                  is H05(H3);
  end  Proof L4;           
 end Proof TFgr5;
 
                                         // ! Tfgr4 := A[N: nsubgr, Q: P[CS(N)], union(Q) <: elg];  // is Tlcosets6a;  // now LCSP;
// ! L09 := elg in subgr;   // see ! Telg := elg in subgr;
// N_nsubgr := {N; N in nsubgr};
// !! L09 := A[N_nsubgr, N <| elg];      // same as TN5;
 ];  // nsubgr :: [                      // nsubgr := {N ; AxN0 := N in subgr; AxN1 := normal(N)};

// NH := {N,H; AxN*** := N in nsubgr, AxH*** := H in subgr };   // Host = group
NH := nsubgr && subgr;
NH :: [                      // subgr :: ! Tnormal0 := normal(H) == H in nsubgr;   // nsubgr :: ! L00 := N in nsubgr;
GrH := Gr.H;
! LNH_GrH := subgr.GrH <: subgr;        by TGr_H; is LsubgrGr;    // ! LsubgrGr := subgr.Gr <: subgr;  // ! TGr_H := Gr.H = Gr; 
! L0a := H*N = N*H;                     is TN1(H);                // nsubgr :: ! TN1 := A[S:P[elg], S*N = N*S]; 
! L0b := normal(N);                     is Tnsubgrin(N)(L00 @ nsubgr);  // ! Tnsubgrin := A[H:subgr, H in nsubgr == normal(H)];
! L0c := N <: H -> N <| H;              is Tisnorm4a(N,H)(L0b);   // ! Tisnorm4a := normal(H) -> (H <: K -> H <| K);
! L0d := N <| H -> N <: H;              is LHKIn(N,H);            // ! LHKIn := H <| K -> H <: K; 
! L14 := N in nsubgr;                   by Axab; AxN0 & AxN1;     // ! TinIn := x in X2 & X2 <: Y2 -> x in Y2;
! L15 := N in subgr;                    is TinIn(L14 & Tnsubgr1); //  ! Tnsubgr1 := nsubgr <: subgr; 
! L16 := N <: H*N;                      is LsbgInm1@HK;           // !! LsbgInm1 := H <: K*H; 
! L17 := H in subgr;                    is AxH;
! TngrIn1 := N <| H == N <: H;          by Deqv; L0d & L0c;     // ! Deqv := (p==q) == (p->q) & (q->p); // GrK := Gr.K;
// ! L00 := M in HK;                            by Axab; AxN0 & AxH;          
! L0e := N in nsubgr.(Gr.H) == N <: H;  by -Tisnorm1(N,H); TngrIn1; // HK :: ! Tisnorm1 := H<|K == H in nsubgr.GrK;
! TngrIn := N in nsubgr.Gr == N <: H;   by -TGr_H; L0e;         // ! TGr_H := Gr.H = Gr;      
! L0f := N/\H in subgr;                 is TsbgI(N,H);          // ! TsbgI := H/\K in subgr;  // ! Taut30 := (p==q)&q -> p;
! LHNsbg := H*N in subgr;               is Taut30((Tsbgmlt(H,N)\\Red("adt")) & L0a);          // HK :: ! Tsbgmlt := H*K in subgr == H*K = K*H;
! LNnHN := N <| H*N;                    is Tnsubgr3(N,H*N)(L14 & L16);   // ! Tnsubgr3 := A[H:subgr,K:subgr, H in nsubgr && H<:K -> H <: K];

! LNH1 := A[h:H,n:N, (h*n)*N = h*N];          // move to first NH;
 EqProof LNH1;
F0 := h in H;                           assume;
F01 := n in N;                          assume;
F02 := n*N = N;                         is LH2lA(N,n);           // !! LH2lA := A[H:subgr,h:H, h*H = H];   
F1 := (h*n)*N;                          by Associnve;
F2 := h*(n*N);                          by F02;              
F3 := h*N; 
 end EqProof LNH1;

// ! TngrI := N /\ H <| H;                  ??? wrong ???
// Proof TngrI;
// F0 := N/\H <: H;                             is TIIn2;                       // ! TIIn2 := X/\Y <: Y; 
// F1 := N/\H <: H -> N/\H <| H;                is TngrIn1(N/\H,H);
// F2 :=  N/\H <| H;                            is F1(F0);
// end Proof TngrI;

// LngrIin := N /\ H <: N;                           
//            N/\H <| H;   // x in H -> ( x * (N/\H) = x*N /\ x*N = N*x /\ H*x);
]; // NH ::  #1

                                         // Definition of the usual notation H/N
HN := {H,N; AxH := H in subgr, AxN0 := N in subgr; AxN1 := N <| H };     //         N <| H; // AxN := N in nsubgr.(GrH := Gr.H) 
dcl[/, fn(HN, group)];                           // H/N

HN :: [             // #1                                               
! AxN := N in nsubgr.(GrH := Gr.H);            by -Tisnorm1A; AxN1;    // ! Tisnorm1A := A[H,K:subgr, H<|K == H in nsubgr.(Gr.K)];
! L0 := nsubgr.GrH <: subgr.GrH;               is Tnsubgr1.GrH;        // group :: ! Tnsubgr1 := nsubgr <: subgr; 
! L01 := subgr.GrH <: subgr;                   is LsubgrGr.H;          // subgr :: ! LsubgrGr := subgr.Gr <: subgr;
! L02 := nsubgr.GrH <: subgr;                  is TInIn(L0 & L01);     // ! TInIn := X0 <: Y0 & Y0 <: Z0 -> X0 <: Z0;
! L03 := N in subgr;                           is TinIn(AxN & L02);    // ! TinIn := x in X2 & X2 <: Y2 -> x in Y2;
! LHNnorm := N <| H;                           is Tisnorm1(N,H)(AxN);  // HK :: ! Tisnorm1 := H<|K == H in nsubgr.GrK;
! L05 := N <: H;                               is LHKIn(N,H)(LHNnorm); by -AxP;   // HK :: ! LHKIn := H <| K -> H <: K; // !! AxP := Z in P[Y] == Z <: Y;
! L06 := N in P[H];
! L07 := P[H] <: P[elg];                       is LPHelg.H;            // subgr :: ! LPHelg := P[H] <: P[elg];
! L08 := P[H]#P[H] <: P[elg]#P[elg];           is Tdp4(L07);           // !! Tdp4 := A<:B -> A#A <: B#B; 
! L09 := N in P[elg];                          is TinIn(L06 & L07);    // ! TinIn := x in X2 & X2 <: Y2 -> x in Y2;      
! L10 := GrH = [H,*(group)|(H#H)];             is AxGr.H;              // subgr :: ! AxGr := Gr = [H, *_Gr]
! L11 := *@mSS.GrH = *@mSS | (P[H]#P[H]);      is THmSS.H;             // subgr :: ! THmSS := *(mSS).Gr = *(mSS)|(P[H]#P[H]);
! L12 := P[H]#P[H] <: dom(*@mSS);              by TmSSdom; L08;        // ! TmSSdom := dom(* @ mSS) = P[elg] # P[elg];        

CS1 := R[x:H, x*N];                            // TRA := R[d,f] <: B == A[d,f in B]; x*N in P[H];
! L13 := A[x:H, x*N in P[H]];                  is LHAP.H(N); by -TRA;  // ! LHAP := A[K:P[H], A[x:H, x*K in P[H]]];
! L14 := CS1 <: P[H];                                                  // CS1 := R[x:H, x*N];
! L15 := CS1#CS1 <: P[H]#P[H];                 is Tdp4(L14);
! LCS1in :=  A[x:H, x*N in CS1];               is TAinR;               // !! TAinR   := A[d, f in R[d,f]];

*_CS1 := *@mSS|(CS1#CS1);
! AxmCS1 := *_CS1 = *@mSS|(CS1#CS1);           is Axrefl;              //  Axrefl := x = x;
! L16 := *@mSS.GrH | (CS1#CS1) = *_CS1;        byeq L11, Trere;        // !! Trere := A[fAB, f|A|B = f|B]; // fAB: A<:dom(f),B<:A;
! L17 := CS1 <: P[elg];                        is TInIn(L14 & L07);    // ! TInIn := X0 <: Y0 & Y0 <: Z0 -> X0 <: Z0;
! LmCS1_type := *_CS1 in fn(CS1#CS1, P[elg]);  is Tre4a(TmSSt & L17);  // !! Tre4a := f in fn(A#A,B) & C <: A -> f|(C#C) in fn(C#C,B); 
                                              // ! TmSSt := * @ mSS in fn(P[elg] # P[elg], P[elg]);
!! AxFgr := H/N = Fgr.N;                      // group::nsubgr:: Fgr := [CS, *_CS]; // group::nsubgr:: ! TFgr_type := Fgr in group;
! Tfgr_type := H/N in group;                  by AxFgr; is TFgr_type.N; // is TFgr_type(group::nsubgr,GrH,N);  

! Lfgr1 := CS.N = CS1;                            // ! L1 := CS(group::nsubgr,GrH,N) = CS1; 
 EqProof Lfgr1;  
// F1 := CS(group::nsubgr,GrH,N);                by LCS2@nsubgr;        // group :: nsubgr := ! LCS2 := CS = R[g:elg, g*N];  
F1 := CS.N;                                    by LCS2@nsubgr;          // ! LCS2 := CS = R[g:elg, g*N]; // CS.N, ker.g: far dot terms; 
F2 := R[g:elg, g*(N@nsubgr)].N;                by Red("dot");           // used N in nsubgr.H;
F3 := R[g:H, g *@meS.GrH N];                   by LHmeS.H;              // ! LHmeS := A[a:H,B:P[H],  a*(meS).Gr B = a*B];
F4 := R[g:H, g * N];                           // (group::nsubgr,GrH,N): full method terms: not introduced, see F2, also see ker(g);
 end EqProof Lfgr1;        // F2; by Red; HostMod: nsubgr: N, group: GrH; it means, that a group-name elg will be replace with H;

! Lfgr2 := *_CS.N = *_CS1;                        // ! L2 := *_CS(group::nsubgr,GrH,N) = *_CS1;  
 EqProof Lfgr2;
F1 := *_CS.N;                                  by Red("dot");   // *_CS(group::nsubgr,GrH,N);        // *_CS := *@mSS | (CS # CS); 
F2 := (*@mSS.GrH) | (CS.N # CS.N);             by Lfgr1; // (*_mSS|(CS#CS)=
F3 := (*@mSS.GrH) | (CS1 # CS1);               by L16;   // ! L16 := *@mSS.GrH | (CS1#CS1) = *_CS1;
F4 := *_CS1;                                             // *_CS1 := *@mSS|(CS1#CS1);
 end  EqProof Lfgr2;

! Tfgr := H/N = [CS1, *_CS1];                  // CS1 := R[x:H, x*N];
 EqProof Tfgr;
F1 := H/N;                                     by AxFgr;
F2 := Fgr.N;                                   by Red("dot");            // Fgr(group::nsubgr,GrH,N);
F3 := [CS.N, *_CS.N];                          by Lfgr1,Lfgr2;     // CS(group::nsubgr,GrH,N)
F4 := [CS1, *_CS1];
 end EqProof Tfgr;                             
                                               // nsubgr :: ! TFgre := e.Fgr = N;   //   (nsubgr ::) Fgr := [CS, *_CS];
! Tfgrelg := elg.(H/N) = CS1;                  byeq Red;             // HN :: CS1 := R[x:H, x*N]; we are in HN;
! Tfgrin := A[x:H, x*N in elg.(H/N)];          by Tfgrelg; LCS1in;   // ! LCS1in :=  A[x:H, x*N in CS1];
                                               // Tfgrin was in wrong place: before ! Tfgr := H/N = [CS1, *_CS1]; so val was wrong !!!  
! Tfgrm := *.(H/N) = *_CS1;                    byeq Red;   // HN :: *_CS1 := *@mSS|(CS1#CS1); // because  ! Tfgr := H/N = [CS1, *_CS1];
! Tfgre1 := e.(H/N) = N;                       by AxFgr;  is TFgre.N;              // ! AxFgr := H/N = Fgr.N; // // host(Tfgre1) = HN;
                                                   // ! Tisnorm1 := H<|K == H in nsubgr.GrK;     // GrK := Gr.K;   
! TnsubgreG := {e} in nsubgr.(Gr.elg);         by -Tisnorm1({e},elg); Tisnorm9;  // ! Tisnorm9 := {e} <| elg;      
! Tfgr0 := elg / {e} ~ G;                      // use elg/{e} = Gr(elg)/{e} = G/{e} ~ G; 

                                               // ! Tre6 := f in fn(A#A,A) & B <: A -> A[x,y:B, (f|(B#B))(x,y) = f(x,y)];
! Tfgrm1 := A[X,Y: CS1, X *_CS1 Y = X * Y]; is Tre6(TmSSt & L17);  // ! TmSSt := * @ mSS in fn(P[elg] # P[elg], P[elg]);  
! Tfgrm2 := A[X,Y: elg.(H/N), X *.(H/N) Y = X * Y];  by Tfgrelg, Tfgrm; Tfgrm1;

// ! Tfgr1 := A[N,H,K: subgr, N<|K & N<:H & H<:K -> H/N <: K/N]; //  ??? Reference ???

// ! Tfgr2 := A[N,H,K: subgr, N<|K -> (K/\H) / (N/\H) ~ (K/\H*N) / N];  // proof in Tism2
// ! Tfgr3 := A[N,H,K: subgr, N<|K & K/N in abelgroup -> (K/\H) / (N/\H) in abelgroup];

]; // HN :: [ #1

! TNgrDef := nsubgr = {H; H <: elg; H ~= {}; A[x,y:H, x*y in H];  
        A[x:H, inv(x) in H]; A[g:elg,h:H, (g*h)*inv(g) in H] }; // is Def(Nsubgr);  ??? no name ???
//  EqProof TNgrDef;                                // group :: ! Tclosed := A[S:P[elg], closed(S) == A[x,y: S, x*y in S] & A[x: S, inv(x) in S] ];
// F1 := nsubgr;                                                        by Axab;     // subgr := {H; AxHt := H in P1[elg], AxclosedH := closed(H) };
// F2 := {N; N in P1[elg]; closed(N); normal(N)};                       by AxP1;     // AxP1 := S in P1[Y] == S <: Y & S ~= {};
// F3 := {N; N <: elg & N ~= {}; closed(N); normal(N)};                 by Tclosed;  // Tnormal4 := normal(H) == A[x:elg, h:H, x*h*inv(x) in H];
// F4 := {N; N <: elg & N ~= {}; A[x,y: S, x*y in S] & A[x: S, inv(x) in S]; normal(N)}; by Tnormal4;  
// F5 := {N; N <: elg & N ~= {}; A[x,y: S, x*y in S] & A[x: S, inv(x) in S]; A[x:elg, h:H, x*h*inv(x) in H];};
//  end EqProof TNgrDef;

! TnsubrI := A[N1,N2: nsubgr, N1 /\ N2 in nsubgr];                   // nsubgr := {N ; AxN0 := N in subgr; AxN1 := normal(N)};
 Proof TnsubrI;
F0 := N1 in nsubgr;                          assume; by Axab; F01 & F02;
F01 := N1 in subgr;
F02 := normal(N1);
F03 := N2 in nsubgr;                         assume; by Axab; F04 & F05;
F04 := N2 in subgr;
F05 := normal(N2);
F06 := N1/\N2 in subgr;                     is TsbgI(N1,N2);         // HK :: ! TsbgI := H/\K in subgr; 
F07 := normal(N1) & normal(N2) -> normal(N1/\N2); is TnormalI(N1,N2);
F08 :=  normal(N1/\N2);                      is F07(F02 & F05);
G0 := N1/\N2 in nsubgr;                      by Axab; F06 & F08;
 end Proof TnsubrI;

nsubgr :: [                                       // ! Tisnorm1 := H<|K == H in nsubgr.GrK;     // GrK := Gr.K;   
! TN10 := N in nsubgr.(Gr.elg);              by -Tisnorm1(N,elg); TN5;      // ! TN5 := N <| elg;
elgN := elg/N;                               //HN :: !! Axfgr := H/N = Fgr.N;
! LelgN_type := elgN in group;               is Tfgr_type(elg,N);           // HN :: ! Tfgr_type := H/N in group;
! L11 := Fgr.N = Fgr;                        is Red;
! L12 := elgN = Fgr.N;                       is AxFgr(elg, N); by L11;      // HN :: !! AxFgr := H/N = Fgr.N;
! L13 := elgN = Fgr; 

! TunionRIn := A[B:P[P[elg]], B <: R[g:elg, g*N] -> union(B) = {g; g in elg, g*N in B}]; 
 Proof TunionRIn;
F0 := B in P[P[elg]];                        assume;               by AxP;  // ! AxP := Z in P[Y] == Z <: Y;
F01 := B <: P[elg];
F02 := B <: R[g:elg, g*N];                   assume;
G0 := union(B) = {g; g in elg, g*N in B};    by AxextA;            // !! AxextA := X = Y == All(x, x in X == x in Y);
G1 := All(g, g in union(B) == g in {g; g in elg,  g*N in B});
  Proof G1;  
assume(g);
G2 := g in union(B) == g in {g; g in elg, g*N in B}; by Axab;      // Axab: g in {g:elg; g*N in B} == g in elg & g*N in B;
G3 := g in union(B) == g in elg & g*N in B;  by Deqv; L1 & L2;     // ! Deqv := (p==q) == (p->q) & (q->p);

L1 := g in union(B) -> g in elg & g*N in B;
   Proof L1;
H0 := g in union(B);                         assume; by Tunionin;  // ! Tunionin := x in union(A) == Exist(Y, Y in A & x in Y);
H1 := Existx(Y, (H1a := Y in B) & (H1b := g in Y));
H2 := Y in P[elg];                           is TinIn(H1a & F01);  // ! TinIn := x in X2 & X2 <: Y2 -> x in Y2;
H3 := g in elg;                              is TininP(H1b & H2);  // ! TininP := x in X2 & X2 in P[Y2] -> x in Y2;
H4 := Y in R[g:elg, g*N];                    is TinIn(H1a & F02);  by TRin1; // !! TRin1 := z in R[x:A, G(x)] == Exist(x, x in A & z = G(x)]; 
H5 := Existx(x, x in elg & (H5b := Y = x*N));
H6 := g in x*N;	                             is H5b(H1b);          by LN9; // !! LN9 := A[g,x:elg; g in x*N == x*N=g*N]; 
H7 := x*N = g*N;
H8 := Y = g*N;                               is H7(H5b);                           
H9 := g*N in B;                              is H8(H1a);
   end Proof L1;

L2 := g in elg & g*N in B -> g in union(B);
   Proof L2;
H0 := g in elg;                              assume;
H01 := g*N in B;                             assume;
H02 := g in g*N;                             is LN10;             // ! LN10 := A[x:elg, x in x*N];
H1 := g*N <: union(B);                       is Tunion5(H01);     // !! Tunion5 := X in A -> X <: union(A));
H2 := g in union(B);                         is TinIn(H02 & H1);  // ! TinIn := x in X2 & X2 <: Y2 -> x in Y2;
   end Proof L2; 
  end Proof G1;   
 end Proof TunionRIn;

subgr_elgN := subgr.elgN;
! Tfgr5 := A[Q: subgr_elgN, union(Q) in subgr]; by L13; TFgr5;              //  A[N: nsubgr,   // proof in 15canhomp Prove !!!
// subgr_elgN :=                             // nsubgr :: ! TFgr5 := A[Q: subgr.Fgr, (UQ := union(Q)) in subgr];
]; // nsubgr :: [

dNK0K1 := nsubgr && {K0,K1; K0 in subgr_elgN, K1 in subgr_elgN };   // was subgr(elg/N), fix !!!
dNK0K1 :: [ 
// ! L0 := elg/N in group;
! L00 := union(K0) in subgr;   is Tfgr5;
! L01 := union(K1) in subgr;   is Tfgr5;
<|_elgN := <|.(elgN);         // error in typdot, vdt! // elgN := elg/N;
! L02_type := <|_elgN in fn(subgr_elgN # subgr_elgN, bool);  is Tisnorm.elgN; //  ! Tisnorm := <| @ group in fn(subgr#subgr, bool);
! Tfgr6 := K0 <|_elgN K1 -> union(K0) <| union(K1);  // <| := F[HK, H<:K & A[x:K, x*H = H*x]];// proof in 15canhomp;
]; // dNK0K1 :: [ 

// HNK := {N,H,K; N in subgr, H in subgr, K in subgr, N<|K};
// NHK := {N,H,K ; AxN := N in subgr, AxH := H in subgr, AxK := K in subgr, AxNH := N <| H};   // AxNK := N<|K};

HNK := HN && {K; AxK := K in subgr; AxNK := N <: K; AxKH := K <: H};   // K is an intermediated subgrop
HNK :: [            // HN := {H,N; AxH := H in subgr, AxN0 := N in subgr; AxN1 := N <| H };     //         N <| H;
! L0 := N/\H in subgr;                 is TsbgI(N,H);              // HK ::  ! TsbgI := H/\K in subgr;  
! L01 := K/\H in subgr;                is TsbgI(K,H);              // L02: should find it automatically: using thms: var in P[elg]; ?
! L02 := K/\H in P[elg];               is LsbgIP(K,H);             // ! LsbgIP := H/\K in P[elg];subgr -> var in P[elg]
                                                                   // HKL := HK && {L;  AxL := L in subgr};
! L04 := N<:H;                         is TInIn(AxNK & AxKH);      // ! TInIn := X0 <: Y0 & Y0 <: Z0 -> X0 <: Z0;
! L05 := N/\K in subgr;                is TsbgI(N,K);              // HK :: ! Tisnorm1 := H<|K == H in nsubgr.GrK;                       
! L1 := N <| K;                        is Tisnorm3(H,K,N)(LHNnorm & AxNK & AxKH); by Tisnorm1(N,K); // HK :: ! Tisnorm1 := H<|K == H in nsubgr.GrK;
! L2 := N in nsubgr.(GrK := Gr.K);     //  HKL :: ! Tisnorm3 :=  L <| H & L <: K & K <: H -> L <| K; // HN :: ! LHNnorm := N <| H;      
! Tfgr1 := K/N <: H/N;                  // for type checking:  use K in nsubgr.(Gr.H) == K <| H;
// !! L3 := N/\K <| K/\H;                  // x in K/\H -> (x*(N/\H) = x*N /\ x*H = N*x /\ H*x; (use x in K, N<|K, x in H);
// !! L4 := (K/\H)*N  in subgr;            // K/\H in subgr, use ! LHNsbg := H*N in subgr;
// !! L5 := (K/\H)*N <: H;                 // use N <: K, K/\H <:K, K in subgr;
// !! L6 := N <| (K/\H)*N;                 // use N<|K, L4, Tngrin;
// !! L7 := N/\K in nsubgr.(Gr.(K /\H));   //  it= 2 difitt= 0
// !! L8 := N in nsubgr.(Gr.((K /\H)*N));
// ! Tfgr2 := (K/\H) / (N/\K) ~ ((K/\H)*N) / N;
]; // HNK :: [   
                                // partition :: ! Tprtcl := Exist1x(cl, (Axcl1 := cl in fn(A,B)) & (Axcl2 := A[x:A, x  in cl(x)]));
nsubgr :: [   // ch: canonical homomorphism  // ! LCS2 := CS = R[g:elg, g*N]; // dcl[qinv,FN,FN];
ch := F[x:elg, x*N];  
! Lchdom := dom(ch) = elg;                  is TFdom1;
! Lchim := im(ch) = CS;                     by LCS2; is TimF;         // ! TimF   := im(F[d, G]) = R[d, G]; 
! Lch_type := ch in fn(elg,CS);             by -Lchim; is TF1t;       // FAGx := F[x:A, G(x)]; !! TF1t := FAGx in fn(A, im(FAGx));
! Lchqinvdom := dom(qinv.ch) = CS;          byeq Tqinvdom.ch, Lchim;  // FN :: !! Tqinvdom := dom(qinv) = im(f);
! Lch1 := A[x:elg, x in ch(x)];             by Red("F"); is LN10;     // ! LN10 := A[x:elg, x in x*N];// for proving cl.elgCS = ch;
! LelgCS1 := cl.elgCS in fn(elg,CS);        is Axcl1.elgCS;           // elgCS = [elg, CS];  // elgCS in partition;
! LelgCS2 := A[x:elg, x in cl.elgCS(x)];    is Axcl2.elgCS;           // !! TExist1 := Exist1(x,P(x)) & P(z) & P(z1) -> z = z1;
! LelgCS0 := Exist1(f, f in fn(elg,CS) & A[x:elg, x in f(x)]);        is Tprtcl.elgCS;   
! TelgCS1 := cl.elgCS = ch;                 is TExist1(LelgCS0 & (LelgCS1 & LelgCS2) & (Lch_type & Lch1));
                                            // !! TExist1 := Exist1(x,P(x)) & P(z) & P(z1) -> z = z1;
erg := [elg, F[x,y: elg, x*N = y*N]];       // erg: equivalence relation in group // host = nsubgr
       
! Terg := erg = eqr.elgCS;                           // eqr := [A, eqf := F[x,y: A, cl(x)=cl(y)] ]; 
 EqProof -Terg;                                      // ch := F[x:elg, x*N];
F1 := eqr.elgCS;                                     by Red("dot");
F2 := [elg, F[x,y:elg, cl.elgCS(x) = cl.elgCS(y)]];  by TelgCS1;      // ! TelgCS1 := cl.elgCS = ch; 
F3 := [elg, F[x,y:elg, ch(x) = ch(y)]];              by Red("F");  // ("F");     // ch := F[x:elg, x*N];
F4 := [elg, F[x,y: elg, x*N = y*N]]; 
 end EqProof -Terg;
                              // partition :: !! Teqr_eqcl := eqcl.eqr = cl;       // !! Axqset :=  qset = R[x:S, eqcl(x)];   
! Tergin := erg in eqvrel;                          by Terg; is Teqr.elgCS;        // ! Teqr := eqr in eqvrel;
! Terg1 := qset.erg = CS;                           by Terg; is Teqr_qset.elgCS;   // !! Teqr_qset := qset.eqr = B;       


! LchqinvA := A[X:CS, qinv.ch(X) = X];
 EqProof LchqinvA;
F0 := X in CS;                              assume; by LCSin2;                     // ! LCSin2 := X in CS == E[g:elg, X = g*N];
F01 := Ex[a:elg, F01a := X = a*N];
// F02 := dom(ch) = elg;                       is TFdom1;     //  !! TFdom1 := dom(FAGx) = A; 
F1 := qinv.ch(X);                           by F01a;                 // ! Lchdom := dom(ch) = elg;  
F2 := qinv.ch(a*N);                         by Tqinv.ch(a*N),Lchdom; // !! Tqinv := A[y:im(f), qinv(y) = {x: dom(f); f(x) = y} ];
F3 := {x: elg; ch(x) = a*N};                by Red;
F4 := {x: elg; x*N = a*N};                  by LN11;                 // ! LN11 := A[g:elg, {x:elg; x*N = g*N} = g*N];
F5 := a*N;                                  by -F01a;
F6 := X;
 end EqProof LchqinvA;
                                            // !! Tideq := A[f:FN, f=id(A) == dom(f)=A & A[x:A, f(x)=x]];
! Lchqinv := qinv.ch = id(CS);              by Tideq; Lchqinvdom & LchqinvA;
! Lchqinv1 := qinv.ch = id(im(ch));         by Lchim; Lchqinv;      // ! Lchim := im(ch) = CS; 
                                       
! Lchpreim := preim.ch = F[Y:P[CS], union(Y)];
 Proof Lchpreim;                                               // !! Tpreim1 := qinv=id(im(f)) -> preim = F[Y:P[im(f)], union(Y)];
F0 := qinv.ch=id(im(ch)) -> preim.ch = F[Y:P[im(ch)], union(Y)]; is Tpreim1.ch;
F1 := preim.ch = F[Y:P[im(ch)], union(Y)];                       is F0(Lchqinv1); by Lchim; Lchpreim
// F2 :=  preim.ch = F[Y:P[CS], union(Y)];                       // error: no merging;    
 end  Proof Lchpreim;
                                                // HK :: ! Tisnorm4a := normal(H) -> (H <: K -> H <| K); 
]; // nsubgr :: [   // canonical homomorphism   // HK :: ! Tisnorm4 := normal(H) & H <: K -> H <| K;                  
]; // group :: [    // 5                        // HK :: ! Tisnorm1 := H<|K == H in nsubgr.GrK; 

GG1 := {G, G1; AxG := G in group, AxG1 := G1 in group};
dcl[<::, group, group, bool];

GG1 :: [      // 1 
!! AxgroupIn := G <:: G1 == elg.G <: elg.G1 & *.G = *.G1|(elg.G#elg.G);  // did not work: error;
!! AxGreq := G=G1 == elg.G = elg.G1 & *.G = *.G1;
! LeG := e.G in elg.G;                                 is Axe.G;
! LeG1 := e.G1 in elg.G1;                              is Axe.G1; 
! Lelg_G := elg.G in subgr.G;                          is Telg.G;        // ! Telg := elg in subgr;  
! Lelg_G1 := elg.G1 in subgr.G1;                       is Telg.G1;
! LeG1n := {e.G1} in nsubgr.G1;                        is Tnsubgre.G1;   // ! Tnsubgre := {e} in nsubgr; 

*_G := *.G;   // *(group).G;
! LmG_type := *_G in fn(elg.G#elg.G, elg.G);           is Axm.G;      // Axm := * in fn(elg#elg, elg);  
! LassocG := assoc(*_G, elg.G);                        is Lassoc.G; // ! Lassoc := assoc(elg, *(group)); 

*_G1 := *(group).G1;
! LmG1_type := *_G1 in fn(elg.G1#elg.G1, elg.G1);       is Axm.G1;
! LassocG1 := assoc(*_G1, elg.G1);                     is Lassoc.G1; 
! Lm_G1_dom := dom(*_G1) = elg.G1#elg.G1;              is Tfndom(LmG1_type);    // !! Tfndom := f in fn(A,B) -> dom(f) = A;

inv_G := inv@group.G;
! Linv_G_type := inv_G in fn(elg.G, elg.G);            is Axinv.G;              // Axinv  := inv in fn(elg,elg)
! Linv_G_dom := dom(inv_G) = elg.G;                    is Tfndom(Linv_G_type);  // Tfndom := f in fn(A,B) -> dom(f) = A; 

inv_G1 := inv@group.G1;
! Linv_G1_type := inv_G1 in fn(elg.G1, elg.G1);        is Axinv.G1; 
! Linv_G1_dom := dom(inv_G1) = elg.G1;                 is Tfndom(Linv_G1_type);  // Tfndom := f in fn(A,B) -> dom(f) = A; 

*_eS_G := *(meS).G;                                                   // meS := dcl[*, fn(elg # P[elg], P[elg]) ]; 
! LmeSG_type := *_eS_G in fn(elg.G # P[elg.G], P[elg.G]); is TmeSt.G; // ! TmeSt := * @ meS in fn(elg # P[elg], P[elg]);

*_Se_G := *(mSe).G;                                                   // mSe := dcl[*, fn(P[elg] # elg, P[elg]) ];
! LmSeG_type := *_Se_G in fn(P[elg.G] # elg.G, P[elg.G]); is TmSet.G; // ! TmSet := * @ mSe in fn(P[elg] # elg, P[elg]);

*_eS_G1 := *(meS).G1;                                                 // meS := dcl[*, fn(elg # P[elg], P[elg]) ]; 
! LmeSG1_type := *_eS_G1 in fn(elg.G1 # P[elg.G1], P[elg.G1]); is TmeSt.G1;

*_Se_G1 := *(mSe).G1;                                                 // mSe := := dcl[*, fn(P[elg] # elg, P[elg]) ];
! LmSeG1_type := *_Se_G1 in fn(P[elg.G1] # elg.G1, P[elg.G1]); is TmSet.G1;

! AxconjG := A[x,y:elg.G, conj.G(x,y) = x *_G y *_G inv_G(x)]; is Axconj.G; // !! Axconj := A[x,y:elg, conj(x,y) = x*y*inv(x)];

]; // GG1 :: [ // 1

GG1a := GG1 && (AxGG1a := G <:: G1);    // !! AxgroupIn := G <:: G1 == elg.G <: elg.G1 & *.G = *.G1|(elg.G#elg.G); 
GG1a :: [                              // 1
(! L_elg := elg.G <: elg.G1) &
(! L_m := *.G = *.G1 | (elg.G#elg.G));       is AxgroupIn(AxGG1a);
! L1 := e.G in elg.G1;                       is TinIn(LeG & L_elg);                     // ! TinIn := x in X2 & X2 <: Y2 -> x in Y2;
! L2 := A[x,y: elg.G, x *.G y = x *.G1 y];   by L_m; is Tre6(LmG1_type & L_elg);        // ! LmG1_type := *_G1 in fn(elg.G1#elg.G1, elg.G1); 
                 // !! Tre6 := f in fn(A#A,A) & B <: A -> A[x,y:B, (f|(B#B))(x,y) = f(x,y)];
! L0 := elg.G in subgr.G;                    is Telg.G;                                 // ! Telg := elg in subgr;  
! L01 := P1[elg.G] <: P1[elg.G1];            is  TP1m(L_elg);                // !! TP1m := X <: Y -> P1[X] <: P1[Y];
                                                          
! L_e := e.G = e.G1;                                      
 Proof L_e;
F0 := A[a:elg.G1, a *.G1 a = a -> a = e.G1]; is Laaa.G1;                // ! Laaa := A[a:elg, a*a = a -> a = e];
F01 := e.G *.G e.G = e.G;                    is Teee.G;    by L2;       // ! Teee := e*e = e;
F02 := e.G *.G1 e.G = e.G;  
F1 := e.G = e.G1;                            is F0(F02);                    
 end Proof L_e;                                                              /// fa :: !! Treval := A[x:A, (f|A)(x) = f(x)];  

! L3 := dom(inv.G1 | elg.G) = elg.G;         is Tredom@fA;                               // fA :: !! Tredom := dom(f|A) = A; 
! L4 := dom(inv.G) = dom(inv.G1 | elg.G);    byeq Linv_G_dom, -L3;   // ! Linv_G_dom := dom(inv_G) = elg.G;
                     
! L_invA := A[x:elg.G, inv.G(x) = inv.G1(x)];  
 Proof L_invA;
F0 := x in elg.G;                            assume;
F01 := A[x:elg.G, x *.G inv.G(x) = e.G];     is Axrinv.G;  by L2;       // Axrinv := A[x: elg, x * inv(x) = e];
F02 := A[x:elg.G, x *.G1 inv.G(x) = e.G];
F03 := A[x:elg.G1, x *.G1 inv.G1(x) = e.G1]; is Axrinv.G1;
F1 := x *.G1 inv.G(x) = e.G;                 is F02;                    // !! Axeq3 := x=a1 & y=a2 & a1=a2 -> x=y;
F2 := x *.G1 inv.G1(x) = e.G1;               is F03;                    // was error if *G1 (no dot); 1.1.22
F3 := x *.G1 inv.G(x) = x *.G1 inv.G1(x);    is Axeq3(F1 & F2 & L_e);
F4 := inv.G(x) = inv.G1(x);                  is Tcancel_law2A1.G1(F3);  // ! Tcancel_law2A1 := A[a,b,c: elg, c*a=c*b == a=b];   
 end Proof L_invA;

! K0 := A[x:dom(inv.G), inv.G(x) = (inv.G1 | elg.G)(x)]; by Linv_G_dom, Tre2(Linv_G1_type & L_elg); L_invA;
                      // ! Linv_G_dom := dom(inv_G) = elg.G;            // ! Tre2 := f in fn(A,B) & C <: A -> A[x: C,  (f|C)(x) = f(x)];
! L_inv := inv.G = inv.G1 | elg.G;           by Tfneq; L4 & K0; // !! Tfneq := A[f,g: FN, f=g == dom(f)=dom(g) & A[x:dom(f), f(x)=g(x)]];       
  
! L_closed := A[H:P[elg.G], closed.G1(H) == closed.G(H)];      // ! Tclosed := A[S:P[elg], closed(S) == A[x,y:S, x*y in S] & A[x:S, inv(x) in S] ];
 EqProof -L_closed;
F0 := H in P[elg.G];                       assume;
F1 := closed.G(H);                         by Tclosed.G;
F2 := A[x,y:H, x *.G y in H] & A[x:H, inv.G(x) in H];  by L2, L_invA, -(Tclosed.G1);
F3 := closed.G1(H);
 end EqProof -L_closed;

// !! L_P1elg := P1[elg.G] <: P1[elg.G1];    // same as L01

! L5 := subgr.G <: subgr.G1; 
 Proof L5;                                   by TInA;                        // !! TInA := A <: B == A[x:A, x in B]; 
F1 := A[H: subgr.G, H in subgr.G1];
  Proof F1;
K0 := H in subgr.G;                          assume; by Tsubgrin.G; K1 & K2; // ! Tsubgrin := X in subgr == X in P1[elg] & closed(X);
K1 := H in P1[elg.G];
K2 := closed.G(H);
G0 := H in subgr.G1;                         by Tsubgrin.G1; G01 & G02;
G01 := H in P1[elg.G1];                      is TinIn(K1 & L01);             // ! TinIn := x in X2 & X2 <: Y2 -> x in Y2;
G02 := closed.G1(H);                         by L_closed; K2;          
  end Proof F1;         
 end Proof L5;

! L6 := elg.G in subgr.G1;                   is TinIn(L0 & L5);              // ! L0 := elg.G in subgr.G;   // used in Tisnorm4b.F1; 

! L7 := A[X,Y: subgr.G, X <|.G1 Y == X <|.G Y];
 EqProof -L7;                                              // ! Tre6 := f in fn(A#A,A) & B <: A -> A[x,y:B, (f|(B#B))(x,y) = f(x,y)];
F0 := X in subgr.G;              assume;  
F01 := X in P1[elg.G];           is TinIn(F0 & Tsubgr3.G);                   // ! Tsubgr3 := subgr <: P1[elg];
F02 := Y in subgr.G;             assume;                                     // ! TinIn := x in X2 & X2 <: Y2 -> x in Y2;
F03 := Y in P1[elg.G];           is TinIn(F02 & Tsubgr3.G);
F1 :=  X <|.G Y;                 by Tisnorm0A.G;           // ! Tisnorm0A := A[H,K:subgr, H<|K == H<:K & A[x:K,h:H, x*h*inv(x) in H]]; 
F2 := X <: Y & A[x:Y,h:X, x *.G h *.G inv.G(x) in X];      by L2;     // ! L2 := A[x,y: elg.G, x *.G y = x *.G1 y];  
F3 := X <: Y & A[x:Y,h:X, x *.G h *.G1 inv.G(x) in X];     by L2;     // F2; by L2; F4; did not work: 01.15.22; congr(F2,F4, ...) ???
F4 := X <: Y & A[x:Y,h:X, x *.G1 h *.G1 inv.G(x) in X];    by L_invA;  // ! L_invA := A[x:elg.G, inv.G(x) = inv.G1(x)];
F5 := X <: Y & A[x:Y,h:X, x *.G1 h *.G1 inv.G1(x) in X];   by -(Tisnorm0A.G1);
F6 := X <|.G1 Y;   // F2; by L2; F4; did not work because in isbe after finding first instance of x *.G y, 
 end EqProof -L7;  // second instance was missed because Nxt1; (because top-down search is used). F2; by L2,L2,L_invA,-(Tisnorm0A.G1); does work !!! 
                                          
! Tisnorm4b := A[N: nsubgr.G1, N in subgr.G -> N in nsubgr.G];
 Proof Tisnorm4b;                                            // ! Tnormal0 := normal(H) == H in nsubgr; 
F0 := N in nsubgr.G1;            assume;                     // ! Tisnorm1 := H<|K == H in nsubgr.GrK;
F01 := N in subgr.G;             assume;                     // HK :: ! Tisnorm4 := normal(H) & H <: K -> H <| K;
F02 := N <: elg.G;               is Tsubgr2.G(F01);            // ! Tsubgr2 := X in subgr -> X <: elg;
F1 := A[H,K:subgr.G1, H in nsubgr.G1 & H <: K -> H <|.G1 K]; is Tisnorm4A1.G1; // take H=N, K = elg.G
F2 := N <|.G1 elg.G;             is F1(F0 & F02);  by L7;           
F3 := N <|.G elg.G;              by -(Tisnormelg.G);         // ! Tisnormelg := A[H:subgr, H in nsubgr == H <| elg] ;  
F4 := N in nsubgr.G;             // ! Tisnorm4A1 := A[H,K:subgr, H in nsubgr & H <: K -> H <| K]; // H=N, K= elg.G;
 end  Proof Tisnorm4b;
 
]; // GG1a :: [                     // 1

// !! Tisnorm4b := A[G,G1:group, N: nsubgr.G1, G <:: G1 & N <: elg.G -> N in nsubgr.G];
dGN := {G,N; AxG := G in group, AxN := N in nsubgr.G; };        // !! Lpreim2 := A[x:dom(f),Y:P[im(f)], x in preim(Y) == f(x) in Y];  

dcl[/, fn(dGN, group)];                                  
!! Axfgr := A[dGN, G/N = Fgr.N];                       // Fgr := [CS, *_CS];  // *_CS := *@mSS | (CS # CS); 
dGN :: [
 ! TFgr := G/N = [CS.N, *_CS.N];                       byeq Axfgr, Red("dot");       // *_CS.ker = *_CS
]; // dGN :: [

GG1 :: [     // 2

hom := {h ; Axh := h in fn(elg.G, elg.G1); 
          Axhom := A[x,y: elg.G, h(x *.G y) = h(x) *.G1 h(y)] }; 

! Thomin := All(f, f in hom(G,G1) == f in fn(elg.G, elg.G1) & A[x,y: elg.G, f(x *.G y) = f(x) *.G1 f(y)]);  is Axab;

hom :: [
imG := im(h);                                                // Timval.h: A[x:dom(h), h(x) in im(h)]; 
! Lhomdom := dom(h) = elg.G;             is Tfndom(Axh);     // !! Tfndom := f in fn(A,B) -> dom(f) = A;  
! Lhom1 := A[x:elg.G, h(x) in imG];      is Timval.h;        // !! Timval := A[x:dom(f), f(x) in im(f)];             
! Lhom1a := h in fn(elg.G, imG);         by -Lhomdom; is Tfndomim@FN;   // FN :: !! Tfndomim := f in fn(dom(f), im(f));
! LimG := imG <: elg.G1;   is Tfnim(Axh);  // !! Tfnim := f in fn(A,B) -> im(f) <: B; // Axh := h in fn(elg.G, elg.G1);
! L0 := elg.G in P[elg.G]; is L01.G;       // group :: ! L01 := elg in P[elg]; 
 
! Lhom1t := A[x,y:elg.G, h(x *.G inv.G(y)) = h(x) *.G1 inv.G1(h(y))];      // was L1t;
 EqProof Lhom1t;
F0 := x in elg.G;                                      assume;
F01 := y in elg.G;                                     assume;
F02 := h(y) *_G1 inv.G1(h(y)) = e.G1;                  is Axrinv.G1(h(y)); // Axrinv := A[x: elg, x * inv(x) = e]
F1 := h(x *.G inv.G(y));                               by -(Axre.G1);      // Axre := A[x:elg, x * e = x]
F2 := h(x *.G inv.G(y)) *.G1 e.G1;                     by -F02;  
F3 := h(x *.G inv_G(y)) *.G1 (h(y) *.G1 inv.G1(h(y))); by AxAssoc.G1;      // AxAssoc:= A[x,y,z: elg, x*(y*z) = (x*y)*z ];
F4 := (h(x *.G inv_G(y)) *.G1 h(y)) *.G1 inv.G1(h(y)); by -Axhom;
F5 := h(x *.G inv.G(y) *.G y) *.G1 inv.G1(h(y));       by Linv2.G;         // ! Linv2 := (x * inv(y))*y = y; 
F6 := h(x) *.G1 inv.G1(h(y));                          // was F6 := h(x) *.G1 inv_G1(h(y)); the error was discovered on 2023.03.29
 end EqProof Lhom1t;

! Lhome := h(e.G) = e.G1;                             // e.G*e.G = e.G; h(e.G)*h(e.G) = h(e.G); h(e.G) = e.G1;
 Proof Lhome;
F0 := e.G *.G e.G = e.G;                               is Teee.G;          // ! Teee := e*e = e;
F1 := h(e.G *.G e.G) = h(e.G);                         byeq F0; by Axhom;
F2 := h(e.G) *.G1 h(e.G) = h(e.G);
F3 := h(e.G) = e.G1;                                   is Laaa.G1(F2);     // ! Laaa := A[a:elg, a*a = a -> a = e];  
 end Proof Lhome;

! L05 := e.G1 in imG;                                  by -Lhome; is Lhom1;
! L05a := {e.G1} in P[imG];                            by TSinP; L05; // ! TSinP := {a} in P[X] == a in X;    // imG := im(h);
// !! L05b := {e.G1} <: elg.ImG;                       
     
! Lhominv  := A[x:elg.G, h((inv_G)(x)) = inv_G1(h(x)) ];
 EqProof Lhominv; 
F0 := x in elg.G;                                      assume;   
F01 := e.G *_G inv_G(x) = inv_G(x);                    is Tle.G;           // ! Tle := A[a:elg, e*a = a];
F1 := h(inv_G(x));                                     by -F01;         
F2 := h(e.G *_G inv_G(x));                             by Lhom1t;
F3 := h(e.G) *.G1 inv.G1(h(x));                        by Lhome;
F4 := e.G1 *.G1 inv.G1(h(x));                          by Tle.G1(inv_G1(h(x)));
F5 := inv.G1(h(x));
 end EqProof Lhominv;

! Lhomm3 := A[x,y,z: elg.G, h((x *_G y) *_G z) = (h(x) *_G1 h(y)) *_G1 h(z)]; 
 EqProof Lhomm3;
F0 := x in elg.G;                                      assume;
F01 := y in elg.G;                                     assume;
F02 := z in elg.G;                                     assume;
F1 := h((x *_G y) *_G z);                              by Axhom;
F2 := h(x *_G y) *_G1 h(z);                            by Axhom;
F3 := (h(x) *_G1 h(y)) *_G1 h(z);
 end EqProof Lhomm3;

dhP := dcl[h, fn(P[elg.G], P[imG])];                   // FN :: !! TimreP1 := A[A:P[dom(f)], A in P1[dom(f)] == im(f|A) in P1[im(f)]];
B_P_elg_G := {B; B in P[elg.G]};                       // fA :: !! TimreE := All(y,y in im(f|A) == E[x:A, f(x) = y]);
!! AxhP := A[B_P_elg_G, h(B) = im(h|B) ];    by Timre@fA;   // fA :: !! Timre := im(f|A) = R[x:A, f(x)];
! LhPR := A[B_P_elg_G, h(B) = R[x:B, h(x)] ];               //  ! Lhomdom := dom(h) = elg.G;
! LhP1 := A[B_P_elg_G, B in P1[elg.G] == h(B) in P1[imG]]; by -Lhomdom, AxhP; is TimreP1@FN; // ! Lhomdom := dom(h) = elg.G;
! LhPin := A[B_P_elg_G, x1 in h(B) == E[x:B, h(x) = x1]];  byeq AxhP, TimreE@fA; 
! LhP2 := A[B_P_elg_G, A[b:B, h(b) in h(B)]]; by AxhP;     is Treim2(h,B@LhP2);     // fA::!! Treim2 := A[x:A, f(x) in im(f|A)]; //  A[B:P[elg.G],
! LhP3 := h(dom(h)) = imG;                    byeq AxhP, Timredom@FN; by Lhomdom;   // !! Timredom := im(f|dom(f)) = im(f);       
! LhP4 := h(elg.G) = imG;                                // h(dom(h)) = im(h);

! Lhomim := A[H: subgr.G, h(H) in subgr.G1];
 Proof Lhomim;
F0 := H in subgr.G;                       assume; by Tsubgrin1t.G; F0a & F0d;
H1 := h(H);
F0a := H in P1[elg.G];                    by LhP1;                // !! LhP1 := A[B:P[elg.G], B in P1[elg.G] == h(B) in P1[imG]];
F0b := H1 in P1[imG];                     // imG := im(h);        // ! LimG := imG <: elg.G1; 
F0c := H1 in P1[elg.G1];                  is TP1inIn(F0b & LimG); // !! TP1inIn :=  X in P1[A] & A <: B -> X in P1[B];
F0d := A[x,y:H, x *.G inv.G(y) in H];
G0 := H1 in subgr.G1;                    by Tsubgrin1t.G1; F0c & G01; // Tsubgrin1t := V in subgr == V in P1[elg] & A[x,y: V, x*inv(y) in V];
G01 := A[x1,y1: H1, x1 *.G1 inv.G1(y1) in H1];              // Cannot use G1 !!!
  Proof G01;                            
F01 := x1 in H1;                         assume; by LhPin;  // !! LhPin := A[B:P[elg.G], x1 in h(B) == Ex[x:B, h(x) = x1]];
F01a := Ex[x:H, F01a1 := h(x) = x1];
F02 := y1 in H1;                         assume; by LhPin;  // !! LhPin := A[B:P[elg.G], x1 in h(B) == Ex[x:B, h(x) = x1]];
F02a := Ex[y:H, F02a1 := h(y) = y1];
F1 := (z:=x *_G inv.G(y)) in H;          is F0d;            // ! Lhom1t := A[x,y:elg.G, h(x *_G inv_G(y)) = h(x) *_G1 inv_G1(h(y));
F2 := h(z) in H1;                        is LhP2(H)(z); by Lhom1t; // !! LhP2 := A[B:P[elg.G], b: B, h(b) in h(B)]; 
F3 := h(x) *.G1 inv.G1(h(y)) in H1;      by F01a1, F02a1;
F4 := x1 *.G1 inv.G1(y1) in H1;
  end  Proof G01;
 end Proof Lhomim;

! L03 := h(elg.G) in subgr.G1;           is Lhomim(elg.G);   // ! Lhomim := A[H: subgr.G, h(H) in subgr.G1];
! L08 := A[x:elg.G, h(x) in imG];        is TfnA(Lhom1a);  // ! Lhom1a := h in fn(elg.G, imG);

// ! Lhom3 := imG in subgr.G1;              by -LhP4; is Lhomim(elg.G);   // ! LhP4 := h(elg.G) = imG; 
*_ImG := *_G1 | (imG#imG);               // *_G1 := *(group).G1;
! LimG_type := imG in subgr.G1;          by -LhP4; is Lhomim(elg.G); // is Lhom3;     // ! Lhom3 := imG in subgr.G1;

ImG := Gr.imG;                           // *_ImG := *_G1 | (imG#imG); // Axh := h in fn(elg.G, elg.G1);
! LImG_type := ImG in group;             is TGr_type.imG;              //:(subgr.G1)); // ! TGr_type := Gr in group; 

! TImG := ImG = [imG, *_ImG];            is AxGr.imG; // Gr := [H, *_Gr := *(group)|(H#H)];    // subgr :: ! AxGr := Gr = [H, *_Gr];
! LImGelg := elg.ImG = imG;              is Red;
                                                                  // 2023.03.30
! L12 := *_ImG = *.ImG;                  by TImG; is Red;         // ??? find out, why by TImG; is necessary, unlike ! LImGelg := elg.ImG = imG;      
! L13 := elg.ImG <: elg.G1;              by LImGelg; is LimG;     // ! LimG := imG <: elg.G1;
! L14 := *.ImG = *_G1 | (elg.ImG # elg.ImG);  byeq -L12, -LImGelg;    // LImGelg;    is Axrefl; // Axrefl := x = x; // was by AxgroupIn@GG1;
! TImG1 := ImG <:: G1;                   by AxgroupIn(ImG,G1); L13 & L14; // !! AxgroupIn := G <:: G1 == elg.G <: elg.G1 & *.G = *.G1|(elg.G#elg.G); 
! LeImG := e.ImG = e.G1;                 is L_e(ImG,G1);          // GG1a:: L_e := e.G = e.G1;
! L05b := {e.G1} in subgr.ImG;           by -LeImG; is TSe.ImG;   // ! TSe  := {e} in subgr; 
! L07 := subgr.ImG <: P[im(h)];          is Tsubgr3b.ImG;    // ImG := Gr.imG; imG := im(h); ! Tsubgr3b := subgr <: P[elg]; 

! LImGG1 := elg.ImG = elg.G1 -> ImG = G1;    // imG = im(h) = elg.Img;  // ImG := Gr.imG;
 Proof LImGG1;
F0 := elg.ImG = elg.G1;                  assume;                // *_ImG := *_G1 | (imG#imG);   // FN :: !! Tredomf := f|dom(f) = f;  
F1 := *.ImG = *.G1;                      byeq L14,F0, -Lm_G1_dom , Tredomf@FN;         // ! Lm_G1_dom := dom(*_G1) = elg.G1#elg.G1; 
Goal := ImG = G1;                        by AxGreq@GG1; F0 & F1;                       // !! AxGreq := G=G1 == elg.G = elg.G1 & *.G = *.G1;
 end Proof LImGG1;                                                                     // @GG1 makes G,G1 in AxGreq variables;

! LImGG1a := imG = elg.G1 -> ImG = G1;  by -LImGelg; LImGG1;     // ! LImGelg := elg.ImG = imG;
                                                               
                                        
! Lhom3 := A[X,Y: subgr.G1, X in subgr.(Gr.Y) == X <: Y];   is L25A.G1; // ! L25A := A[H,K: subgr, H in subgr.(Gr.K) == H <: K]; 

! Lhomim1 := A[H: subgr.G, h(H) in subgr.ImG];                   //  ! Lhomdom := dom(h) = elg.G; // h(H) = im(h|H);
 Proof Lhomim1;                                                  // ! Lhomim := A[H: subgr.G, h(H) in subgr.G1]; 
F0 := H in subgr.G;                      assume;                 // Axh := h in fn(elg.G, elg.G1);
F01 := H <: elg.G;                       is Tsubgr2.G(F0);       // ! Tsubgr2 := X in subgr -> X <: elg;             
F02 := h(H) in subgr.G1;                 is Lhomim(H);           // ! Lhomim := A[H: subgr.G, h(H) in subgr.G1];
// G0 := h(H) in subgr.ImG;                 by -Lhom3;              // change the name; // fA :: !! Treim1 := im(f|A) <: im(f); 
G0 := h(H) in subgr.ImG;                 by Lhom3;               // change the name; // fA :: !! Treim1 := im(f|A) <: im(f); 
G01 := h(H) <: imG;                      by AxhP;                // !! AxhP := A[B_P_elg_G, h(B) = im(h|B) ];
G02 := im(h|H) <: imG;                   is Treim1@fA;           // fA :: !! Treim1 := im(f|A) <: im(f); 
 end Proof Lhomim1;

!! Axhom1 :=  A[x,y: elg.G, h(x *.G y) = h(x) *.ImG h(y)];       // is Tre6 ??? Tre2 ??? must be proved !!! 2022.11.16
                                        
   // !! Timre2  := f in fn(A,B) & C <: A -> im(f|C) <: B;

! L06 := A[x1,y1: imG, x1 *_G1 y1 in imG];
 Proof L06;
F0 := x1 in imG;                         assume;   by TimE(h); // !! TimE := All(y, y in im(f) == E[x:dom(f), y = f(x)]); 
F01 := Ex[x:dom(h), F01a := x1 = h(x)];
F02 := y1 in imG;                        assume;   by TimE(h);         
F03 := Ex[y:dom(h), F03a := y1 = h(y)];       // Axhom := A[x,y: elg.G, h(x *_G y) = h(x) *_G1 h(y)] };
F1 := h(x *_G y) = h(x) *_G1 h(y);       is  Axhom; by -F01a, -F03a;  
F2 := h(x *_G y) = x1 *_G1 y1; 
F3 := h(x *_G y) in imG;                 is Timval.h; by F2;  // FN :: !! Timval := A[x:dom(f), f(x) in im(f)]; 
F4 := x1 *_G1 y1 in imG;                    // subgr :: Lx := inv|H in fn(H,H); Lx.imG: imG in subgr.G1;
 end Proof L06;                             // ! Tre7 := f in fn(A#A,A) & B<:A & A[x,y:B, f(x,y) in B] -> f|(B#B) in fn(B#B,B);
                                            // ! LmG1_type := *_G1 in fn(elg.G1#elg.G1, elg.G1); // ! LimG := imG <: elg.G1; 
! L09 := A[x,y: imG, x *_ImG y = x *_G1 y]; is Tre6(LmG1_type & LimG);
// ! Tre2 := f in fn(A,B) & C<:A -> A[x:C, (f|C)(x) = f(x)]; // ! Tre6 := f in fn(A#A,A) & B<:A -> A[x,y:B, (f|(B#B))(x,y) = f(x,y)]; 
inv_ImG := inv_G1 | imG;                    // ! Linv_G1_type := inv_G1 in fn(elg.G1, elg.G1);  =
! Linv_ImG_type := inv_ImG in fn(imG, imG); is Linv_Gr_type.imG; // ! Linv_Gr_type  := inv_Gr in fn(H, H);  // inv_Gr := inv|H;
! L10 := A[x_imG, inv_ImG(x) = inv_G1(x)];  is Tre2(Linv_G1_type & LimG);     
! L11 := A[x_imG, inv_G1(x) in imG];        by -L10; is TfnA(Linv_ImG_type); // ! TfnA := f in fn(A, B) -> A[x:A, f(x) in B];  
                                            
! Tm_ImG_type := *_ImG in fn(imG#imG, imG); is Tre7(LmG1_type & LimG & L06);             // ! LimG := imG <: elg.G1;
! Tm_ImG_ass := assoc(*_ImG, imG);          is Treassoc(LassocG1 & LimG & Tm_ImG_type); 
                                                         // !! Treassoc := assoc(f,A) & B<:A & f|(B#B) in fn(B#B,B) -> assoc(f|(B#B),B);   
x_imG := {x; x in imG};                            
! T_ImG_e := A[x_imG, x *_ImG e.G1 = x];    by L09; is LHre.imG;  // ! LHre := A[x_H, x * e = x]; // LHre.imG = A[x:imG, x *_G1 e.G1 = x];
! T_ImG_inv := A[x_imG, x *_ImG inv_ImG(x) = e.G1]; by L09,L10; is LHrinv.imG;  // ! LHrinv := A[x_H, x * inv(x) = e]; 
! T_ImG_einv := E[e1:imG,inv1:fn(imG,imG), A[x_imG, x *_ImG e1 = x] & A[x_imG, x *_ImG inv1(x) = e1]]; is Witness(e.G1, inv_ImG);
// istr0: A[x:A, P(x)] can be converted to P(Var(A,1)); ??? 6.12.21 A[x,y:A, P(x,y) => P(Var(A,1),Var(A,2); v1,v2,v3, ... ???

// ImG := [imG, *_ImG]; // !! Treassoc := assoc(f,A) & B<:A & f|(B#B) in fn(B#B,B) -> assoc(f|(B#B),B);
// AxAssoc:= A[x,y,z: elg, x*(y*z) = (x*y)*z ];
// Axeinv := Ex[{e,inv; Axe := e in elg; Axinv  := inv in fn(elg,elg)}, 
//               (Axre := A[x:elg, x * e = x]) & (Axrinv := A[x: elg, x * inv(x) = e])];
// !! Tingroup := [A,f] in group == assoc(f,A) & E[e1:A, inv1:fn(A,A), A[x:A, f(x,e1) = x] & A[x:A, f(x,inv1(x)) = e1]];
// !! LassocG1 := assoc(*_G, elg.G1);     

// ! TImG_type := ImG in group;          by Tingroup; Tm_ImG_ass & T_ImG_einv;
// ! LImGelg := elg.ImG = imG;           byeq Red;   // moved up;  // ImG := Gr.imG; // inv_ImG := inv_G1 | imG;

! Linv_ImG1 := inv.ImG = inv_ImG;        is LH3a.imG;  // subgr :: ! LH3a := invGr = inv_Gr; // invGr := inv.Gr;  // inv_Gr := inv|H;

 *_eS_ImG := *@meS.ImG;               // ! LmG1_type := *_G1 in fn(elg.G1#elg.G1, elg.G1);
! L03_type := *_eS_ImG in fn(imG # P[imG], P[imG]); is TmeSt.ImG;  // ! TmeSt := * @ meS in fn(elg # P[elg], P[elg]);

 *_Se_ImG := *@mSe.ImG;
! L04_type := *_Se_ImG in fn(P[imG] # imG, P[imG]); is TmSet.ImG;  // ! TmSet := * @ mSe in fn(P[elg] # elg, P[elg]);
! L2 := P[imG] <: P[elg.G1];  is TPm(LimG);  // ! TPm := X1 <: Y1 == P[X1] <: P[Y1];  // ! LimG := imG <: elg.G1; 

! Lhom1t1 := A[x,y:elg.G, h(x *.G inv.G(y)) = h(x) *_ImG inv_ImG(h(y))];  
                            //  byeq Lhom1t, Tre6a(LmG1_type & LimG), Tre2a(Linv_G1_type & LimG);
 EqProof Lhom1t1;
F0 := x in elg.G;              assume;                        // *_ImG := *_G1 | (imG#imG);             // *_G1 := *(group).G1;
F01 := y in elg.G;             assume;                        // ! L12 := *_ImG = *.ImG; 
F02 := inv.G1(h(y)) in imG;    is L11(h(y));                  // ! L11 := A[x_imG, inv_G1(x) in imG];
F1 := h(x *.G inv.G(y));       by Lhom1t;                     // ! Lhom1t := A[x,y:elg.G, h(x *_G inv_G(y)) = h(x) *_G1 inv_G1(h(y))];
F2 := h(x) *.G1 inv.G1(h(y));  by Tre6a(LmG1_type & LimG);    // !! Tre6a := f in fn(A#A,A) & B <: A -> A[x,y:B, f(x,y) = (f|(B#B))(x,y)];  
F3 := h(x) *_ImG inv.G1(h(y)); by Tre2a(Linv_G1_type & LimG); // !! Tre2a := f in fn(A,B) & C <: A -> A[x: C,  f(x) = (f|C)(x)];
F4 := h(x) *_ImG inv_ImG(h(y))
 end EqProof Lhom1t1;

// ! Lhom1 := A[x:elg.G, h(x) in imG];  // !! Tre6a := f in fn(A#A,A) & B <: A -> A[x,y:B, f(x,y) = (f|(B#B))(x,y) ]; 
// !! Tre2 := f in fn(A,B) & C <: A -> A[x: C,  (f|C)(x) = f(x)];
// !! Tre2a := f in fn(A,B) & C <: A -> A[x: C,  f(x) = (f|C)(x)];
// ! Linv_G1_type := inv_G1 in fn(elg.G1, elg.G1);

! Lhomconj := A[a:elg.G, b:elg.G, h(a *.G b *.G inv.G(a)) = h(a) *.G1 h(b) *.G1 inv.G1(h(a))];  // conj: conjugate;
 EqProof Lhomconj;
F0 := a in elg.G;                              assume;    // if F0, F01 are absent then error;
F01 := b in elg.G;                             assume;
F1 := h(a *.G b *_G inv.G(a));                 by Axhom;  // Axhom := A[x,y: elg.G, h(x *.G y) = h(x) *.G1 h(y)] };  
F2 := h(a *.G b) *.G1 h(inv.G(a));             by Axhom;
F3 := h(a) *.G1 h(b) *.G1 h(inv.G(a));         by Lhominv; //! Lhominv  := A[x:elg.G, h((inv_G)(x)) = inv_G1(h(x)) ];
F4 :=  h(a) *.G1 h(b) *.G1 inv_G1(h(a));
 end EqProof Lhomconj;

! Thomconj := A[a:elg.G, b:elg.G, h(a *.G b *.G inv.G(a)) = h(a) *_ImG h(b) *_ImG inv_ImG(h(a))];
 EqProof Thomconj;
F0 := a in elg.G;                              assume;            // if F0, F01 are absent then error;
F01 := b in elg.G;                             assume;
F02 := inv.G1(h(a)) in imG;                    is L11(h(a));      // ! L11 := A[x_imG, inv.G1(x) in imG];
F1 := h(a *.G b *.G inv.G(a));                 by Lhomconj;   
F2 := h(a) *.G1 h(b) *.G1 inv.G1(h(a));        by -L09, -L09;     // ! L09 := A[x,y: imG, x *_ImG y = x *_G1 y];
F3 := h(a) *_ImG h(b) *_ImG inv.G1(h(a));      by -L10;           // ! L10 := A[x_imG, inv_ImG(x) = inv_G1(x)];
F4 := h(a) *_ImG h(b) *_ImG inv_ImG(h(a));
 end EqProof Thomconj;
                                                                     // ?? conj := F[x,y:elg, x*y*inv(x)];
! Lhomconj1 :=  A[x,y: elg.G, h(conj.G(x,y)) = conj.ImG(h(x),h(y))];  // !! Axconj := A[x,y:elg, conj(x,y) = x*y*inv(x)];
 EqProof Lhomconj1;
F0 := x in elg.G;                                           assume;
F01 := y in elg.G;                                          assume;
// F02 := A[x,y:elg.G, conj.G(x,y) = x *_G y *_G inv_G(x)]; is Axconj.G;
F1 := h(conj.G(x,y));                                       by Axconj.G; 
F2 := h(x *_G y *_G inv_G(x));                              by Thomconj;
F3 := h(x) *_ImG h(y) *_ImG inv_ImG(h(x));                  by -Linv_ImG1;  // ! Linv_ImG1 := inv.ImG = inv_ImG;        
F4 := h(x) *_ImG h(y) *_ImG inv.ImG(h(x));                  by -(Axconj.ImG(h(x),h(y)));
F5 := conj.ImG(h(x),h(y)); 
 end EqProof Lhomconj1;
 
! LhomNim    := A[N: nsubgr.G, h(N) in nsubgr.ImG];
 Proof LhomNim;                                  // TN7a := All(K, K in nsubgr == K in subgr & A[x:elg,z:K, conj(x.z) in K]);    
F0 := N in nsubgr.G;                             assume; by TN7a.G; F01 & F02; 
F01 := N in subgr.G;
F02 := A[x:elg.G,z:N, conj.G(x,z) in N];         // conj.G(x,z) = x *_G z *_G inv_G(x);
N1 := h(N);                                      // h(N) = im(h|N)  
G0 := N1 in nsubgr.ImG;                          by TN7a.ImG; G01 & G02;
G01 := N1 in subgr.ImG;                          is Lhomim1(N);          // ! Lhomim1 := A[H: subgr.G, h(H) in subgr.ImG];
G02 := A[x1:imG,z1:N1, conj.ImG(x1,z1) in N1];
  Proof G02;                                     // !! TimE := All(y, y in im(f) == E[x:dom(f), y = f(x)]);
K0 := x1 in imG;                                 assume; by TimE@FN;     // imG := im(h); 
K01 := E[x:dom(h), x1 = h(x)];                   by Lhomdom;             // ! Lhomdom := dom(h) = elg.G;   
K1 :=  Ex[x:elg.G, K1a := x1 = h(x)];   
K2 := z1 in N1;                                  assume; by AxhP;        // !! AxhP := A[B_P_elg_G, h(B) = im(h|B) ]; // h(N) = im(h|N)  
K3 := z1 in im(h|N);                             by TimreE@fA;           // !! TimreE := All(y,y in im(f|A) == E[x:A, f(x) = y]);
K4 := Ex[z:N, K4a := h(z) = z1];                
K5 := conj.G(x,z) in N;                          is F02;                 // Lhomconj1 :=  A[x,z: elg.G, h(conj.G(x,z)) = conj.ImG(h(x),h(z)]
K6 := h(conj.G(x,z)) in im(h|N);                 is Treim2(h,N); by -AxhP; // fA :: !! Treim2 := A[x:A, f(x) in im(f|A)]; 
K61 := h(conj.G(x,z)) in N1;                     by Lhomconj1;                                                                                    
K7 := conj.ImG(h(x),h(z)) in N1;                 by -K1a, K4a;           // is ??? // x *_G *_z *_G *_inv_G(x)
G2 := conj.ImG(x1,z1) in N1;                                              
  end Proof G02;
 end Proof LhomNim;

! Lhompreim := A[H1:subgr.ImG, preim.h(H1) in subgr.G];
 Proof Lhompreim;
H := preim.h(H1);
F0 := H1 in subgr.ImG;              assume;     // !! Lpreim1 := A[Y:P[im(f)], Y in P1[im(f)] == preim(Y) in P1[dom(f)]];
F0a := H1 in P1[imG];               is AxHt.H1; by Lpreim1.h;  // AxHt := H in P1[elg];  
F0b := H in P1[dom(h)];             by Lhomdom;                // !! Lhomdom := dom(h) = elg.G;
F0c := H in P1[elg.G];
G0 := H in subgr.G;                 by Tsubgrin1t.G; F0c & G1; // Tsubgrin1t := V in subgr == V in P1[elg] & A[x,y: V, x*inv(y) in V];
G1 := A[x,y: H, x *_G inv_G(y) in H];
  Proof G1;
F01 := x in H;                      assume; by Lpreim2.h;      // !! Lpreim2 := A[x:dom(f),Y:P[im(f)], x in preim(Y) == f(x) in Y];   
F01a := (x1 := h(x)) in H1;  
F02 := y in H;                      assume; by Lpreim2.h;      // ! Linv_ImG1 := inv.ImG = inv_ImG;
F02a := (y1 := h(y)) in H1;                                    //  LH3a := inv.Gr = inv_Gr; // ! Linv_ImG1 := inv.ImG = inv_ImG; 
F03 := A[x,y: H1, x *_ImG inv_ImG(y) in H1];    by -Linv_ImG1; is LHinv4.H1;      // !! LHinv4 := A[x,y: H, x*inv(y) in H];
F1 := x1 *_ImG inv_ImG(y1) in H1;    is F03;    by -Lhom1t1;   // ! Lhom1t := A[x,y:elg.G, h(x *_G inv_G(y)) = h(x) *_G1 inv_G1(h(y))]; 
F2 := h(x *_G inv_G(y)) in H1;                  by -(Lpreim2.h);
F3 := x *_G inv_G(y) in H;   
  end Proof G1;
 end Proof Lhompreim;

! LhomNpreim := A[N1:nsubgr.ImG, preim.h(N1) in nsubgr.G];
 Proof LhomNpreim;
F0 := N1 in nsubgr.ImG;           assume; by TN7.ImG;  F0a & F0b;
F0a := N1 in subgr.ImG;            //  TN7 := All(K, K in nsubgr == K in subgr & A[x:elg,z:K, x*z*inv(x) in K]);
F0b := A[x:imG,k:N1, x *_ImG k *_ImG inv.ImG(x) in N1];
N := preim.h(N1);
F1 := N in subgr.G;               is Lhompreim;
G0 := N in nsubgr.G;              by TN7.G; F1 & G1;
G1 := A[x:elg.G, n:N, x *_G n *_G inv_G(x) in N];
  Proof G1;    // !! Thomconj := A[a:elg.G, b:elg.G, h(a *_G b *_G inv_G(a)) = h(a) *_ImG h(b) *_ImG inv_ImG(h(a))];
F0 := x in elg.G;                   assume;
F00 := A[x:dom(h),Y:P[im(h)], x in preim.h(Y) == h(x) in Y]; is Lpreim2.h;
 x=x; // !! F01a := n in dom(h);   // to keep numeration; 
F01 := n in N;                      assume;                by F00; // !! Lpreim2 := A[x:dom(f),Y:P[im(f)], x in preim(Y) == f(x) in Y]; 
F03 := h(n) in N1;
F04 := h(x) in imG;             is Timval.h;                // ! Timval := A[x:dom(f), f(x) in im(f)];
F1 := h(x *_G n *_G inv_G(x)) = h(x) *_ImG h(n) *_ImG inv_ImG(h(x)); is Thomconj;
F2 := h(x) *_ImG h(n) *_ImG inv.ImG(h(x)) in N1;            is F0b; by Linv_ImG1, -F1; // ! Linv_ImG1 := inv.ImG = inv_ImG;
F3 := h(x *_G n *_G inv_G(x)) in N1;                        by -(Lpreim2.h);
F4 := x *_G n *_G inv_G(x) in N;
  end Proof G1;
 end Proof LhomNpreim;
// ]; // dHG :: [
]; // hom :: [

// ism := hom && h in bfn(elg.G, elg.G1);
ism := {f ; Axf := f in bfn(elg.G, elg.G1);                      // GG1 :: ism :=
          Axhom := A[x,y: elg.G, f(x *.G y) = f(x) *.G1 f(y)] }; 
! Tismin := All(f, f in ism(G,G1) == f in bfn(elg.G, elg.G1) & A[x,y: elg.G, f(x *.G y) = f(x) *.G1 f(y)]);  is Axab;

dcl[~, fn(group#group, bool)];   // isomorphic;
!! Axisomorphic := G ~ G1 == Exist(f, f in ism(G,G1));  // ExP := Exist(x,P(x));
                                                        // !! AxExist := ExP(a) -> ExP; // ExP(a) denotes P(a); Witness;
! Tisom := f in ism(G,G1) -> G ~ G1;
 Proof Tisom;
F0 := f in ism(G,G1);                 assume;
F1 := Exist(f, f in ism(G,G1));       is Witness(f); by -Axisomorphic;
F2 :=  G ~ G1;
 end Proof Tisom;

// epi := hom && h in sfn(elg.G, elg.G1);
epi :=  {f ; Axf := f in sfn(elg.G, elg.G1); 
             Axhom := A[x,y: elg.G, f(x *.G y) = f(x) *.G1 f(y)] }; 


! Tepiin := f in epi == f in sfn(elg.G, elg.G1) & A[x,y: elg.G, f(x *.G y) = f(x) *.G1 f(y)];

// mon := hom && h in ifn(elg.G, elg.G1);
mon := {f ; Axf := f in ifn(elg.G, elg.G1); 
          Axhom := A[x,y: elg.G, f(x *.G y) = f(x) *.G1 f(y)] }; 

! Tmonin := f in mon == f in ifn(elg.G, elg.G1) & A[x,y: elg.G, f(x *.G y) = f(x) *.G1 f(y)];

! Thom1 := ism <: hom;                                    // is TscIn;
! Thom2 := epi <: hom;                                    // is TscIn;
! Thom3 := mon <: hom;                                    // is TscIn;
! Tismepi := ism <: epi;                                  // is TscInimp;   // Tism1
! Tismmon := ism <: mon;                                  // is TscInimp;   // Tism2
! Tismepm := ism = epi /\  mon;                           // Tism3

hom :: [                                                  // GG1::hom::

<|_G := (<| @ group).G;  // <| := F[HK, H<:K & A[x:K, x*H = H*x]]; cannot use <|(group), because <| is not primitive(abt) method;
! L0_type := <|_G in fn(subgr.G # subgr.G, bool);      is Tisnorm.G;   // ! Tisnorm := <| @ group in fn(subgr#subgr, bool); 
<|_G1 := (<| @ group).G1;
! L01_type := <|_G1 in fn(subgr.G1 # subgr.G1, bool);  is Tisnorm.G1; 
! L01 := subgr.G <: P1[elg.G];                         is Tsubgr3.G;     // ! Tsubgr3 := subgr <: P1[elg];
! L02 := nsubgr.G <: P1[elg.G];                        is Tnsubgr2.G;    // ! Tnsubgr2 := nsubgr <: P1[elg];

! LeImGn := {e.G1} in nsubgr.ImG;           is Tisnorm4b(ImG,G1)({e.G1})(L05b); // !! L05a := {e.G1} in P[imG];
! Lpreimh := preim.h = F[Y: P[im(h)], {x:dom(h); h(x) in Y} ]; byeq Red;

ker := preim.h({e.G1});                     // ker means ker(h); // ! LhomNpreim := A[N1:nsubgr.ImG, preim.h(N1) in nsubgr.G];
! Lkern := ker in nsubgr.G;                 is LhomNpreim;  // used !! LeImGn := {e.G1} in nsubgr.ImG; ! LeG1n := {e.G1} in nsubgr.G1;
! Lkern1 := ker <|.G elg.G;                 is TN5.ker;     // ! TN5 := N <| elg;     //! Tisnormelg := A[H:subgr, H in nsubgr == H <| elg];
! Lkern2 := nsubgr.G <: subgr.G;            is Tnsubgr1.G;  // ! Tnsubgr1 := nsubgr <: subgr;
! Lkers := ker in subgr.G;                  is TinIn(Lkern & Lkern2);      // TinIn := x in X2 & X2 <: Y2 -> x in Y2;
! Lker1 := A[x:elg.G, x in ker == h(x) = e.G1]; byeq Lpreim2.h,  Axcoll1;  // !! Axcoll1 := All(x, All(a, x in {a} == x = a));  

! Lker2 := A[x,z:elg.G, h(x)=h(z) == h(x *.G inv.G(z)) = e.G1];
 EqProof Lker2;
F0 := x in elg.G;                           assume;
F01 := z in elg.G;                          assume;             // Axhom := A[x,y: elg.G, h(x *_G y) = h(x) *_G1 h(y)];
F1 := h(x)=h(z);                            by -(Tinvm2a.G1);   // ! Tinvm2a := A[x,y:elg, x * inv(y) = e == x = y];
F2 := h(x) *.G1 inv.G1(h(z)) = e.G1;        by -Lhominv,-Axhom; // ! Lhominv  := A[x:elg.G, h((inv_G)(x)) = inv_G1(h(x)) ];
F3 := h(x *.G inv.G(z)) = e.G1;
 end EqProof Lker2;
 
// !! Tabred                                                               // ! TminS1a := A[a,x:elg, B:P[elg], a*inv(x) in B == a in B*x];  

! Lker3a := nsubgr.G <: P[elg.G];          is Tnsubgr2a.G;      // ! Tnsubgr2a := nsubgr <: P[elg];
! Lker3 := A[x,z: elg.G, h(x)=h(z) == x *.G inv.G(z) in ker];   byeq Lker2, -Lker1; by TminS1a.G, -(TN9.G);
! Lker4 := A[x,z: elg.G, h(x)=h(z) == x in z *_eS_G ker];       // *_eS_G := *(meS).G;  // !! TN9 := A[x:elg, N: nsubgr, x*N = N*x];

! Tker := ker = {x:elg.G; h(x) = e.G1};  // byeq Lpreimh,Lhomdom, Red;        // same as ker = {x; x in elg.G & h(x) = e.G1}
 EqProof Tker;                                 // ! Lpreimh := preim.h = F[Y: P[im(h)], {x: dom(h); h(x) in Y} ];
F1 := ker;                                      by  Lpreimh;                     // ker := preim.h({e.G1});  
F2 := F[Y: P[im(h)], {x: dom(h); h(x) in Y} ]({e.G1}); by Red("F");
F3 := {x:dom(h); h(x) in {e.G1} };              by Lhomdom, Axcoll1;             // !! Lhomdom := dom(h) = elg.G;
F4 := {x:elg.G; h(x) = e.G1};                                              // !! Axcoll1 := All(x, All(a, x in {a} == x = a));      
 end EqProof Tker;

/*                                                               // ! Lhomdom := dom(h) = elg.G; 
dGN := {G,N; AxG := G in group, AxN := N in nsubgr.G; };        // !! Lpreim2 := A[x:dom(f),Y:P[im(f)], x in preim(Y) == f(x) in Y];  
dcl[/, fn(dGN, group)];                                  
!! Axfgr := A[dGN, G/N = Fgr.N];                       // Fgr := [CS, *_CS];  // *_CS := *@mSS | (CS # CS); 
dGN :: [
 ! TFgr := G/N = [CS.N, *_CS.N];                       byeq Axfgr, Red;       // *_CS.ker = *_CS
]; // dGN :: [
*/                                                       // nsubgr:: *_CS := *@mSS | (CS # CS);   // CS means CS.N

Gk := G/ker;                                           // nsubgr:: CS := lcosets.N;
var y,a, elg.G;                                        // !! LGk0 := *.Gk = *_CS.ker;              
! LGk_type := [CS.ker, *_CS.ker] in group;             is TFgr_type.ker;       // ! TFgr_type := Fgr in group;    // Fgr := [CS, *_CS]; 
!! TGk_type := Gk in group;
! TGk := Gk = [CS.ker, *_CS.ker];                      is TFgr@dGN(G, ker);    // ! TFgr := G/N = [CS.N, *_CS.N]; 
! LGkelg := elg.Gk = CS.ker;                           byeq TGk,Red;
! LGkm0 := *.Gk = *_CS.ker;                            byeq TGk,Red;
! LGkm1 := CS.ker <: P[elg.G];                         is LCSInP.ker;          // ! LCSInP := CS <: P[elg]; 
// ! LGkm1 := *_CS.ker = *(mSS).G | (CS.ker # CS.ker);    is AxmCS.ker;        // ! AxmCS := *_CS = *@mSS | (CS # CS);
// ! LGkm := *_Gk = *(mSS).G | (CS.ker # CS.ker);         byeq LGkm0, LGkm1;
! LGkmA := A[X,Y: CS.ker, X *.Gk Y = X *(mSS).G Y];    by LGkm0; is LCSm.ker;  // LCSm := A[Q1,Q2:CS, Q1 *_CS Q2 = Q1*Q2];
! LGkelg1 := elg.Gk <: P[elg.G];                       by LGkelg; LGkm1;
! LGkelg2 := A[z:elg.G, z *_eS_G ker in elg.Gk];       by LGkelg; is LCSl.ker; // ! LCSl := A[g:elg, g*N in CS];
                                                       // !! Tqinvbfn := qinv in bfn(im(f), part);    // part := im(qinv);
// iq := inv(qinv);                                    // FN :: !! Tiq := iq in bfn(im(qinv), im(f)); 
! Liqh1_type := iq.h in bfn(im(qinv.h), im(h));        is Tiq.h;   // iq.h in bfn(CS.ker, im(h)); 
! Lqinvh_type := qinv.h in bfn(im(h), im(qinv.h));     is Tqinvbfn.h;                 // !! Tqinvbfn := qinv in bfn(im(f), part);  
! L15 := dom(qinv.h) = im(h);                          is Tbfndom(Lqinvh_type);       // !! Tbfndom := f in bfn(A,B) -> dom(f) = A;

! L16 := x in a *_eS_G ker -> x in elg.G;              is typeaxiom;  // x in t1 -> x in t2 is true if t1 in P[t2];  (typ(t1) = P[t2]);
                                                                      //  
x_dom_h := {x; x in dom(h)};                           // !! Tqinv := A[y:im(f), qinv(y) = {x: dom(f); f(x) = y} ];

! Lqinvh1 := A[z:dom(h), qinv.h(h(z)) = z *_eS_G ker];
 EqProof Lqinvh1; 
F0 := z in dom(h);     assume;   by Lhomdom;  // FN :: !! Tqinv1 := A[z:dom(f), qinv(f(z)) = {x; x in dom(f) & f(x) = f(z)} ];                      
F01 := z in elg.G;                            // ! Lhomdom := dom(h) = elg.G;
F02 := y in elg.G & y in z *_eS_G ker == y in z *_eS_G ker;  is Absorb1(L16);  // ! Absorb1  := (q->p) == (p&q == q);
F1 := qinv.h(h(z));                           by Tqinv1.h;        // ! Lker4 := A[x,z: elg.G, h(x)=h(z) == x in z *_eS_G ker];      
F2 := {x; x in dom(h) & h(x)=h(z)};           by Lhomdom, Lker4;  
F3 := {x3; x3 in elg.G & x3 in z *_eS_G ker}; by F02;  // by Absorb1(L16);    // ! Absorb1  := (q->p) == (p&q == q);
F4 := {x4; x4 in z *_eS_G ker};               by Tabin;
F5 := z *_eS_G ker;
 end EqProof Lqinvh1;

! Lqinvh2_type := inv(qinv.h) in bfn(im(qinv.h), im(h)); is Tbfninv(Lqinvh_type);  // !! Tbfninv  := f in bfn(A,B) -> inv(f) in bfn(B,A);

! LiqhCS := im(qinv.h) = CS.ker;
 EqProof LiqhCS;                              // ! L15 := dom(qinv.h) = im(h);
F0 := CS.ker = R[x:elg.G, x *_eS_G ker];      is LCS2.ker;                // ! LCS2 := CS = R[g:elg, g*N];
F1 := im(qinv.h);                             by Tim@FN, L15;             // FN :: !! Tim := im(f) = R[x:dom(f), f(x)]; 
F2 := R[x:im(h), qinv.h(x)];                  by TRim@FN;                 // !! TRim := R[y:im(f), Q(y)] = R[x:dom(f), Q(f(x))]; 
F3 := R[x:dom(h), qinv.h(h(x))];              by Lqinvh1,Lhomdom;         // ??? double name F3 (second F3 is now F4) undetected; ???
F4 := R[x:elg.G, x *_eS_G ker];               by -F0;
F5 := CS.ker;    
 end EqProof LiqhCS;     

! LIqh2 := A[x_dom_h,  x *_eS_G ker in im(qinv.h)];  by Lhomdom, LiqhCS; is LCSl.ker;       // ! LCSl := A[g:elg, g*N in CS]; 

! LIqh2a := A[x:elg.G,  x *_eS_G ker in CS.ker];     by -Lhomdom, -LiqhCS; LIqh2;  // ! Lhomdom := dom(h) = elg.G;

! Liqh3 := A[x_dom_h, h(x) = iq.h(x *_eS_G ker)];    // *_eS_G := *(meS).G;
 EqProof Liqh3;                                      // !! Tbfninv3 := A[t:set, g: bfn(im(f), t), A[x:dom(f), f(x) = inv(g)(g(f(x)))]];
F0 := x in dom(h);                                   assume;
F01 := A[x_dom_h, h(x) = inv(qinv.h)(qinv.h(h(x)))]; is Tbfninv3.h(im(qinv.h), qinv.h); // !! Lqinvh_type := qinv.h in bfn(im(h), im(qinv.h));       
F02 := iq.h = inv(qinv.h);                           byeq Red;
F1 := h(x);                                          by F01;
F2 := inv(qinv.h)(qinv.h(h(x)));                     by -F02, Lqinvh1;
F3 := iq.h(x *_eS_G ker);               
 end EqProof Liqh3;

! Liqh_type := iq.h in bfn(elg.Gk, elg.ImG);    by LGkelg, LImGelg, -LiqhCS;  Liqh1_type; // ! LImGelg := elg.ImG = imG;

! Lism_iqh := A[X,Y: elg.Gk, iq.h(X *.Gk Y) = iq.h(X) *.ImG iq.h(Y)];                       // Gk := G/ker;
 EqProof Lism_iqh;
F0 := X in elg.Gk;                              assume;  by LGkelg;  // ! LGkelg := elg.Gk = CS.ker; 
F01 := X in CS.ker;                             by LCSin2.ker;       // ! LCSin2 := X in CS == E[g:elg, X = g*N];
F02 := Ex[x:elg.G, F02a := X = x *_eS_G ker];
F03 := Y in elg.Gk;                             assume;  by LGkelg;  // ! LGkelg := elg.Gk = CS.ker; 
F04 := Y in CS.ker;                             by LCSin2.ker;       // ! LCSin2 := X in CS == E[g:elg, X = g*N];
F05 := Ex[y:elg.G, F05a := Y = y *_eS_G ker];
F06 := x *_eS_G ker in CS.ker;                  by -F02a; F01;
F07 := y *_eS_G ker in CS.ker;                  by -F05a; F04;       // ! LGkm0 := *.Gk = *_CS.ker; 
F1 := iq.h(X *.Gk Y);                           by F02a, F05a;       // ! LGkmA := A[X,Y: CS.ker, X *.Gk Y = X *(mSS).G Y]; 
F2 := iq.h((x *_eS_G ker) *.Gk (y *_eS_G ker)); by LGkmA, LN6l.ker;  // ! LN6l := A[g1,g2:elg, (g1*N) * (g2*N) = (g1*g2) * N];
F3 := iq.h(x *.G y *_eS_G ker);                 by -Liqh3;           // ! Liqh3 := A[x_dom_h, h(x) = iq.h(x *_eS_G ker)];
F4 := h(x *.G y);                               by Axhom1;           // !! Axhom1 :=  A[x,y: elg.G, h(x *_G y) = h(x) *.ImG h(y)]; // not axiom; 
F5 := h(x) *.ImG h(y);                          by Liqh3;            // *_G := *(group).G;
F6 := iq.h(x *_eS_G ker) *.ImG iq.h(y *_eS_G ker); by -F02a, -F05a;
F7 := iq.h(X) *.ImG iq.h(Y);
 end EqProof Lism_iqh;
                        GG1 :: [ !! Tismin1 := f in ism(G,G1) == f in bfn(elg.G, elg.G1) & A[x,y: elg.G, f(x *.G y) = f(x) *.G1 f(y)]; ];
// GkImG := [Gk, ImG];
// !! LGkImG_type := GkImG in GG1;
! Lism0 := iq.h in ism(Gk, ImG);                by Tismin1(Gk,ImG);  Liqh_type & Lism_iqh;       // ker = ker(h) // Gk := G/ker;
! Tism0 := Gk ~ ImG;                            is Tisom(Lism0);                        // ! Tisom := f in ism(G,G1) -> G ~ G1;

! Tism0a := im(h) = elg.G1 -> Gk ~ G1;                // Gk := G/ker; // ImG := Gr.imG; // ! TImG := ImG = [imG, *_ImG]; 
 Proof Tism0a;
F0 := im(h) = elg.G1;               assume;
F1 := ImG = G1;                     is LImGG1a(F0);   // ! LImGG1a := imG = elg.G1 -> ImG = G1; // because imG := im(h);
Goal := Gk ~ G1;                    by -F1; Tism0; 
 end Proof Tism0a;
 
 ]; // hom ::     //   ! Tismin := All(f, f in ism(G,G1) == f in bfn(elg.G, elg.G1) & A[x,y: elg.G, f(x *.G y) = f(x) *.G1 f(y)]);
]; // GG1 :: [   // 2

/*
 The First Isomorhism Theorem (A Course in Group Theory, by John F.Humphreys, Oxford Science Publications, 1996), Theorem 8.15, p. 72-73.
Let H be a subgroup of the group G and N be a normal subgroup of G. 
Then N is a normal subgroup of the group HN and N/\H is a normal subgroup of H. Futhermore H/(H/\N) ~ HN/N;

   Proof sketch
1. g := F[h:H, h*N];

2. g in hom(Gr(H), (H*N)/N); see g1
2.1 surjective(g);

3. ker(g) = H/\N; 

4. H/(H/\N) ~ H*N/N;  follows immediately from the Homomorphism Theorem;
*/

group :: [ 

HN :: [     // #2

! LHN1 := Gr.H/N = H/N;
 EqProof LHN1;                              // used in next line: HN :: ! AxN := N in nsubgr.(GrH := Gr.H); 
F1 := Gr.H/N;               by Axfgr;   // !! Axfgr := A[dGN, G/N = Fgr.N]; // dGN := {G,N; AxG := G in group, AxN := N in nsubgr.G; }; 
F2 := Fgr.N;                by -AxFgr;      // HN :: !! AxFgr := H/N = Fgr.N;  
F3 := H/N;  
end EqProof LHN1;

]; // HN :: [  #2

NH :: [ // #2 NH := nsubgr && subgr; N,H defined in nsubgr,subgr;  // HN :: ! L0a := H*N = N*H;
// NH :: ! LHNsbg := H*N in subgr;
// NH :: !! LNnHN := N <| H*N;

// GrH := Gr.H;                                // moved to NH #1;
g := F[h:H, h*N];
! L0 := H/\N in subgr;                         is TsbgI@HK;      // HK :: ! TsbgI := H/\K in subgr;   
! L01 := A[h1,h2:H, h1*h2 in H];               is LHm;           // ! LHm := A[x,y: H, x*y in H]; 
! L02 := H*N in subgr;                         is LHNsbg;        // ! LHNsbg := H*N in subgr;
! L03 := N <| H*N;                             is  LNnHN;        // !! LNnHN := N <| H*N;   // HN :: CS1 := R[x:H, x*N];
! L04 := H*N/N = [CS1(H*N,N), *_CS1(H*N,N)];   is Tfgr(H*N,N);   // HN :: *_CS1 := *@mSS|(CS1#CS1); // HN :: ! Tfgr := H/N = [CS1, *_CS1];
! L06 := N ~= {};                              is LHnemp.N;      // ! LHnemp := H ~= {};  // NH :: ! L15 := N in subgr; 
! L07 := dom(g) = H;                           is TFdom;         // ! TFdom   := dom(F[d, g]) = d; 
! L08 := elg.(Gr.H) = H;                       byeq Red;         // is TGrelg;      // ! LGrelg := elg.Gr = H;
! L09 := elg.(H*N/N) = CS1(H*N,N);             byeq L04, Red;     
! L1 := e.(H*N/N) = N;                         is Tfgre1@HN;     // (H*N,N);        // HN :: !! Tfgre1 := e.(H/N) = N; 
! L18 := *.(Gr.H) = *_Gr;                      byeq Red;
! L19 :=  *.(H*N/N) = *_CS1(H*N,N);            byeq Red;         // ??? L04 ????
! LNH2 := *_CS1(H*N,N) = *@mSS|(CS1(H*N,N) # CS1(H*N,N));         is AxmCS1(H*N,N);  //HN :: ! AxmCS1 := *_CS1 = *@mSS|(CS1#CS1);
! LNH3 := *.(H*N/N) = *@mSS|(CS1(H*N,N) # CS1(H*N,N));     byeq L19,LNH2;            // move up or research the necessity;
! LNH4 := H in subgr.GrH;                      by TGr_H; is Telg.Gr;      //! Telg := elg in subgr;  // ! TGr_H := Gr.H = Gr; 
                 
! Lg1 := im(g) =  CS1(H*N,N);
 EqProof -Lg1;
F1 := CS1(H*N,N);                      by Red;             // ??? Red("adt") ???
F2 := R[x:H*N, x*N];                   by TmSSR;           // ! TmSSR := A[A:P[elg], B:P[elg], A * B = R[a:A,b:B, a*b]]; 
F3 := R[x: R[h:H,n:N, h*n], x*N];      by TRR;             // ! TRR  := R[x:R[d,f], G(x)] = R[d, G(f)];  
F4 := R[h:H,n:N, (h*n)*N];             by LNH1;            // !! LNH1 := A[h:H,n:N, (h*n)*N = h*N]
F5 := R[h:H,n:N, h*N];                 by Red("free",2) ;  // second bvar(n) in F5 is not used in h*N;         
F6 := R[h:H, h*N];                     by -TimF;           // !! TimF := im(F[d, g]) = R[d, g];
F7 := im(g);
 end EqProof -Lg1;
                                      // g := F[h:H, h*N]; // ! L07 := dom(g) = H;   // first H is in g 
! Lg2 := g in fn(H, CS1(H*N,N));       by -L07,2, -Lg1; is Tfndomim@FN;  // FN :: !! Tfndomim := f in fn(dom(f), im(f));

! Lg2a := g in fn(elg.(Gr.H), elg.(H*N/N)); by L08,L09; Lg2;  // !! L08 := elg.(Gr.H) = H; // !! L09 := elg.(H*N/N) = CS1(H*N,N);

! Lg3 := A[h1,h2:H, g(h1*h2) = g(h1)*g(h2)];       // ! Lg3a := A[h1,h2:elg.(Gr.H), g(h1*h2) = g(h1)*g(h2)];
 EqProof -Lg3;
F0 := h1 in H;                         assume;
F01 := h2 in H;                        assume;
F02 := g(h1*h2) = (h1*h2)*N;           byeq Red("F");
F1 := g(h1)*g(h2);                     by Red("F");
F2 := (h1*N)*(h2*N);                   by LN6l.N;          // ! LN6l := A[g1,g2:elg, (g1*N) * (g2*N) = (g1*g2) * N];
F3 := (h1*h2)*N;                       by -F02;
F4 := g(h1*h2);
 end EqProof -Lg3;                     // !! [Gr.H, H*N/N] in GG1; ERROR in pars;              
                        // GG1 :: !! Thomin := All(f,f in hom(G,G1) == f in fn(elg.G, elg.G1) & A[x,y: elg.G, f(x *_G y) = f(x) *_G1 f(y)]);
! L10 := *.(Gr.H) <: *(group);                   by L18; is LHmIn;  // ! L18 := *.(Gr.H) = *_Gr;  // !! LHmIn := *_Gr <: *(group);           
! L11 := *.(H*N/N) <: *(mSS);                    by LNH3; is TreIn2@FN; // FN :: !! TreIn2 := f|(A#B) <: f;  // !! TreIn := f|A <: f;

! Lg4 := g in hom(Gr.H, H*N/N);                  by Thomin(Gr.H, H*N/N); Lg2a & Lg3;     // Gr.H = Gr;  Gr(H): was error;        
  
! Lg5 := ker(g) = H/\N;                          // host(ker) = hom; ! Lg2 := g = F[x:H, x*N];
 EqProof Lg5;                                    // Tker := ker = {x; x in elg.G; f(x) = e.G1};
F1 := ker(g);                                    by Tker(g);      // !! Tker := ker = {x, x in elg.G, h(x) = e.G1};
F2 := {x: elg.(Gr.H); g(x) = e.(H*N/N)};    by L08, L1;      // ! LGrelg := elg.Gr = H;
F3 := {x:H; g(x) = N};                     by Red("F");     // g(x) = x*N;
F4a := {x:H; x*N = N};                     by LH7l.N;       //  by LH7l_NH(x@F4a);    // ! LH7l := A[g:elg, g*H = H == g in H];
F5 := {x:H; x in N};                       by TabI;         // !! TabI := {x: A ; x in B} = A/\B;     
F6 := H/\N;
 end EqProof Lg5;
 
// M := [GrH, H*N/N];
// !! LM1_type := M in GG1;                       // from g in hom(GrH, H*N/N) can build [GrH, H*N] which is in GG1;
// !! Lg_type := g in hom.M;                       // g in hom(GrH, H*N/N)

// !!  L23 := subgr.GrH <: subgr;                moved to NH #1 as LNH_GrH; // ! TinIn := x in X2 & X2 <: Y2 -> x in Y2;
! Lkerg_type := ker(g) in subgr.GrH;             is Lkers.g;    // used val(Lkers.g) !! Lkers := ker in subgr.G;// for type checking Lg6;
! L24 := ker(g) in subgr;                        is TinIn(Lkerg_type & LNH_GrH);      // !! LNH_GrH := subgr.GrH <: subgr;
                                                 // !! L24 := subgr.GrH <: subgr;     // did not work instead of !! L24 := ker(g) in subgr; 
! L20 := ker(g) <: H;                            by Lg5; is TIIn1;                    // ! TIIn1 := X/\Y <: X; // use in ismd not istr2 ?
! Lg6 := ker(g) <|.GrH H == ker(g) <| H;         is LHK1_1(ker(g), H);    // HK1 :: ! LHK1_1 := H <|.GrK K == H <| K; 
                                                 // ! Lkern1 := ker <|.G elg.G;  // ker(g) <|.(Gr.H) elg.(Gr.H) ERROR in pars;
! Lg7 := ker(g) <|.GrH elg.GrH;                  is  Lkern1.g;  by L08, Lg6; // ! L08 := elg.(Gr.H) = H;  
! Lg8 := ker(g) <| H;                            by Lg5;
! L05 := H/\N <| H;                               
! L23 := ker(g) in subgr;                        is TinIn(Lkerg_type & LNH_GrH);      // ! LNH_GrH := subgr.GrH <: subgr; 
! Lg9 := ker(g) in nsubgr.GrH;                   by -Tisnorm1A; Lg8;  // ! Tisnorm1A := A[H,K:subgr, H<|K == H in nsubgr.GrK];
! Lg10 := im(g) = elg.(H*N/N) -> GrH/ker(g) ~ (H*N/N);   is Tism0a.g;     // Tism0a(g);   // GG1::hom:: !! Tism0a := im(h)==elg.G1 -> Gk ~ G1;  
! Lg11 := im(g) = elg.(H*N/N);                   byeq Lg1, -L09;// Lg1 := im(g) =  CS1(H*N,N); // ! L09 := elg.(H*N/N) = CS1(H*N,N);  
! Lg12 := GrH/ker(g) ~ (H*N/N);                  is Lg10(Lg11); by Lg5;   // ! Lg5 := ker(g) = H/\N; // CS1 := R[x:H, x*N];  
! Lg13 := GrH/(H/\N) ~ (H*N)/N;                  by LHN1@HN;              // HN :: !! LHN1 := Gr.H/N = H/N;
! Tism1 := H/(H/\N) ~ (H*N)/N;                                            // ! Lg10 := im(g) = elg.(H*N/N) -> GrH/ker(g) ~ (H*N/N);   is Tism0a.g;
 
/*
dGN := {G,N; AxG := G in group, AxN := N in nsubgr.G; };        // !! Lpreim2 := A[x:dom(f),Y:P[im(f)], x in preim(Y) == f(x) in Y];  

dcl[/, fn(dGN, group)];                                  
!! Axfgr := A[dGN, G/N = Fgr.N];                       // Fgr := [CS, *_CS];  // *_CS := *@mSS | (CS # CS); 
dGN :: [
 ! TFgr := G/N = [CS.N, *_CS.N];                       byeq Axfgr, Red;       // *_CS.ker = *_CS
]; // dGN :: [
// dcl[/, fn(HN, group)]; // !! AxFgr := H/N = Fgr.N; ! Tfgr := H/N = [CS1, *_CS1]; 
*/                   

] ]; // NH::[

/*
 The Second Isomorhism Theorem (A Course in Group Theory, by John F.Humphreys, Oxford Science Publications,!996), Theorem 8.16, p. 73.
Let H and N be normal subgroups of the group G with N contained in H. Then H/N is a normal subgroup of G/N, and (G/N)/(G/H) ~ G/H;
   
  Proof sketch      
! Tfgr := H/N = [CS1, *_CS1];                  // CS1 := R[x:H, x*N]; // *_CS1 := *@mSS|(CS1#CS1); // ! L2 := *_CS.N = *_CS1;
! Tfgrm := *.(H/N) = *_CS1;                    byeq Red;   // HN :: *_CS1 := *@mSS|(CS1#CS1);
                                               // ! Tre6 := f in fn(A#A,A) & B <: A -> A[x,y:B, (f|(B#B))(x,y) = f(x,y)];
! Tfgrm1 := A[X,Y: CS1, X *_CS1 Y = X * Y]; is Tre6(TmeSt & L17);  // ! TmeSt := * @ meS in fn(elg # P[elg], P[elg]);  

*/

group :: [ 
HN1 := {H,N; AxH := H in nsubgr, AxN := N in nsubgr, AxNH := N <: H };
HN1 :: [                                                     // !! TinInP := X in Y & Y <: P[Z] -> X <: Z;
! L0 := N <: elg;       is TinInP(AxN & Tnsubgr2a);          // to check n*g; // ! Tnsubgr2a := nsubgr <: P[elg];  
! L00 := H <: elg;      is TinInP(AxH & Tnsubgr2a);
! L01 := H in subgr;    is TinIn(AxH & Tnsubgr1);            // ! TinIn := x in X2 & X2 <: Y2 -> x in Y2; 
! L02 := N in subgr;    is TinIn(AxN & Tnsubgr1);            // ! Tnsubgr1 := nsubgr <: subgr; 
! L03 := N <| elg;      by -Tisnormelg; AxN;                 // ! Tisnormelg := A[H:subgr, H in nsubgr == H <| elg];
! L04 := H <| elg;      by -Tisnormelg; AxH; 

// g_elg := {g; g in elg};                                   // see group;
R := R[g_elg, [g*N, g*H]];
GN := R[g_elg, g*N];       
GH := R[g_elg, g*H]; 
             
! L07 := N <| H;                   is Tisnorm4A1(AxN & AxNH); // ! Tisnorm4A1 := A[H,K:subgr, H in nsubgr & H <: K -> H <| K];   
! LGNelg := elg.(elg/N) = GN;      is Tfgrelg(elg,N); // HN: ! Tfgrelg := elg.(H/N) = CS1;  // HN :: CS1 := R[x:H, x*N]; we are in HN;
! LGHelg := elg.(elg/H) = GH;      is Tfgrelg(elg,H); // HN := {H,N; AxH := H in subgr, AxN0 := N in subgr; AxN1 := N <| H };
! LHNelg := elg.(H/N) = R[x:H, x*N]; is Tfgrelg(H,N);
! LGHe := e.(elg/H) = H;           is Tfgre1(elg,H);  //   Tfgre1 := e.(H/N) = N;
! LR1 := R in REL;                 is TR3;      // !! TR3 := R[d, [F,G]] in REL;
! LRdom := dom(R) = GN;            is TR4;      // !! TR4 := dom(R[d, [F,G]]) = R[d, F];
! LRim := im(R) = GH;              is TR5;      // !! TR5 := im(R[d, [F,G]]) = R[d, G];
! LRR := A[g_elg, [g*N, g*H] in R]; is TAinR;   // !! TAinR   := A[d, f in R[d,f]]; 
! L05 := elg.(elg/N) <: P[elg];    by LGNelg;   is typeaxiom;   // type(GN) = P[P[elg]]; computed automatically;
! L06 := elg.(elg/H) <: P[elg];    by LGHelg;   is typeaxiom;   // type(GH) = P[P[elg]]; computed automatically;

! LRfunc := func(R);
 Proof LRfunc;           by TfuncR@REL;         // REL :: !! TfuncR := func(R) == A[X,Y,Y1:any, [X,Y] in R & [X,Y1] in R -> Y=Y1];
G0 := A[X,Y,Y1:any, [X,Y] in R & [X,Y1] in R -> Y=Y1];
  Proof G0;
F0 := X in any;          assume;
F0a := Y in any;         assume;
F0b := Y1 in any;        assume;           // F(z), G(z) can be used only locally in a theorem, no remote using !!!
F0c := [X,Y] in R;       assume; by TRE2;  // !! TRE2 := [x,y] in R[z:A, [F(z), G(z)]] == E[a:A, x = F(a) & y = G(a)];
F01 := Ex[g:elg, (F01a := X = g*N) & (F01b := Y = g*H)];
F02 := [X,Y1] in R;       assume; by TRE2;  
F03 := Ex[g1:elg, (F03a := X = g1*N) & (F03b := Y1 = g1*H)];
F1 := g*N = g1*N;        is Axeq2a(F01a & F03a);             // !! Axeq2a := a=x & a=y -> x=y;
F2 := Ex[n:N, F2a := g1 = g*n]; is LN12@nsubgr(F1);          // nsubgr :: !! LN12 := A[g,g1: elg, g*N = g1*N -> E[n:N, g1 = g*n]];
F3 := n in H;            is TinIn(n in N & AxNH);
G1 := Y=Y1;
   EqProof -G1;
K1 := Y1;                by F03b;
K2 := g1*H;              by F2a;
K3 := (g*n)*H;           by LH9A(H,g,n);   // !! LH9A := A[H:subgr, x:elg, h:H, (x*h)*H = x*H]; // !! LH9 := A[x:elg, h:H, (x*h)*H = x*H];
K4 := g*H;               by -F01b;
K5 := Y;
   end EqProof -G1;
  end Proof G0;
 end Proof LRfunc;

! LRfn := R in fn(GN,GH);  by -LRdom, -LRim; is TRELfn(LRfunc);  // TRELfn := A[R:REL, func(R) -> R in fn(dom(R), im(R))];
! LRfn1_type := R in fn(elg.(elg/N), elg.(elg/H)); by LGNelg, LGHelg; LRfn;

! LRfn2 := A[g_elg, g*N in GN];     is TAinR;   // !! TAinR   := A[d, f in R[d,f]];  GN := R[g_elg, g*N]; 

! LRfn3 := A[g_elg, R(g*N) = g*H];              // use in fit: ! LGNelg := elg.(elg/N) = GN;
 Proof LRfn3;
F0 := g in elg;                     assume;
F1 := [g*N, g*H] in R;              is LRR;                         // ! LRR := A[g_elg, [g*N, g*H] in R]];          
F2 := R(g*N) = g*H;                 is TfuncRin@REL(LRfunc & F1);   // ! TfuncRin := func(R) & [x,y] in R -> R(x) = y;
 end Proof LRfn3;

! LRfn4 := A[X,Y: elg.(elg/N), X *.(elg/N) Y = X *@mSS Y]; is Tfgrm2(elg,N); // ! Tfgrm2 := A[X,Y: elg.(H/N), X *.(H/N) Y = X * Y];
! LRfn4a := A[X,Y: elg.(elg/H), X *.(elg/H) Y = X *@mSS Y]; is Tfgrm2(elg,H); 

! LRfn5 := A[X,Y: elg.(elg/N), R(X *.(elg/N) Y) = R(X) *.(elg/H) R(Y)];
 EqProof LRfn5;
F0 := X in elg.(elg/N);             assume;  by LGNelg;             // ! LGNelg := elg.(elg/N) = GN;
F01 := X in GN;                     by TRin;   // !! TRin := z in R[d,f] == E[d, z = f]   // GN := R[g_elg, g*N];
F02 := Ex[g:elg, F02a := X = g*N];  
F03 := Y in elg.(elg/N);            assume;  by LGNelg;             // ! LGNelg := elg.(elg/N) = GN;
F04 := Y in GN;                     by TRin;   // !! TRin := z in R[d,f] == E[d, z = f]   // GN := R[g_elg, g*N];
F05 := Ex[g1:elg, F05a := Y = g1*N];  // in Ex[d,P], d must be unnamed !!!
F06 := g*H in elg.(elg/H);          is Tfgrin(elg,H);               // !! Tfgrin := A[x:H, x*N in elg.(H/N)];
F07 := g1*H in elg.(elg/H);         is Tfgrin(elg,H); 
F1 := R(X *.(elg/N) Y);             by F02a,  F05a, LRfn4, LN6l.N, LRfn3;
// F2 := R((g*N) *.(elg/N) (g1*N)); by LRfn4, LN6l.N;    // ! LN6l := A[g1,g2:elg, (g1*N) * (g2*N) = (g1*g2) * N];
// F3 := R((g*g1)*N);               by LRfn3;
F4 := (g*g1)*H;                     by -(LN6l.H);
F5 := (g*H)*(g1*H);                 by -LRfn4a, -LRfn3;
F6 := R(g*N) *.(elg/H) R(g1*N);     by -F02a, -F05a;
F7 := R(X) *.(elg/H) R(Y);

 end EqProof LRfn5;
                     // GG1 :: !! Thomin := All(f,f in hom(G,G1) == f in fn(elg.G, elg.G1) & A[x,y: elg.G, f(x *_G y) = f(x) *_G1 f(y)]);
! LRhom := R in hom(elg/N, elg/H);   by Thomin(elg/N, elg/H);  LRfn1_type & LRfn5;

! LRker := ker(R) = elg.(H/N);
 EqProof LRker;
F1 := ker(R);                       by Tker(R);              // ! Tker := ker = {x, x in elg.G, h(x) = e.G1};
F2 := {X: elg.(elg/N); R(X) = e.(elg/H)};  by LGNelg, LGHe;  // ! LGNelg := elg.(elg/N) = GN, // ! LGHe := e.(elg/H) = H;
F3 := {X: GN; R(X) = H};            by TRset;                // !! TRset := {z: R[x:A, G(x)], P(z)} = R[{x:A; P(G(x)}}, G(x)];
F4 := R[g_elg && R(g*N)=H, g*N];    by LRfn3;                // ! LRfn3 := A[g_elg, R(g*N) = g*H]; // GN := R[g_elg, g*N];
F5 := R[g_elg && g*H = H, g*N];     by LH7l@subgr;           // ! LH7l := A[g_elg, g*H = H == g in H];
F6 := R[g_elg && g in H, g*N];      by TInab7(L00);          // ! TInab7 := B <: t -> {x ; x in t} && x in B = {x; x in B};  // ! L00 := H <: elg; 
F7 := R[{g; g in H}, g*N];          by - LHNelg;             // ! LHNelg := elg.(H/N) = R[x:H, x*N];
F8 := elg.(H/N);                                             // g:H is internally represented as {g; g in H};  
 end EqProof LRker;
                                                             // GG1::hom:: !! Tism0a := im(h)==elg.G1 -> Gk ~ G1;
! LRim1 := im(R) = elg.(elg/H);     by  LGHelg;  LRim;       // ! LGHelg := elg.(elg/H) = GH; // ! LRim := im(R) = GH;
! LR2 := ker(R) in nsubgr.(elg/N);  is Lkern.R;              // hom :: ! Lkern := ker in nsubgr.G; 
! LR3 := im(R) = elg.(elg/H) -> (elg/N)/ker(R) ~ elg/H;      is Tism0a.R;  // GG1::hom:: !! Tism0a := im(h)==elg.G1 -> Gk ~ G1;
! LR4 := (elg/N)/ker(R) ~ elg/H;    is LR3(LRim1); by LRker; // ! LRker := ker(R) = elg.(H/N);
! Tism2 := (elg/N)/(elg.(H/N)) ~ elg/H; 

]; // HN1 :: [            // now we are in group::[...]     // !! TLastS := Last([x]) = x;   !! TLast_2 := Last([x,y]) = y;      
                                   
// !! Mathindr := A[mnd:nat, A[d,P] == A[d, mnd=0 -> P] & A[k:nat1, A[d, mnd < k -> P] -> A[d, mnd = k -> P]]];
// dcl[seqbij, set, SEQinj];
// !! Axseqbij := z in seqbij(A) == z in SEQinj & im(z) = A;
! L0 := seq1(elg) <: SEQ1;          is Tseq1t;     // !! Tseq1t := seq1(A) <: SEQ1;    // remove  !!! should be found automatically !!!
! L00 := seq1(elg) <: seq(elg);     is Tseq1t1;    // !! Tseq1t1 := seq1(t) <: seq(t); // remove !!!  see d.d 06.10.22;
! L05 := seq(elg) <: SEQ;           is Lseq0;      // !! Lseq0 := seq(t) <: SEQ;       // remove  !!! should be found automatically !!!
! L06 := [] in seq(elg);            is Axempseqt;  // !! Axempseqt := [] in seq(t);

dcl[Pseq, fn(seq(elg), elg)];      // !! Tseq1in1 := z in seq1(A) == z in seq(A) & l(z) ~= 0;    // z in seq1(elg) == z in seq(elg) & l(z) ~= 0;
!! AxPseq := A[z:seq(elg), Pseq(z) = if(l(z)=0, e, Pseq((z:seq1(elg))- ) * Last(z:seq1(elg)) )]; // ??? no termination check ???
                                         // !! Axfn := f in fn(A,B) == f in FN & dom(f) = A & im(f) <: B;        
! LPseqt := Pseq in fn(seq(elg), elg);   is typeaxiom; by Axfn; LPseq01 & LPseq02 & LPseq03;
! LPseq01 := Pseq in FN;                 // is TfnFN(LPseqt); // !! TfnFN := fn(A,B) <: FN;
! LPseq02 := dom(Pseq) = seq(elg); 
! LPseq03 := im(Pseq) <: elg;            
! LPseq0 := Pseq([]) = e;                byeq AxPseq, Red; // Tif1 // Red: if(l([])=0, e, Pseq([]-) * Last([]) ) = e;
//  EqProof LPseq0;
// F0 := l([]) = 0;
// F1 := Pseq([]);                              by AxPseq;
// F2 := if(l([])=0, e, Pseq([]-) * Last([]) ); by Tif1(Axempseq);           // !! Axempseq := l([]) = 0; // did not work: 6.18.22
// F3 := e;
//  end EqProof LPseq0;

! LPseq1 := A[z:seq1(elg), Pseq(z) = Pseq(z-) * Last(z)]; 
 EqProof LPseq1;
F0 := z in seq1(elg);                    assume;
F01 := ~(l(z) = 0);                      is Tseq1lnz(F0);   // !! Tseq1lnz := z in seq1(A) -> ~(l(z) = 0);
F1 := Pseq(z);                           by AxPseq;
F2 := if(l(z)=0, e, Pseq(z-) * Last(z)); by Tif2(F01);      // !! Tif2 := ~p -> if(p,a,b) = b;
F3 := Pseq(z-) * Last(z);
 end EqProof LPseq1;

! LPseq2 := A[z: seq(elg), x:elg,  Pseq(z^[x]) = Pseq(z) * x];  // use LPseq1, z^[x] in seq1((z^[x])- = z, Last(z^[x]) = x;
 EqProof LPseq2;
F0 := z in seq(elg);                     assume;
F01 := x in elg;                         assume;
F1 := Pseq(z^[x]);                       by LPseq1;
F2 := Pseq((z^[x])-) * Last(z^[x]);      by LPref1;        // !! LPref1 := (u0^[x])- = x;
F3 := Pseq(z) * Last(z^[x]);             by LLast1;        // !! LLast1 := Last(u0^[x]) = x;
F4 := Pseq(z) * x;
 end EqProof LPseq2;

dzz1 := {z,z1; Ax0 := z in seq(elg); Ax1 := z1 in seq(elg) };
// !! Mathindr := A[mnd:nat, A[d,P] == A[d, mnd=0 -> P] & A[k:nat1, A[d, mnd < k -> P] -> A[d, mnd = k -> P]]]; 

! LPseq3 := A[dzz1, Goal := Pseq(z^z1) = Pseq(z) * Pseq(z1)];
 Proof LPseq3;                           by Mathindr(l(z1)); Basis & Step; 
Basis := A[dzz1, l(z1)=0 -> Goal];       //  Pseq(z^z1) = Pseq(z) * Pseq(z1)];                     // Basis;
  EqProof Basis;
F0 := z in seq(elg);                     assume;     // such assume's are not necessary: REWORK !!! 2023.02.02 ???
F00 := l(z1)=0;                          assume; by Lseqlz;  // !! Lseqlz := l(u0)=0 == u0=[];
F01 := z1 = [];
F1 := Pseq(z^z1);                        by F01;
F2 := Pseq(z^[]);                        by Lconcemp;  // !! Lconcemp := A[z:SEQ, z^[] = z];
F3 := Pseq(z);                           by -Axre;     // Axre := A[x:elg, x * e = x]
F4 := Pseq(z) * e;                       by -LPseq0;
F5 := Pseq(z) * Pseq([]);                by - F01;
F6 :=  Pseq(z) * Pseq(z1);
  end EqProof Basis;

Step := A[k:nat1, A[dzz1, l(z1) < k -> Goal] -> A[dzz1, l(z1) = k -> Goal]]; 
  Proof Step;      
F0 := k in nat1;                            assume;
F01 := k ~= 0;                              is Lnat1nz(F0);  // !! Lnat1nz := x in nat1 -> x ~= 0; 
F02 := A[dzz1, l(z1)<k -> Goal];            assume;          // Goal := Pseq(z^z1) = Pseq(z) * Pseq(z1)
G0 := A[dzz1, l(z1)=k -> Goal];
   EqProof G0;
H00 := z in seq(elg);                       assume;     // such assume's are not necessary: REWORK !!! 2023.02.02 ???              
H0 := l(z1) = k;    assume;                 // !! Lseqbij1 := z in seqbij(A) & A ~= {] -> E[z1:seq(a),x:A, z = z1^[x] & z1 in seqbij(S--{x})] ;
H01 := l(z1) ~= 0;                          by H0; F01;              
H02 := z1 in seq1(elg);                     by Tseq1in1; z1 in seq(elg) & H01; // !! Tseq1in1 := z in seq1(A) == z in seq(A) & l(z) ~= 0;
H03 := Ex[z0:seq(elg),x:elg, H1a := z1 = z0^[x] ]; is Lseq1E(H02);             // !! Lseq1E := z in seq1(A) -> E[z1:seq(A),c:A, z = z1^[c]];
H04 := l(z0) < k;                           by -H0, H1a; is Lseq1ltlc;         // !! Lseq1ltlc  := A[z:SEQ, z1:SEQ1, l(z) < l(z^z1)];
H05 := Pseq(z^z0) = Pseq(z)*Pseq(z0);       is F02(z,z0);
H1 :=  Pseq(z^z1);                          by H1a;
H2 := Pseq(z^(z0^[x]));                     by -Lconcass;  // !! Lconcass := A[z,z1,z2: SEQ, (z^z1)^z2 = z^(z1^z2)];
H3 := Pseq((z^z0)^[x]);                     by LPseq2;     // ! LPseq2 := A[z: seq(elg), x:elg,  Pseq(z^[x]) = Pseq(z) * x];
H4 :=  Pseq(z^z0) * x;                      by H05;
H5 := (Pseq(z)*Pseq(z0)) * x;               by -AxAssoc;   // AxAssoc:= A[x,y,z: elg, x*(y*z) = (x*y)*z ]; 
H6 := Pseq(z)*(Pseq(z0)*x);                 by -LPseq2;
H7 := Pseq(z)*Pseq(z0^[x]);                 by -H1a;
H8 := Pseq(z)*Pseq(z1);                     // Goal := Pseq(z^z1) = Pseq(z) * Pseq(z1)
   end EqProof G0; 
  end Proof Step;
 end Proof LPseq3;

! LPseq4 := A[z,z1: seq(elg), x:elg, Pseq(z^[x]^z1) = Pseq(z) * x * Pseq(z1)];
 EqProof LPseq4;
F0 := z in seq(elg);                        assume;
F01 := z1 in seq(elg);                      assume;
F1 := Pseq(z^[x]^z1);                       by LPseq3; // ! LPseq3 := A[dzz1, Goal := Pseq(z^z1) = Pseq(z) * Pseq(z1)];
F2 := Pseq(z^[x])*Pseq(z1);                 by LPseq2; // ! LPseq2 := A[z: seq(elg), x:elg,  Pseq(z^[x]) = Pseq(z) * x];
F3 := Pseq(z)*x*Pseq(z1);
 end EqProof LPseq4;

// !! TInIn1 := Y0 <: Z0  & X0 <: Y0  -> X0 <: Z0;   // moved to root;

fcs := {C; AxC1 := C in FS(elg); AxC2 := A[x,y: C, x*y = y*x] };       // finite commutative set; {} in fcs
! Lfcs1 := fcs <: FS(elg);                  is TInab5a;                // !! TInab5a := {x; x in t; Q(x)} <: t;
! L26 := FS(elg) <: finset;                 is TFS0;                   // !! TFS0 := FS(A) <: finset
! Lfcs2 := fcs <: finset;                   is TInIn(Lfcs1 & L26);     // ! TInIn := X0 <: Y0 & Y0 <: Z0 -> X0 <: Z0;
// ! Lfcs2 := fcs <: finset;                is TInIn1(TFS0 & Lfcs1);   // !! TFS0 := FS(A) <: finset; //  -> X0 <: Z0;
// ! TInIn1 := Y0 <: Z0  & X0 <: Y0  -> X0 <: <: Z0; // Problems: fca <: FS(elg) & FS(A) <: finset -> fcs <: finset; so L26 above;

S_fcs := {S; Ax1 := S in fcs };
S_fcs :: [                              // !! AxFS := X in FS(A) == X <: A & X in finset;  // was L0; is TinIn(Ax1 & Lfcs1);
! L0 := S in FS(elg);                   is AxC1.S; by AxFS; L1 & L2;   // ! TinIn := x in X2 & X2 <: Y2 -> x in Y2;
! L1 := S <: elg;
! L2 := S in finset;
! L5 := seq(S) <: seq(elg);             is Tseqmon(L1);         // !! Tseqmon := A <: B -> seq(A) <: seq(B);
! L6 := S--X <: S;                      is TDIn;                // ! TDIn := X--Y <: X; 
! L8 := S--X in FS(elg);                is TFS3(L0);            // !! TFS3 := B in FS(A) -> B -- C in FS(A);
! L9 := A[x,y: S--X, x*y = y*x];        is TAIn2(L6 & AxC2.S);  // !! TAIn2 := A <: B & A[x,y:B, P(x,y)] -> A[x,y:A, P(x,y)];
! L7 := S--X in fcs;                    by Axab; L8 & L9;
]; // S_fcs :: [ 

// ! Lfcs3 := A[S_fcs, Goal1 := A[x:S, a:seq(S), Pseq(a)*x = x*Pseq(a)]];   // Goal1: if Goal, then error in bdef: double name; Correct ??? 6.25.22
Sxa := S_fcs && {x,a; x in S, a in seq(S) };
! Lfcs3 := A[Sxa, Pseq(a)*x = x*Pseq(a)];

 Proof Lfcs3;                           by Mathindr(l(a)); Basis & Step; 
! Basis := A[Sxa, l(a)=0 -> Pseq(a)*x = x*Pseq(a)];
  Proof Basis;
F0 := S in fcs;                         assume;
F01 := l(a)=0;                          assume;   by Lseqlz;  // !! Lseqlz := l(u0)=0 == u0=[]; ///  ! LPseq0 := Pseq([]) = e; 
F02 := a = [];
G0 := Pseq(a)*x = x*Pseq(a);            by F02; 
G1 := Pseq([])*x = x*Pseq([]);          by LPseq0;            // ! LPseq0 := Pseq([]) = e; 
G2 := e*x = x*e;                        byeq Tle, -Axre;      // ! Tle := A[a:elg, e*a = a]; // Axre := A[x:elg, x * e = x]
  end Proof Basis; 

! Step := A[k:nat1, A[Sxa, l(a) < k -> Pseq(a)*x = x*Pseq(a)] -> A[Sxa, l(a) = k -> Pseq(a)*x = x*Pseq(a)]];
  Proof Step;
F0 := k in nat1;                                      assume;
F01 := k ~= 0;                                        is Lnat1nz(F0);  // !! Lnat1nz := x in nat1 -> x ~= 0;
F02 := A[Sxa, l(a) < k -> Pseq(a)*x = x*Pseq(a)];     assume;
G0 :=  A[Sxa, l(a) = k -> Pseq(a)*x = x*Pseq(a)];     
   EqProof G0;
H0 := S in fcs;                         assume;
H00 := A[z:seq(S), l(z)~=0 -> E[z1:seq(S),c:S, z = z1^[c]]]; is LseqE; // !! LseqE := A[z: seq(A), l(z) ~= 0 -> E[z1:seq(A),c:A, z = z1^[c]];
H01 := A[x,y: S, x*y = y*x];            is AxC2.S;                     // AxC2 := A[x,y: C, x*y = y*x] };
H02 := l(a) = k;                        assume;
H03 := l(a) ~= 0;                       by H02; F01;  
H04 := Ex[a1:seq(S), x1:S, H04a := a = a1^[x1]];       is H00(H03);   
H05 := l(a1) < k;                       by -H02, H04a; is Lseq1ltlc;   // !! Lseq1ltlc  := A[z:SEQ, z1:SEQ1, l(z) < l(z^z1)];
H06 := Pseq(a) = Pseq(a1)*x1;           byeq H04a,LPseq2;              // ! LPseq2 := A[z: seq(elg), x:elg,  Pseq(z^[x]) = Pseq(z) * x];
H1 := Pseq(a)*x;                        by H06; 
H2 := Pseq(a1)*x1*x;                    by -AxAssoc;
H3 := Pseq(a1)*(x1*x);                  by H01;
H4 := Pseq(a1)*(x*x1);                  by AxAssoc;
H5 := (Pseq(a1)*x)*x1;                  by F02(S,x,a1)(H05);
H6 := (x*Pseq(a1))*x1;                  by -AxAssoc;
H7 := x*(Pseq(a1)*x1);                  by -H06;
H8 := x*Pseq(a);                    
   end EqProof G0;
  end Proof Step;
 end Proof Lfcs3;
  
// ab := {a,b; Ax2 := a in seqbij(S); Ax3 := b in seqbij(S) };

Sab := S_fcs && {a,b; Ax2 := a in seqbij(S); Ax3 := b in seqbij(S) };
Sab :: [                                // !! AxFS := X in FS(A) == X <: A & X in finset; 
// ! L0 := S in FS(elg);                   is TinIn(Ax1 & Lfcs1); by AxFS; L1 & L2;   // ! TinIn := x in X2 & X2 <: Y2 -> x in Y2;
// ! L1 := S <: elg;
// ! L2 := S in finset;
! L3 := #S = 0 -> a = [];               is Lseqbij3;        // !! Lseqbij3 := A[A:finset, z:seqbij(A), #A = 0 -> z = [] ];
! L4 := #S = 0 -> b = [];               is Lseqbij3;
// ! L5 := seq(S) <: seq(elg);             is Tseqmon(L1);     // !! Tseqmon := A <: B -> seq(A) <: seq(B);
! L6 := seqbij(S) <: seq(elg);          is Lseqbij4(L1);    // !! Lseqbij4 := A <: B -> seqbij(A) <: seq(B);       
// !! L7 := S--X in fcs; 
// !! L8 := Pseq(a)*Pseq(b)*x = Pseq(a)*x*Pseq(b);   
]; // Sab :: [

// ! TPseq := A[Sab, Pseq(a) = Pseq(b)];   by Mathindr(#(S@Sab)); LPseqB & LPseqS;  // Basis & Step; 
// !! LPseqB := A[Sab, #S=0 -> Pseq(a) = Pseq(b)];                        // Basis;
// !! LPseqS := A[k:nat1, A[Sab, #S < k -> P] -> A[Sab, #S = k -> P]];    // Step;

! TPseq := A[Sab, Pseq(a) = Pseq(b)];   // did not work:  by Mathindr(#(S@Sab)); Basis & Step; 
 Proof TPseq;                           by Mathindr(#(S@S_fcs)); Basis & Step;  //  by Mathindr(#(S@Sab)); Basis & Step; 
Basis := A[Sab, #S=0 -> Pseq(a) = Pseq(b)];
  Proof Basis;
F00 := a in seqbij(S);                  assume;              // such assume's are not necessary: REWORK !!! 2023.02.02 ???    
F0 := #S = 0;                           assume;     
F01 := a = [];                          is L3(F0);           // ! L3 := #S = 0 -> a = [];
F02 := b = [];                          is L4(F0);           // ! L4 := #S = 0 -> a = [];
G0 := Pseq(a) = Pseq(b);                byeq F01, -F02;
 end Proof Basis;
                          
Step := A[k:nat1, A[Sab, #S < k -> Pseq(a) = Pseq(b)] -> A[Sab, #S = k -> Pseq(a) = Pseq(b)]]; 
  Proof Step;      
F0 := k in nat1;                            assume;
F01 := k ~= 0;                              is Lnat1nz(F0);  // !! Lnat1nz := x in nat1 -> x ~= 0; 
F02 := A[Sab, #S < k -> Pseq(a) = Pseq(b)]; assume;
G0 := A[Sab, #S = k -> Pseq(a) = Pseq(b)];
   Proof G0;              // !! Lseqbij2 := z in seqbij(A) & x in A -> E[z1,z2: seq(A), z = z1^[x]^z2] & z1^z2 in seqbij(S--{x})];
F00 := a in seqbij(S);                      assume;              // such assume's are not necessary: REWORK !!! 2023.02.02 ???
H0 := #S = k;    assume;  // !! Lseqbij1 := z in seqbij(A) & A ~= {] -> E[z1:seq(a),x:A, z = z1^[x] & z1 in seqbij(S--{x})] ;
H01 := #S ~= 0;                             by H0; F01;              
H02 := S ~= {};                             by -Tcardnz; H01;                      // !! Tcardnz   := #A ~= 0 == A ~= {};
H1 := Ex[a1:seq(S),c:S, (H1a := a = a1^[c]) & (H1b := a1 in seqbij(S--{c}))];      is Lseqbij1(Ax2 & H02);
H03 := S--{c} in fcs;                       is L7;                                 // !! L7 := S -- X in fcs;   
H2 := Ex[b1:seq(S), b2:seq(S), (H2a := b = b1^[c]^b2) & (H2b := b1^b2 in seqbij(S--{c}))]; is Lseqbij2(Ax3 & c in S); // H03); //  c in S); 
H3 := #(S--{c}) < k;                        by -H0; is TcardD1a.S(c); //  finset :: !! TcardD1a := A[a: A, #(A--{a}) < #A];
H4 := Pseq(a) = Pseq(a1) * c;               byeq H1a, LPseq2;       // !! LPseq2 := A[z: seq(elg), x:elg,  Pseq(z^[x]) = Pseq(z) * x];
H5 := Pseq(b) = Pseq(b1)*c*Pseq(b2);        by H2a; is LPseq4;      // !! LPseq4 := A[z,z1: seq(elg), x:elg, Pseq(z^[x]^z1) = Pseq(z)*x*Pseq(z1)];
H6 := Pseq(b) = Pseq(b1)*Pseq(b2)*c;        by -AxAssoc, Lfcs3, AxAssoc; H5;   // !! Lfcs3 := A[S:fcs, x:S, a:seq(S), Pseq(a)*x = x*Pseq(a)];
H7 := Pseq(b) = Pseq(b1^b2)*c;              by LPseq3; H6;          // !! LPseq3 := A[z,z1: seq(elg), Pseq(z^z1) = Pseq(z) * Pseq(z1];   
H8 := Pseq(a1) = Pseq(b1^b2);               is F02(S--{c}, a1, b1^b2)(H3);
G1 := Pseq(a) = Pseq(b);                    byeq H4,H8,-H7;         //  AxAssoc:= A[x,y,z: elg, x*(y*z) = (x*y)*z ]; 

   end Proof G0;
  end Proof Step;
 end Proof TPseq;
                                             // LPseq5a: something wrong is in hnis; 7.03.22
! LPseq5 := A[S_fcs, LPseq5a := A[a,b:seqbij(S), Pseq(a) = Pseq(b)]];  is TAdd1AA(TPseq);  // !! TAdd1AA := A[d&&d1, P] == A[d,A[d1,P]];

! LPseq := A[S_fcs, E1[c:elg, A[a:seqbij(S), Pseq(a)=c]]];  // !! TfnAE1 := A[x:A, E1[y:B, Q(x,y)]] -> Exist1(f, f in fn(A,B) & A[x:A, Q(x,f(x))]);
 Proof LPseq;
F0 := S in fcs;                              assume;
F1 := seqbij(S) ~= {};                      is Lseqbij5;                      // !! Lseqbij5 := seqbij(A) ~= {}; // ! LPseq01 := Pseq in FN;
F4 := seqbij(S) <: dom(Pseq);               by LPseq02; is L6@Sab;         // ! LPseq02 := dom(Pseq) = seq(elg); // ! L6 := seqbij(S) <: seq(elg); 
F2 := Pseq in Fn(seqbij(S),elg);            by AxFn; LPseq01 & F4 & LPseq03;  // !! AxFn := f in Fn(A,B) == f in FN & A <: dom(f) & im(f) <: B;
F5 := A[a,b:seqbij(S), Pseq(a) = Pseq(b)];  is LPseq5a;                    // !! TFnAE1 := A ~= {} & g in Fn(A,B) & A[a,b:A, g(a)=g(b)] ->
G1 := E1[c:elg, A[a:seqbij(S), Pseq(a)=c]]; is TFnAE1(F1 & F2 & F5);       //               E1[c:B, A[a:A, g(a)=c]];      
 end Proof LPseq;

! Exist1x(Pset, (Ax1 := Pset in fn(fcs,elg)) & (AxPset := A[S_fcs, A[a:seqbij(S), Pseq(a)=Pset(S)]]) ); is TfnAE1(LPseq); // rename TfnAE1 !!!

]; // group :: [    

finset1 :: [   // ??? Aset :: [ ???  // finset := {A; Ax1 := fin(A)}; finset1 := finset && (Ax2 := A ~= {});
Sym := [afn(A), compA];            // symmetric group Sym(A); // compA := F[f,g:afn(A), f o g];       // comp: composition;
! TSym := Sym in group;  by Tingroup;  LcompA_type & LcompAass & Leinv; // ! LcompA_type := compA in fn(afn(A)#afn(A),afn(A)); 
]; // finset1 :: [  // ! LcompAass := A[f,g,h:afn(A), compA(f, compA(g,h)) = compA(compA(f,g),h)];
                

]  // end module 1_group.v