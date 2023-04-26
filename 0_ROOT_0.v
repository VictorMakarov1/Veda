module 0_root;          // Newveda_C4: 0_root:   04.21.23
use ;                   // The first module: no other modules are used;
[                       //  Lucida console bold 11 yoga: consolas regular 14 
dcl[:=]; dcl[bvar,bvar]; dcl[term]; dcl[formula]; // Problem #1: when creating a term, tp must be zel !!!
dcl[Proof]; dcl[EqProof]; dcl[Taut,bool,bool]; dcl[Staut,bool,bool];
dcl[assume,any,assume]; dcl[Instance,bool,bool]; dcl[Witness,any,bool];   // dcl[suppose,any,suppose]; 
dcl[by,bool,by]; dcl[byeq,bool,byeq]; dcl[byimp,bool,byimp]; dcl[add,bool,add];
 dcl[with,bool,with];  dcl[is,bool,is]; dcl[typeaxiom,bool]; // ,typeaxiom]; // dcl[from,bool,from];
dcl[variable,variable];  dcl[abterm,abterm]; dcl[finabterm,finabterm]; // dcl[tterm,tterm]; // dcl[cterm,cterm]; // dcl[abterm,abterm];
dcl[NotAxiom];  dcl[recdef];  dcl[postfix,bool]; dcl[var]; dcl[{];

var p,q,_q,q1,q2,q3,r,s,p1,p2,p3,p4,p5,p6,p7,p8,p9,P,P1,Q,Q1,Q2,R,R1, bool;
var Aa,a,a1,a2,a3,b,b1,c,x,x1,x2,x3,y,y1,y2,y3,u,v,z,z1,xx,yy,zz,F,G,G1,G2,H,K,f,f1,g,h, any;          
var A,A1,A2,A3,B,B1,B2,B3,C,C1,C2,D,S,S1,S2,T,T1,T2,t,t1,t2,w,w1,X,X0,X1,X2,X3,X4,Y,Y0,Y1,Y2,Z,Z0,Z1,Z2,Z3, set;                 
var d,d1,d2, abterm;  var zd, d; var QQ,RR,SS,TT, REL;
var i,j,k,k0,k1,m,m0,m1,i_int, int;  var n,n0,n00, nat;  var n_natm, natm; var n1, nat1;
fnsetbool := fn(set,bool);
var Pf, fnsetbool;

dx := {x; true}; dxy := {x,y; true}; 
              // 0. System names // "! Q;" means "Q must be proved later").
// sysname(var, is, Taut, by, with, axiom, theorem);    // {, ! 

               //  1. Propositional logical names

dcl[bool,set];
dcl[true, bool];
dcl[false, bool]; 
!! Axbool := bool = {true, false};          // {z1, ... , zk} is an embedded notation line 25
not1 := dcl[~, bool, bool];                 // negation         \~   \lnot
dcl[&, bool, bool, bool];                   // conjunction      \&
dcl[or, bool, bool, bool];                  // disjunction      \lor
dcl[->, bool, bool, bool];                  // implication      \to
dcl[<-, bool, bool, bool];                  // reverse implication p <- q == q -> p;      
dcl[==, bool, bool, bool];                  // equivalence      \equiv
dcl[~==, bool, bool, bool];                 // antiequivalence  \not\equiv
dcl[xor, bool, bool, bool];                 // exclusive or     \oplus 
dcl[xor3, bool, bool, bool,bool]; 
exc2 := dcl[!, bool, bool, bool];           // quasi resolvent
exc1 := dcl[!,bool,bool];                   // Conditionally true: not proved yet;
dcl[!!, bool, bool];                        // is an axiom 
dcl[A[,abterm,bool,bool];
dcl[E[,abterm,bool,bool];
dcl[Ex[,abterm,bool,bool];                  // Ex[d,P]: d-names are visible also in the enclosing scope; Ex[d,P] can occure only in proof scopes; 
dcl[E1[,abterm,bool,bool];
dcl[R[,abterm,any,set];  
dcl[U[,abterm,set,2];                       // 2: type(U[d,w]) = type(w);  
dcl[F[,abterm,any,any];                     // Lambda notation
dcl[S[,finabterm,any,any];                  // sum (Sigma), change dterm !
dcl[II[,finabterm,any,any];                 // product (Greek II)
dcl[II,set,set];                            // II(A) intersection of all sets in A
dcl[::,any,any,2];                          // type(d::M) = type(M);
dcl[&&,any,any,set];                        // was dcl[&&,any,any,any];  6.24.22
mnbool := dcl[-, bool, bool];               // reverse equation
dcl[class];  // check for repeating: dcl[class] was in the beginning !!!
dcl[set,set];                               // here set is a type, not a set
dcl[any,set];
dcl[{}, set ];                              // the empty set
dcl[<: ,set,set, bool];                     // set inclusion
dcl[<<, set, set, bool];                    // strict set inclusion
dcl[\/ ,set,set, set];                      // union of two sets
dcl[/\ ,set,set, set];
dpsetset := dcl[#,set,set,set];             // direct product
dcl[~, set,set,bool];                       // eqiupollent
dcl[in,any,set,bool];                       // belongs to
dcl[=,any,any,bool];
dcl[~=,any,any,bool];
dcl[=>, bool,bool,bool];
dcl[int, set];                              // the set of integers
dcl[nat, set];                              // the set of natural numbers
dcl[eps, bvar, bool, any];
dcl[arb, set, any]; 
dcl[nemp,set,bool];
dcl[most1,set,bool];                      // was M[X]
dcl[one,set,bool];                        // was E1[X]
dcl[the,set,any];                         // was T[X]
dcl[Exist, bvar, bool, bool];  
dcl[Exist1, bvar, bool, bool]; 
dcl[Existx, bvar, bool, bool];
dcl[Exist1x, bvar, bool, bool];  
dcl[All,bvar, bool, bool]; 
dcl[Sbbv]; 
dcl[Axab,bool];
dcl[Bred,bool];
dcl[Red];                                 // dcl[Red,bool]: error: z= #23434 Red(0 1 105)("f";2)
// dcl[AxAll,bool];
dcl[:, any, any, any];                   // type conversion

dcl[., any, any, any];
dcl[@, any,any, any];       //  m@M  method m in module M
dcl[fn, set,set, set];      // fn(A,B);  // ? fn(A1,...,Ak,B)
dcl[Fn, set,set, set];      // f in Fn(A,B) == f in FN & A <: dom(f) & im(f) <: B;
dcl[rel,set,set, set];      // rel(A,B);
anyd := dcl[^,abterm,any];
dcl[dom,REL,set];
dcl[im,REL,set];
restr := dcl[|,REL,set,REL];            //  Restriction R|A
dcl[\,FN,set,FN];            // Difference (for functions) f\A
dcl[\\, any, any, any];      // z \\ a=b: every instance a' of a in z replaced with b';
dcl[injective,FN,bool];
dcl[func,REL,bool];
!! Linv1_ptd := f in afn(A) -> inv(f) in afn(A);
!! Linv_ptd := f in bfn(A,B) -> inv(f) in bfn(B,A);
dcl[inv,REL,REL];
// dcl[pws,set,set];   // powerset
// !! Axpws := x in pws(A) == x <: A;
dcl[begin,any,any];
dcl[debug,any,any];
dcl[Associnve,bool];   // F1; by Associnve; F2;  means: F1 = F2, using associativity, inv, e; 

// Precedence: ~ * + = & or == ->                 
     
// Every tautology is an axiom, for example: true & p == p, p&(p->q) -> q;

! MP := (p -> q) & p -> q;                         is Taut;  // Modus Ponens
! MT := (p->q) & (~q) -> ~p;                       is Taut;  // Modus Tollens
! DS := (p or q) & (~p) -> q;                      is Taut;  // Disjunctive Syllogism
! MPT := (~p or q) & p -> q;                       is Taut;  // Modus Ponendo Tollens
! HS := (p->q) & (q->r) -> (p->r);                 is Taut;  // Hypothetical Syllogism
! HS1 := (p->q) & (q==r) -> (p->r);                is Taut;
! Tconjsym := p&q == q&p;                          is Taut;  // Taut21
! CP := (p->q) == (~q -> ~p);                      is Taut;  // ContraPosition
! TNimp := ~(p->q) == p & ~q;                      is Taut;
! Deqv := (p==q) == (p->q) & (q->p);               is Taut;  // Definition of equivalence
! Teqv1 := (p==q) == (p->q) & (~p -> ~q);          is Taut; 
! Teqvsym := (p==q) == (q==p);                     is Taut;  // was Taut15, Teqv2,Deqvr 
! Teqvneg := (p==q) == (~p == ~q);                 is Taut;
! Teqvneg1 := (~p == q) == (p == ~q);              is Taut;
! Teqvneg2 := (p == ~q) == (~p == q);              is Taut;
! Tneqv:= (p~==q) == ~(p == q);                    is Taut; 
! Tneqvr := ~(p == q) == (p~==q);                  is Taut; 
! TNor := ~(p or q) == (~p) & (~q);                is Taut;
! TNand := ~(p & q) == ~p or ~q;                   is Taut;
! TNandimp := ~(p & q) == (p -> ~q);               is Taut;
! TNN := ~(~p) == p;                               is Taut;  // DNE: double negation elimination 
! TautorN := p or ~p;                              is Taut;  // the law of excluded middle 
! Torimp := ((p or q) -> r) == (p->r) & (q->r);    is Taut;
! Torand := p or q == (~p -> q) & (~q -> p);       is Taut;
! Timpand := (p -> q) & (p -> r) == p -> (q & r);  is Taut;
! Tautor1 := ~p & ~q -> r == (p or q or r);        is Taut;
! Tautor2 := ~q & ~r -> p == (p or q or r);        is Taut;
! Tautor3 := ~r & ~p -> q == (p or q or r);        is Taut;
! Taut1 := (p or q) & (r or s) == (p&r or p&s or q&r or q&s);   is Taut;
! Taut2 := (p & ~q) or (q & ~p) == (p or q) & (p -> ~q);        is Taut;
! Taut3 := (p == q & r)->(p -> q);                 is Taut;
! Taut3a := (p == q & r) -> (p -> r);              is Taut; 
! Tidemor := p or p == p;                          is Taut;    // was Tautor4
! Dxor := p xor q == (p or q) & ~(p & q);          is Taut;    // Definition of xor
! Dxora := p xor q == (p or q) & (~p or ~q);       is Taut;
! Dxor3 := xor3(p,q,r) == (p & ~q & ~r) or (q & ~p & ~r) or (r & ~p & ~q);  is Taut;     // Definition of xor3
! Dxor3a := xor3(p,q,r) == (p or q or r) & (~p & ~q or ~p & ~r or ~q & ~r); is Taut;
! Dxor3b := xor3(p,q,r) == (p or q or r) & (~(p&q) & ~(p&r) & ~(q&r));             is Taut; 
! Dxor3c := xor3(p,q,r) == (p or q or r) & ((~p or ~q) & (~p or ~r) & (~q or ~r)); is Taut; 
// ! Dxor3d := (p xor q xor r) == &((p or q or r), ~p or ~q, ~p or ~r, ~q or ~r); by orand;
! Dxor3e := xor3(p,q,r) == (p or q or r) & (p -> ~q) & (q -> ~p) & (p -> ~r) & (r -> ~p) & (q -> ~r) & (r -> ~q) ;   is Taut;
! Dxor3f := xor3(p,q,r) == (p or q or r) & (p -> ~q & ~r) & (q -> ~p & ~r) & (r -> ~p & ~q);  is Taut;
! Dxor3g := xor3(p,q,r) == (p or q or r) & (p == ~q & ~r) & (q == ~p & ~r) & (r == ~p & ~q);  is Taut;
! Txor3N1 := xor3(p,q,r) -> (~p == (q or r));                  is Taut;
! Txor3N2a := xor3(p,q,r) -> (~q == (p or r));                 is Taut;
// ! ProofCase2 := (p1 or p2) & (p1 -> q) & (p2 -> q) -> q;  is Taut;  // Proof by cases
! Case2 := p1 or p2 -> (q == (p1 -> q) & (p2 -> q));        is Taut;
! Case3 := (p1 or p2 or p3) -> (q == (p1 -> q) & (p2 -> q) & (p3 -> q));                       is Taut;
! Case4 := (p1 or p2 or p3 or p4) -> (q == (p1 -> q) & (p2 -> q) & (p3 -> q) & (p4 -> q));     is Taut;

! Case6 := (p1 or p2 or p3 or p4 or p5 or p6 ) ->
           (q == (p1 -> q) & (p2 -> q) & (p3 -> q) & (p4 -> q) & (p5 -> q) & (p6 -> q));       is Taut;

// ! Case8 := (p1 or p2 or p3 or p4 or p5 or p6 or p7 or p8) ->
//            (q == (p1 -> q) & (p2 -> q) & (p3 -> q) & (p4 -> q) & (p5 -> q) & (p6 -> q) & (p7 -> q) & (p8 -> q));     is Taut;

// ! Case9 := or(p1,p2,p3,p4,p5,p6,p7,p8,p9) -> (q == &(p1->q,p2->q,p3->q,p4->q,p5->q,p6->q, p7->q,p8->q,p9->q)); is Taut;

! Absorb  := (p->q) == (p&q == p);                     is Taut;  // Absorption
! Absorb1  := (q->p) == (p&q == q);                    is Taut;  // Absorption
! Absorbor := (p->q) == (p or q == q);                 is Taut;
! Tor3or3 := (p1 or p2 or p3) & (q1 or q2 or q3) == 
       (p1&q1 or p1&q2 or p1&q3 or p2&q1 or p2&q2 or p2&q3 or p3&q1 or p3&q2 or p3&q3); is Taut;
! Taut8 := (p == q&r) -> (q -> (p==r));                is Taut; // Taut((p==q&r) -> (q->(p==r)))
! Taut9 := (p -> q) -> (p or q == q);                  is Taut;
! Taut9a := (p -> q) -> (q or p == q);                 is Taut;
! Taut10 := p or q&r == (p or q)&(p or r);             is Taut;
! Taut10a := q&r or ~q == ~q or r;                     is Taut;
! Taut10b := p & ~q or q == p or q;                    is Taut;
// ! Taut11 := (p or q -> r) == (p->r)&(q->r);            is Taut; // same as Torimp
! Taut12 := (p->q) & (r==q) -> (p->r);                 is Taut;
! Taut13 := (p->q) & (r==p) -> (r->q);                 is Taut;
! Taut14 := p & (~p) -> false;                         is Taut; 
! Taut14a := (~p) & p -> false;                        is Taut;
! Taut15 := (p->q&r) == (p->q)&(p->r);                 is Taut;
! Taut16 := ~p == (p==false);                          is Taut;
! Taut17 := (p==false) == ~p;                          is Taut;
! Taut18 := ~(p or q or r or s) == ~p & ~q & ~r & ~s;  is Taut;
! Taut19 := p & (p ~== q) -> ~q;                       is Taut;
! Taut20 := ~p & (p ~== q) -> q;                       is Taut; 

// Taut21 := p & q == q & p;                            is Taut;  // Tconjsym := p&q == q&p; 
! Taut22 := ((p or q) == p) == (q->p);                 is Taut;
// ! Taut23 := (p or q) & ~p -> q;                        is Taut; // same as ! DS := (p or q) & (~p) -> q; 
! Taut23a := p & (~p or q) -> q;                       is Taut;
! Taut24 := true or p;                                 is Taut;
! Taut25 := (p&q->r) == (p->(q->r));                   is Taut;
! Taut25a := (p&q->r) == (q->(p->r));                  is Taut;
! Taut26 := (true->p) == p;                            is Taut;
! Taut26a := (false->p) == true;                       is Taut;
! Taut26b := (p->true) == true;                        is Taut;
! Tidemconj := p & p == p;                             is Taut;
! Taut27 := (p->(q->r)) == (q->(p->r));                is Taut;
! Taut28 := p&(q&r) == q&(p&r);                        is Taut;
! Taut29 := (p == q&q1&q2&q3) -> (p->q);               is Taut;
! Taut29a := (p == q&q1&q2) -> (p->q);                 is Taut;
! Taut30 := (p==q)&q -> p;                             is Taut;
!! Tcaret1 := d ~= {} -> ^d in d;
!! Axrefl := x = x;
!! Axrefl1 := (x=x) == true;                         
!! Axsym := u=v == v=u;
!! Axeq2 := x=a & y=a -> x=y;
!! Axeq2a := a=x & a=y -> x=y;
!! Axeq3a := x=a1 & y=a2 & x=y -> a1=a2;
!! Axeqf := a=b -> G(a)=G(b);
!! Teq1 := (Pf(a) == a=b) == (Pf(b) == a=b);
!! Axeq3 := x=a1 & y=a2 & a1=a2 -> x=y;
!! Axreimp := Sb(Q,x,y) -> (x=y -> Q);
!! Axneq := z ~= z1 == ~(z = z1);                    by Teqvsym;  // ! Teqvsym := (p==q) == (q==p);  
!  Axneqr := ~(z = z1) == z ~= z1;
!  Tneq1a := x=y & x~=y -> false;                    by Axneq; is Taut14;
!  Tneq1 := x~=y & x=y -> false;                     by Axneq; is Taut14a;
!  TNneq := ~(u ~= v) == u = v;                      byeq Axneq, TNN;  // move to 1_quant
!  Tneqsym := x ~= y == y ~= x;                      byeq Axneq,Axsym,Axneqr;
!  Tneq2 := ~(x = x) == false;                       byeq Axrefl1, Taut(~true == false); by Axneqr;
!  Tneq2a := x ~= x == false; 
!! Axeqconj := a=b & Q -> Sb(Q,a,b);                   // was Axeq19
!! Axeqconj1 := a=b & Q -> Sb(Q,b,a);
// Sb(u,u1,u2) - the result of replacement, in the term u, any subterm u1 with the term u2;
dcl[Sb,any,any,any,1];            // #Sb = 0
dcl[===,any, any, bool];          // term equality (graphic equality)       
!! AxSbN := Sb(~Q, H, K) == ~(Sb(Q, H, K)); // (H = K)(~Q) = ~(H = K)(Q);
!! AxSbcnj := Sb(Q&Q1, H,K) == Sb(Q,H,K) & Sb(Q1,H,K); // (H = K)(Q1&Q2) = (H = K)(Q1) & (H = K)(Q2);
!! AxSbor := Sb(Q or Q1, H,K) == Sb(Q,H,K) or Sb(Q1,H,K);   // Sb(P or Q, R, R1) == Sb(P,R,R1) or Sb(Q,R,R1);
!! AxSbimp := Sb(Q->Q1, H,K) == Sb(Q,H,K) -> Sb(Q1,H,K); // Sb(P->Q, R, R1) == Sb(P,R,R1) -> Sb(Q,R,R1);
!! AxSbeqv := Sb(Q==Q1, H,K) == (Sb(Q,H,K) == Sb(Q1,H,K)); // Sb(P==Q, R, R1) == (Sb(P,R,R1) == Sb(Q,R,R1));
!! AxSbeq := Sb(G=G1, H,K) == (Sb(G,H,K) = Sb(G1,H,K)); // Sb(P=Q, R, R1) == Sb(P,R,R1) = Sb(Q,R,R1);
!! AxSb1 := Sb(G,G,H) = H;
!! AxSb1eqv := Sb(Q,Q,Q1) == Q1;

dcl[Rep,abterm,any,any,2];          // #abterm = 1  was zd below;
!! AxRepN := Rep(d,~P,z) == ~Rep(d,P,z);
!! AxRepimp := Rep(d,P->Q,z) == (Rep(d,P,z) -> Rep(d,Q,z));
!! AxRepfree := free(d, P) -> (Rep(d,P,z) == P);

dcl[free, any, variable, bool]; // free(G,x): term G is free from variable x;
!! TfreeN := free(Q,xx) == free(~Q,xx);
!! TfreeSb := free(G,xx) -> (Sb(G, xx, H) === G);    // === TfreeSb(G: term, x: variable) 
!! Tfreesb1 := free(K, xx) -> free(Sb(G,xx,K),xx);  // Tfreesb1(K,x,G)
!! Tsb1 := Sb(G, K, K) === G; 

!! TExistfalse := Exist(x, false) == false;       //   is Sb(AxExist, P, false);
!! TExisttrue := Exist(x, true) == true;          //   is Sb(AxExist, P, true);
// ! TExisteqv := All(x,Q == Q1) -> Exist(x,Q) == Exist(x,Q1);    // see HB17b 

// !! AxAll := All(xx, Q) == Sb(Q, xx, eps(xx,~Q));  // P{x := eps(x, ~P)};
// ThAll := All(x,Q) -> Q;                       //   is Theps ! AxAll;
!! US := All(x,Q(x)) -> Q(K);                    //   is Sb(ThAll, xx, K);  // import xx ??? 
ExP := Exist(x,P(x));
!! AxExist := ExP(a) -> ExP;                     // ExP(a) denotes P(a); // not used; Witness is used instead;
// !! UG := P => All(xx, P);                     // Universal Generalization,see proof in logicp   ! UG := P => 
!! HB1 := All(x,Q(x)) -> Exist(x,Q(x));          // is ThExist ! ThAll; // is HS(ThExist & ThAll);
!! TNAll := ~(All(x, Q(x))) == Exist(x, ~(Q(x)));  //  HB2 byeq AxAll, -AxSbN, -AxExist; was xx
!! HExistN := ~(Exist(x, ~(Q(x)))) == All(x, Q(x));     //  HB2p byeq -HB2, Taut(~(~p) == p); // var p: bool;
!! TNAllN := ~ (All(x, ~(Q(x)))) == Exist(x, Q(x));      //  HB3  byeq HB2, Taut(~(~p) == p);
!! NExist := ~(Exist(x, Q(x))) == All(x, ~(Q(x)) );      //  HB3p byeq -HB3, Taut(~(~p) == p);
!! TAllfalse := All(x, false) == false;           //  byeq -HB2p, ~false == true, TExisttrue, ~true == false;
!! TAlltrue := All(x, true) == true;              //  byeq -HB2p, ~true == false, TExistfalse, ~false == true;
!! HB4 :=  All(x, Q -> P(x)) == (Q -> All(x, P(x)));
!! HB4a := All(x, Q) == Q;         // is HB4(P,true) ! Taut(p->true == p);
!! HB5 :=  All(x, P or Q(x)) == P or All(x, Q(x));
!! HB5a := All(x, P(x) or Q) == All(x, P(x)) or Q;
!! HB6 :=  All(x, P & Q(x)) == P & All(x, Q(x));
!! HB6a := All(x, P(x) & Q) == All(x, P(x)) & Q;
!! TAllconj :=  All(x, P(x) & Q(x)) == All(x, P(x)) & All(x, Q(x));
!! HB7a := All(x, P(x) & Q(x)) -> All(x, P(x));
!! HB7b := All(x, P(x) & Q(x)) -> All(x, Q(x));
!! HB7c := All(x, P(x) & Q(x) & R(x)) == All(x, P(x)) & All(x, Q(x)) & All(x, R(x));
!! HB8 :=  Exist(x, Q or P(x)) == Q or Exist(x, P(x));
!! HB8a := Exist(x, P(x) or Q) == Exist(x, P(x)) or Q;
!! HB9 :=  Exist(x, P(x) or Q(x)) == Exist(x, P(x)) or Exist(x, Q(x));
!! HB9a := Exist(x, P(x) & Q(x)) -> Exist(x, P(x)) & Exist(x, Q(x));
!! HB10 := Exist(x, Q & P(x)) == Q & Exist(x, P(x));
!! HB10a := Exist(x, P(x) & Q) == Exist(x, P(x)) & Q;
!! HB10b := Exist(u, P(u) & Q) == Q & Exist(u, P(u));
!! HB11 := All(x, P(x) -> Q(x)) -> (All(x, P(x)) -> All(x, Q(x)));
!! HB12 := All(x, P(x) -> Q(x)) -> (Exist(x, P(x)) -> Exist(x, Q(x)));
!! HB13 := All(x, All(y, P(x,y))) == All(y, All(x, P(x,y)));                      // TAllAll
!! HB13p := Exist(x, Exist(y, P(x,y))) == Exist(y, Exist(x, P(x,y)));                     // TExistExist
// !! HB13p1 := Exist(x1,x2, P) == Exist(x1,Exist(x2,P));               // Def Axiom, TE2a TE2EE
// !! AxA2AA := All(x1,x2, P) == All(x1,All(x2, P));
// ! HB13p2 := Exist(x, Exist(x1,x2, P)) == Exist(x1,x2, Exist(x, P));
!! HB13p3 := Exist(x, Exist(y, Exist(z, P))) == Exist(y, Exist(z, Exist(x, P)));
!! HB13A3_1_2 := All(x, All(y, All(z, P))) == All(z, All(x, All(y, P)));
!! HB13A2_3_1 := All(x, All(y, All(z, P))) == All(y, All(z, All(x, P)));
// ! HBE12_3_3_12 := Exist(x,y, Exist(z, Q) ) == Exist(z, Exist(x,y,Q)); 
// !! HB14 := All(x, All(y, P(x,y) )) -> All(x, P(x,x) );               // goodimp(HB14) = true ???
// !! HB14p := Exist(x, Exist(y, P(x,y) )) -> Exist(x, P(x,x) );
!! HB15a := All(x, All(y, P(x) & Q(y) )) == All(x, P(x)) & All(y, Q(y)); 
!! HB15b := Exist(x, Exist(y, P(x) & Q(y) )) == Exist(x, P(x) ) & Exist(y, Q(y) );
// !! HB15b1 := free(P, y) & free(Q, x) -> Exist(x,P(x)) & Exist(y,Q(y)) == Exist(x,y, P(x) & Q(y));
!! HB15c := All(x, Exist(y, P(x) & Q(y) )) == All(x, P(x)) & Exist(y, Q(y) ); 
!! HB15d := Exist(x, All(y, P(x) & Q(y)) ) == Exist(x, P(x)) & All(y, Q(y) ); 
!! HB15e := All(x, All(y, P(x) or Q(y)) ) == All(x, P(x) ) or All(y, Q(y) ); 
!! HB15f := Exist(x, Exist(y, P(x) or Q(y) )) == Exist(x, P(x)) or Exist(y, Q(y) );
!! HB15g := All(x, Exist(y, P(x) or Q(y) )) == All(x, P(x) ) or Exist(y, Q(y) ); 
!! HB15h := Exist(x, All(y, P(x) or Q(y) )) == Exist(x, P(x) ) or All(y, Q(y) ); 
// ! HB15g  := All(x,All(y, P(x) -> Q(y) == Exist(x,Q(x)) -> All(y,P(y)); // use HB4,(HB5)
// ! HB15h  := All(x,All(y, P(y) -> Q(x) == Exist(x,P(x)) -> All(y,Q(y)); 
!! HB16a := All(x, P(x) -> Q) == (Exist(x, P(x)) -> Q);
!! HB16b := Exist(x, P(x) -> Q) == (All(x, P(x)) -> Q);      // TfreeExistimp
!! HB17a := All(x, P(x) == Q(x)) -> ( All(x, P(x) ) == All(x, Q(x) ) ); 
!! HB17b := All(x, P(x) == Q(x)) -> (Exist(x, P(x)) == Exist(x, Q(x))); 
!! HB18 := Exist(x, All(y, P(x,y) )) -> All(y, Exist(x, P(x,y) ));
!! HB19 := All(x, Q(x)->R(x)) -> (All(x,P(x)->Q(x)) -> All(x, P(x)->R(x)));
!! HB20 := All(x, Q(x)->R(x)) -> (Exist(x, P(x) & Q(x) ) -> Exist(x, P(x) & R(x) ));
!! TAlleqv := All(a, All(b, All(x, x=a == x=b) == a=b));   // Prove ! 
!! TAlleqv1 := All(x, x=a == x=b) == a=b;
//-----------------  sets ----------------------------------
!! AxextA := X = Y == All(x, x in X == x in Y); 

// ! TAlleq := All(xx, xx = K -> P) == Sb(P,xx,K); 
// ! TAlleq := (M:=All(x, x = a -> Q)) == Sb(Q, M.x, a); 
!! TAlleq := All(x, x=K -> Q(x)) == Q(K);
// !! TExisteq := Exist(xx, xx=K & Q) == Sb(Q,xx,K);
!! TExisteq := Exist(x, x=K & Q(x)) == Q(K);
! TinExist := a in X == Exist(x, x=a & x in X);    by TExisteq; is Taut;   // a in X == a in X;
// dif3(a,b,c) := a ~= b & a ~= c & b ~= c;           // move to 1_quant

     //---------------------------------------- Inclusion ---------------------------------------
!! AxIn := X2 <: Y2 == All(x, x in X2 -> x in Y2);    by Teqvsym; 
! AxIn1 := All(x, x in X2 -> x in Y2) == X2 <: Y2;
! TInrefl := X <: X;                              is Staut; // by AxIn; is Taut; // reflexivity 8,9,10
! Axext := X = Y == X <: Y & Y <: X;              is Staut;
! AxextAB := A=B == A <: B & B <: A;              is Staut;
! Axext0 := X <: Y & Y <: X == X = Y;             is Staut; //   by Teqvsym; Axext;
! Axext01 := X <: Y & Y <: X -> X = Y;            is Staut; by Taut((p&q -> r) == (p & (~r) -> (~q)));
! Axext02 := X <: Y & ~(X=Y) -> ~(Y <: X);        by Axneqr;
! Axext03 := X <: Y & X ~= Y -> ~(Y <: X); 
! Axext1 := X=Y -> X<:Y;                          is Staut; //   by Axext; is Taut;  // Staut: (p==q)->(p->q);
! Axext2 := X=Y -> Y<:X;                          is Staut; //   by Axext; is Taut;  // Staut: (p==q)->(q->p);
! TInIn := X0 <: Y0 & Y0 <: Z0 -> X0 <: Z0;       is Staut; //  transitivity: Staut: (p->q & q->r) -> p->r;
! TInIn1 := Y0 <: Z0  & X0 <: Y0  -> X0 <: Z0;    is Staut;
! TNIn := ~(X2 <: Y2) == Exist(x, x in X2 & ~(x in Y2));  byeq AxIn, TNAll, TNimp;  // used in Proof(TsbgU);
                                                  // !! TNAll := ~(All(x, Q(x))) == Exist(x, ~(Q(x)));
! TinIn := x2 in X2 & X2 <: Y2 -> x2 in Y2;
 Proof TinIn;
F0 := x2 in X2;                                   assume;
F01 := X2 <: Y2;                                  assume; by AxIn;
F02 := All(z, z in X2 -> z in Y2);                // s = [(z,x)]; // bvar z must be var;
F1 := x2 in Y2;                                   is F02(F0); // x in Y2 is s.instance(z in Y2);
 end Proof TinIn;

!! TInin := X <: Y & x in X -> x in Y;
!! TabIn := {x:X; Q(x)} <: X;

! TempIn := {} <: X;                              is Staut; //by AxIn, Tinemp; is Taut; false -> p;

   //----------------------------------nin-------------------
dcl[nin, any, set, bool]; 
!! Axnin := x nin X == ~(x in X);                 by Teqvsym;
!  Axninr := ~(x in X) == x nin X;
!  Tnin1 := x nin X & x in X -> false;            by Axnin; is Taut(~p & p -> false);
// !  Tnin1a := x in X & x nin X -> false;           by Axnin; is Taut(p & ~p -> false); // same as Stautin
!  Tnin2 := x in X or x nin X;                    by Axnin; is Taut(p or ~p);
!  TNnin := ~(x nin X) == x in X;                 byeq Axnin, TNN; // is Teqvneg ! Axnin; 
!  Stautin := (x in X) & (x nin X) -> false;      by Axnin;  is Taut(p & ~p -> false); // is Instance(Taut14);
//   Stautin1 := (x in X) & ~(x in X) -> false;   is Instance(Taut14);

! TninA01 := All(x, x in X -> x ~= y) == y nin X;  
 EqProof TninA01;                                     // EqProof(-TninA0;
F1 := All(x, x in X -> x ~= y);                   by CP;               // ContraPosition: p->q == ~q -> ~p;
// F1a := All(x, ~(x ~= y) -> ~(x in X) );        by Axneq, Axninr;
F1a := All(x, ~(x ~= y) -> ~(x in X) );           by TNneq;            //  replace byr Ax
F1b := All(x, (x = y) -> ~(x in X) );             by Axninr;
F2 := All(x, x=y -> x nin X);                     by TAlleq;           // ! TAlleq := All(x, x=K -> Q(x)) == Q(K);
F3 := y nin X;
 end EqProof TninA01;

! TninA0 := y nin X == All(x, x in X -> x ~= y);  by Teqvsym; TninA01;  // p==q == q==p;

! Tinnin := x in X & y nin X -> x ~= y;            
 Proof Tinnin;
F0 := x in X;                                     assume;
F01 := y nin X;                                   assume;
F02 := ~( x~= y);                                 assume; by TNneq;
F1 := x = y;
F2 := x nin X;                                    by F1; F01;
F3 := false;                                      is Stautin(F0 & F2);   //  !  Stautin := (x in X) & (x nin X) -> false; // F0 ! F2;
 end Proof Tinnin;

!! Axdconj := z in (d&&P) == z in d & Rep(d,P,z);     // ???(d&&P)??? wrong precedence for &&;
!! LdconjIn := (d&&P) <: d;                   // && precedence ???
!! Ldconjfs := d in finset -> (d&&P) in finset;
!! Ldconjimp :=  z in d -> z in (d && P) == Rep(d,P,z);
!! LdconjU := (d&&P) \/ (d&&Q) = (d&&(P or Q));                    // change precedence of && !!!
!! LdconjA := A[d,P] == (d&&P) = d; 
!! LdconjNI := (d&&P) NI (d&&Q) == A[d, ~(P & Q)];
 
// -------------- 1_coll.v
 
// dcl[qq,any,bool];
// dcl[AxAll,bool];
!! Axempt := {} in set;
!! Axemp := ~(u in {});                     by Axninr;           // Axninr := ~(x in X) == x nin X;     
! Tninemp := u nin {};                                           // Taut17 := (p==false) == ~p;
! Tinemp := u in {} == false;              by Taut17; Axemp;     // TempAll: X={}; by AxextA; All(x,x in X == x in {}); by Tinemp; 
! TempAll := All(X, X = {} == All(x, x nin X));    byeq AxextA,Tinemp,Taut17,Axninr;  // All(x,x in X == false); by Taut17; All(x,~(x in X));  
!!  AxAll := All(x,P(x)) -> P(a);          // var Pf, fn(set,bool);  
! Tx1a := All(x, x nin X) -> x nin X;      is AxAll;             //  used only to prove Tempin
! Tempnin := X = {} -> x nin X;            by TempAll; Tx1a;
! Tinnemp := x in X -> X ~= {};            by CP,TNneq,Axninr; Tempnin;     // Later: TNneq & Axninr
! Tx3 := All(X, X = {} == All(x, ~(x in X)));      by Axninr; TempAll;
! Tx2 := All(X, X = {} == ~(Exist(x, x in X)));    by NExist; Tx3;
! TinnempE := All(X, X ~= {} == Exist(x, x in X)); by Teqvneg,TNneq; Tx2;      // HB3p,Axninr; TempAll; 
! Tabin := All(X, {x; x in X} = X);        by AxextA, Axab; is Taut;           // !! AxextA := X = Y == All(x, x in X == x in Y); 
!! TabI := {x:A; x in B} = A/\B; 
!! Axcoll1 := All(x, All(a, x in {a} == x = a));                               // was Axcoll1{a} = {x ; x=a};       
Tcoll1 := {x ; x=a} = {a};                 by AxextA,Axcoll1,Axab; is Taut; 
// TSab := {a} = {x ; x=a};                by AxextA,Axcoll1,Axab; is Taut; 
! TinS := a in {a};                        by Axcoll1; is Axrefl;              // TNnin := ~(x nin X) == x in X;
! TninS := x1 nin {a1} == x1 ~= a1;        by Teqvneg,TNnin,TNneq; is Axcoll1; // Teqvneg := (p==q) == (~p == ~q);  Later: TNnin & TNneq
! TninS1 := a nin {a} == false;            byeq TninS, Tneq2a;                 // Tneq2a := x ~= x == false;
! TSneqemp := {a} ~= {};                   is Tinnemp(TinS);
! TSeq := A={a} == All(x, x in A == x=a);  byeq AxextA, Axcoll1;               // ! AxextA := X = Y == All(x, x in X == x in Y); 
! TSeq; by Teqvneg,Axneqr,TNAll,Tneqvr;
! TSneq := A ~= {a} == Exist(x, x in A ~== x=a); // !! TSneq := A ~= {a} == Exist(x, x in A ~== x=a); // 374
// ! TSeq1 is inclP.v
// TSeq2 := All(a,All(b, {a} = {b} == a = b));                  ///

! TSeq2a := {a} = {b} == a = b;                                  // 375
 Proof TSeq2a;                             by Deqv; L1 & L2;
L1 := {a} = {b} -> a = b;
  Proof L1;                                // hnby: wrong by-element = #1749by(!1Axcoll1#1672;!1Axcoll1#1672)
F0 := {a} = {b};                           assume; by AxextA;
F1 := All(x, x in {a} == x in {b});        by Axcoll1,Axcoll1;
F2 := All(x, x=a == x=b);                  by TAlleqv1;
F3 := a=b;                                 // Sb(Q,x,y) & x=y -> Q; from Q & x=y -> Sb(Q,x,y); (subst ~Q instead of Q);
  end Proof L1;
L2 := a=b -> {a} = {b};                    // byimp Axreimp;  // L2 is s.instance(x=y -> Q): x=a,y=b, Q= {a}={b};
  Proof L2; 
F0 :=  a=b;                                assume;
G0 := {a} = {b};                           byeq F0;      // s.Sb(Q,x,y) = Sb({a]={b],a,b) = {b}={b}; 
  end Proof L2;
 end Proof TSeq2a;

!! TSin := B = {X} & a in B -> a=X;

! TSin2 := a in A & A ~= {a} -> Exist(b, b in A & b ~= a);
 Proof TSin2;
F0 := a in A;                                   assume;
F01 := A ~= {a};                                assume; by TSneq;
F02 := Existx(c, _F02a := c in A ~== c=a);     // make scope "Proof", not zel !!!
F03 := ~(Exist(b, b in A & b ~= a));            assume; by NExist,TNandimp,TNneq;
F04 := All(x, x in A -> x = a);                 // #1559
F1 := c in A or ~(c in A);                      is Taut(p or ~p);
Goal := false;                                  by Case2(F1); L1 & L2;
L1 := c in A -> false;                          // Case2 := p1 or p2 -> (_q == (p1 -> _q) & (p2 -> _q));        Taut;
  Proof L1;
K0 := c in A;                                   assume; with _F02a;   // Taut19: c in A & (c in A ~= c=a);  
K1 := ~(c = a);
K2 := c = a;                                    is F04(K0);
K3 := false;                                    is K1 ! K2;           // Taut14a
  end Proof L1;
L2 := ~(c in A) -> false;
  Proof L2;
K5 := ~(c in A);                                assume; // with _F02a;   // ! Taut20 := ~p & (p ~== q) -> q;
K6 := c = a;                                    is Taut20(K5 & _F02a);   by Axsym;  // !! Axsym := u=v == v=u;
K7 := a = c;
K8 := c in A;                                   is K7(F0);    // F0 := a in A;
K9 := false;                                    is K8 ! K5;   // Taut14 := p & (~p) -> false;
  end Proof L2;
 end Proof TSin2;

!! TSin2E := a in A & A ~= {a} -> E[b:A, b ~= a];

! TSin3 := A = {a} == a in A & All(x, x in A -> x = a);        /// by Teqvneg,Axneqr ///
 EqProof TSin3;                                           // i= 22
F1 := A = {a};                                            by TSeq;
F2 := All(x, x in A == x=a);                              by Deqv;
F3 := All(x, (x in A -> x = a) & (x=a -> x in A) );       by TAllconj;
F4 := All(x, x in A -> x = a) & All(x, x=a -> x in A);    by TAlleq;
F5 := All(x, x in A -> x = a) & a in A;                   by Tconjsym;
F6 := a in A & All(x, x in A -> x = a);
 end EqProof TSin3;

!! TSin3A := A = {a} == a in A & A[x:A, x = a];           // Prove it first, then TSin3a is a simple corollary;

! TSin3a := A ~= {a} == a nin A or Exist(x, x in A & x ~= a);  /// 
 EqProof TSin3a;
F1 := A ~= {a};                                            by Axneq; //  Axneq := z ~= z1 == ~(z = z1);
F2 := ~(A = {a});                                          by TSin3;
F3 := ~(a in A & All(x, x in A -> x = a));                 by TNand; // ! TNand := ~(p & q) == ~p or ~q; 
F4 := ~(a in A) or ~(All(x, x in A -> x = a));             by Axninr; // Axninr := ~(x in X) == x nin X;
F5 := a nin A or ~(All(x, x in A -> x = a));               by TNAll;  // TNAll := ~(All(x, Q(x))) == Exist(x, ~(Q(x)));
F6 := a nin A or Exist(x, ~(x in A -> x = a));             by TNimp;  // TNimp := ~(p->q) == p & ~q;
F7 := a nin A or Exist(x, x in A & ~(x=a));                by -Axneq;
F8 := a nin A or Exist(x, x in A & x~=a); 
 end EqProof TSin3a;

// TSin4 := All(x,All(y,All(A, x in A & y in A & x ~= y) -> A ~= {x}));     ///
! TSin4 := x in A & y in A & x ~= y -> A ~= {x};
 Proof TSin4;
F0 := x in A;                                             assume;
F01 := y in A;                                            assume;
F02 := x ~= y;                                            assume;
F03 := A = {x};                                           assume; with F01;
F1 := y in {x};                                           by Axcoll1;        // !! Axcoll1 := All(x, All(a, x in {a} == x = a));
F2 := y = x;
F3 := false;                                              is F2 ! F02;
 end Proof TSin4;

// !! Axcoll2 := All(x, All(a,All(b, x in {a,b} == x = a or x = b)));
// Tcoll2ab := {a,b} = {x; x=a or x=b};                            by AxextA, Axcoll2, Axab; is Taut;

!! Axcoll2 := x1 in {a1,b1} == x1=a1 or x1=b1;                   // was Tcoll2in
! Tcoll2In := {a,b} <: Z == a in Z & b in Z;        byeq AxIn,Axcoll2,Torimp,TAllconj,TAlleq;
! Tcoll2 := {a,b} = {x; x=a or x=b};                by AxextA,Axcoll2,Axab; is Taut;
// Tcoll2ab1 := {a,a} = {a};                        byeq Axcoll2, Tautor4, Tcoll1; // Tcoll1 := {x ; x=a} = {a}; 
! Tcoll2S := All(x, {x,x} = {x});                   byeq Tcoll2, Tidemor, Tcoll1;  // byeq AxextA, Axcoll2, Axcoll1; is Taut(p or p == p);
// Tcoll2nin := x nin {a,b} == x ~= a & x ~= b;     byeq Axnin, 
! Tcoll2nin := All(y,All(a,All(b, y nin {a,b} == y ~= a & y ~= b))); byeq Axnin,Axcoll2,TNor,Axneqr,Axneqr;    // is  Axcoll2 ! Teqvneg ! TNor;
// Tcoll2Seq := a=b == {a,b} = {a};                            ///
 
! Tcoll2Seq := {a1,b1}={a1} == a1=b1; 
 EqProof Tcoll2Seq;
F1 := {a1,b1} = {a1};                               by AxextA;
F2 := All(x, x in {a1,b1} == x in {a1});            by Axcoll2, Axcoll1;
F3 := All(x, x=a1 or x=b1 == x=a1);                 by Taut22;
F4 := All(x, x=b1 -> x=a1);                         by TAlleq;
F5 := b1=a1;                                        by Axsym;                   
F6 := a1=b1;                                           // line 500, main.his: 500  s= F6 := a1=b1;
 end EqProof Tcoll2Seq;
   
// Tcoll2neq := x in {a,b} & x ~= a -> x=b;                    ///
! Tcoll2neq := All(x,All(a,All(b, x in {a,b} & x ~= a -> x=b)));
 Proof Tcoll2neq;
assume(x); assume(a); assume(b);                    // here goal is x in {a,b} & x ~= a -> x=b
F0 := x in {a,b};                                   assume; by Axcoll2;  // !! Axcoll2 := x1 in {a1,b1} == x1=a1 or x1=b1;
F01 := x=a or x=b;
F02 := x ~= a;                                      assume; by Axneq;    // Axneq := z ~= z1 == ~(z = z1);  // with F01;
F03 := ~(x=a);                                      
Goal := x=b;                                        is DS(F01 & F03);    // ! DS := (p or q) & (~p) -> q; 
 end Proof Tcoll2neq;

! Tcoll2in1 := a in {a,b};
 Proof Tcoll2in1;                                   by Axcoll2;
F1 := a=a or a=b;                                   by Axrefl1;
F2 := true or a=b;                                  is Taut(true or p);   // Taut24;
 end Proof Tcoll2in1;

! Tcoll2in2 := b in {a,b};                          by Axcoll2,Axrefl1; is Taut;
// ! Tcoll2a := {a,b} <: X == a in X & b in X;                // <: is not yet defined
! Tcoll2a := {a,b} = {a,c} == b=c;                             ///
! Tcoll2E := Exist(x, x in {a,b} & Q(x)) == Q(a) or Q(b);        ///
! Tcoll3E := Exist(x, x in {a,b,c} & Q(x)) == Q(a) or Q(b) or Q(c); ///

// !! Axcoll4 := All(x,All(a,All(b,All(c,All(d, x in {a,b,c,d} == x=a or x=b or x=c or x=d)))));
!! Axcoll4a := x in {a,b,c,d} == x=a or x=b or x=c or x=d;
// Tcoll4nin := All(x,All(a,All(b,All(c,All(d, x nin {a,b,c,d} == x~=a & x~=b & x~=c & x~=d))))); 
! Tcoll4nin0 := x nin {a,b,c,d} == x~=a & x~=b & x~=c & x~=d; 
             byeq Axnin, Axcoll4a,Taut18, Axneqr, Axneqr, Axneqr, Axneqr; // is Taut;
// Tcoll4nin1 := All(A, All(a, All(b, All(c, All(d, All(x,
//              A in set & x in A -> x=a or x=b or x=c or x=d or x nin {a,b,c,d})))))); by Tcoll4nin0; is Taut;

!! Axarb     := X ~= {} == arb(X) in X;                 by TinnempE;
!  TExistarb := Exist(x, x in X) == arb(X) in X;       
!  Tarbin := x in X -> arb(X) in X;                     by -Axarb;  is Tinnemp; // ! Tinnemp := x in X -> X ~= {};  

! TarbS := arb({z}) = z;
 Proof TarbS;
F0 := {z} ~= {};                                        is TSneqemp; by Axarb;  // TSneqemp := {a} ~= {}; 
F1 := arb({z}) in {z};                                  by Axcoll1; TarbS;      // !! Axcoll1 := All(x, All(a, x in {a} == x = a));
// F2 := arb({z}) = z;                                  // error: no merging;
 end Proof TarbS;

! TninIn := x nin Y & X <: Y -> x nin X;         ///
 Proof TninIn;
F0 := x nin Y;                                         assume;
F01 := X <: Y;                                         assume;
F02 := x in X;                                         assume;
F1  := x in Y;                                         is TinIn(F02 & F01);   // (p->q & p) -> q;
F2 := false;                                           is F0 ! F1;    
 end Proof TninIn;

! TIneq := X <: Y -> (X = Y == Y <: X);                  // Staut; // (p->q) -> ((p==q) == (q->p));
 Proof TIneq;
F0 := X <: Y;                                          assume;
F1 := X = Y == X <: Y & Y <: X;                        is Axext; by F0, Taut(true & p == p);
F2 := X = Y == Y <: X;
 end Proof TIneq;

! TInemp1 := {} = X == X <: {};                        is Staut; // is TIneq(TempIn); by Teqvsym;
! TInemp2 := X <: {} == {} = X;                        is Staut; // by Axsym;
! TInemp := X <: {} == X = {};                         is Staut;            // ! Axext1 := X=Y -> X<:Y;
! TIneq1 := X<:Y or X=Y == X<:Y;                       byeq Taut9a(Axext1); // ! Taut9a := (p -> q) -> (q or p == q); 
!! TIn_nin := X <: Y & z nin Y -> z nin X;

! TInnemp := X ~= {} & X <: A -> A ~= {};              // is Staut;
 Proof TInnemp;
F0 := X ~= {};                                         assume;
F01 := X <: A;                                         assume;
F02 := A = {};                                         assume; with F01;
F1 := X <: {};                                         by TInemp;
F2 := X = {};
F3 := false;                                           is F0 ! F2;
 end Proof TInnemp;

! TAIneq := All(a,All(b,All(X, X in set & a in X & b in X & X <: {a} -> a=b)));
 Proof TAIneq;
assume(a); assume(b); assume(X);
F00 := X in set;                                       assume;
F0 := a in X;                                          assume;
F01 := b in X;                                         assume;
F02 := X <: {a};                                       assume; by AxIn;
F03 := All(x, x in X -> x in {a});                     by Axcoll1;
F04 := All(x, x in X -> x = a);
F1 := b=a;                                             is F04(F01); by Axsym;
F2 := a=b;
 end Proof TAIneq;

! TSIn := {a} <: X1 == a in X1;                    ///
 EqProof TSIn;
F1 := {a} <: X1;                                        by AxIn;
F2 := All(x, x in {a} -> x in X1);                      by Axcoll1;
F3 := All(x, x = a -> x in X1);                         by TAlleq;
F4 := a in X1;
 end EqProof TSIn;

! TSIn_a := a in X1 == {a} <: X1;                       by Teqvsym; TSIn;    // was TSIn_a := a in X == {a} <: X;
 
! TSIn1 := X <: {a} == All(x,x in X -> x=a);            byeq AxIn, Axcoll1;

! TSIn2 := X <: {a} & X ~= {} -> a in X;         /// line 600, main.his: 600  s= ! TSIn2 := X <: {a} & X ~= {} -> a in X;
 Proof TSIn2;
F0 := X <: {a};                                        assume;
F01 := X ~= {};                                        assume; by TinnempE;
F02 := Existx(x, F02a := x in X);
F1 := x in {a};                                        is F02a ! F0; by Axcoll1;
F2 := x = a;                                           with F02a;
F3 := a in X;
Goal := X = {a};                                       by Axext; F0 & G0;
G0 := {a} <: X;                                        by TSIn; F3;
 end Proof TSIn2;

! TSIn2a := X <: {a} & ~(X = {}) -> a in X;            by Axneqr; TSIn2;

! TSIn3 := X <: {a} == X = {} or X = {a};              ///   
 Proof TSIn3;                                          by Deqv; L1 & L2;
L1 :=  X <: {a} -> (X = {} or X = {a});                by Taut((p->(q or r)) == (p & ~q ->r));
L1a := X <: {a} & ~(X = {}) -> X = {a};
  Proof L1a;
K0 := K1 & K2;                                         assume;
K1 := X <: {a}; 
K2 := ~(X = {});  
K3 := a in X;                                          is TSIn2a(K0); by TSIn_a; // -TSIn; !!!!!!!
K4 := {a} <: X;
K5 := X = {a};                                         is Axext01(K1 & K4);
  end Proof L1a;
L2 :=  X = {} or X = {a} -> X <: {a};
  Proof L2;           
F0 := X = {} or X = {a};                               assume;                   // !! Axreimp := Sb(Q,x,y) -> (x=y -> Q);
Goal :=  X <: {a};                                     by Case2(F0); F1 & F2;    // L2a & L2b;
F01 := Sb(F01a, X, {});                                is Red;
F1 := X = {} -> (F01a := X <: {a});                    is Axreimp(F01);         // byimp Axreimp;  //  is TSBEimp1 ! Staut({} <: {a}); 
F02 := Sb(F02a, X, {a});                               is Red;
F2 := X = {a} -> (F02a := X <: {a});                     is Axreimp(F02);         // byimp Axreimp;  // is TSBEimp1 ! Staut({a} <: {a});
  end Proof L2;
 end Proof TSIn3;

!! TSIn4 := X <: {a} & X ~= {} -> X = {a};     // is Taut( ! TSIn3 := X <: {a} == X = {} or X = {a};
!! TSIn4a := X <: {a} -> (X ~= {} -> X = {a}); 
!! TSIn4c := X <: {a} ->  one(X) == X ~= {} ;
!! TSIn4b := X <: {a} & b in X -> X = {a};

! TSeq1 := X = {a} == a in X & All(x, x in X -> x=a);  byeq Axext, TSIn1,TSIn,Tconjsym;
                                                       by Teqvneg,Axneqr,TNand,Axninr,TNAll,TNimp,Axneqr; 
! TSneq1 := X ~= {a} == a nin X or Exist(x, x in X & x ~= a);     // not used 

! TSeq2 := All(a,All(b, Goal := {a} <: {b} == a = b));        // ! TSeq2 := All(a,All(b, Goal_TSeq2 := {a} <: {b} == a = b)); Error in rnam;
 Proof TSeq2;
assume(a); assume(b);
Goal;                                                  by Deqv; L1 & L2;   // Goal := {a} <: {b} == a = b;  // Goal_TSeq2; see dd 01.30.23
L1 := {a} <: {b} -> a = b;
  Proof L1;
F0 := {a} <: {b};                                      assume; by AxIn;
F1 := All(x, x in {a} -> x in {b});                    by Axcoll1;
F2 := All(x, x=a -> x = b);                            by TAlleq;       // line 650 main.his: 650  s= F2 := All(x, x=a -> x = b);  
F3 := a=b;
  end Proof L1;
L2 := a=b -> {a} <: {b};                               // byimp Axreimp; // is TSBEimp ! Staut({a} <: {a});
  Proof L2; 
F0 :=  a=b;                                            assume;
G0 := {a} <: {b};                                      by F0;      // Sb(Q,x,y) = Sb({a]={b],a,b) = {b}={b}; 
G1 := {b} <: {b};                                      is Staut;
  end Proof L2;
 end Proof TSeq2;

!! TSeq3 :=  X ~= {} -> (X ~= {a} -> E[x:X, x ~= a]);
!! TSeq4 := X={a} -> X ~= {};

// ----------------------------------------------intersection
!! AxI := a in X1/\Y1 == a in X1 & a in Y1;
! TIab := X2/\Y2 = {x; x in X2 & x in Y2};                  by AxextA,AxI,Axab; is Taut; // was TIin

! TInI := B <: A == A/\B = B;                          is Staut; by TIab;    // 663, not 662
! TInIab := B <: A == {x; x in A & x in B} = B;        // was TInab2: , not Y !!!
! TInI1 := B <: A == B = A/\B;                         is Staut;   
// ! TInI1a := B <: A == A/\B = B;                        is Staut;  // same as TInI := B <: A == A/\B = B;
! TInI2 := B <: A == B = B/\A;                         is Staut;
! TInI2a := B <: A == B/\A = B;                        is Staut;
! TImr := X1 <: X2 -> X1/\B <: X2/\B;                  is Staut; // Intersection monotonicity right;
! TInI3 := A <: B -> A = B/\A;                         is Staut;   // ??? == ???

! TabconjI := {x; P(x) & Q(x)} = {x; P(x)} /\ {x; Q(x)}; 
 Proof TabconjI;                                                   by AxextA;
F1 := All(y,y in {x; P(x) & Q(x)} == y in {x; P(x)} /\ {x; Q(x)}); by Axab,AxI;
F2 := All(y, P(y) & Q(y) == y in {x; P(x)} & y in {x; Q(x)});      by Axab; // , Axab;
F3 := All(y, P(y) & Q(y) == P(y) &  Q(y));                         is Taut;
 end Proof TabconjI;
                                                                  // line 678, main.his:  678  s= 
! TabQI := {x; x in A & Q(x)} = A /\ {x;Q(x)};          //  was TInab4a
 Proof TabQI;                                         by AxextA;      // !! AxextA := X = Y == All(x, x in X == x in Y); 
F1 := All(x,x in {x; x in A & Q(x)} == x in  A /\ {x;Q(x)}); by Axab, AxI;  // 2408
F2 := All(x, x in A & Q(x) == x in A & x in {x;Q(x)});       by Axab;
F3 := All(x, x in A & Q(x) == x in A & Q(x));                is Taut;
 end Proof TabQI;

! TInab := X1 <: X2 -> {x1 ; x1 in X1 & Q(x1)} <: {x2 ; x2 in X2 & Q(x2)}; by TabQI,TabQI; is Instance(TImr); // syntax to skip a TabQi ???

! TInab1 := S <: {x; x in T & Q1(x)} == S <: T & All(x, x in S -> Q1(x)); 
 EqProof TInab1;                                                          // line 689, main.his: 690  s=  EqProof TInab1;
F1 := S <: {x; x in T & Q1(x)};                            by AxIn;
F2 := All(x, x in S -> x in {x; x in T & Q1(x)});          by Axab;
F3 := All(x, x in S -> x in T & Q1(x));                    by Taut15; // ((p->q&r)==(p->q)&(p->r));
F4 := All(x, (x in S -> x in T) & (x in S -> Q1(x)));      by TAllconj;
F5 := All(x, x in S -> x in T) & All(x, x in S -> Q1(x));  by -AxIn;
F6 := S <: T & All(x, x in S -> Q1(x));
 end EqProof TInab1;

// TInab2: see TInIab

! TInab3 := {x ; P(x)} <: {x ; Q(x)} == All(x, P(x) -> Q(x));              // line 700, main.his: 701  s= ! TInab3 := ...
 EqProof TInab3;
F1 := {x ; P(x)} <: {x ; Q(x)};                              by AxIn, Axab;
F2 := All(x, P(x) -> Q(x));
 end EqProof TInab3;
                                                             // TInI3 := B <: A -> B = A/\B;
// TInI := B <: A -> A/\B = B;                               // after by TabQI: {x ; Q(x)} <: T -> {x1 ; Q(x1)} = T /\{x2; Q(x2)}
! TInab4 := {x ; Q(x)} <: T -> {x1 ; Q(x1)} = {x2; x2 in T & Q(x2)};     by TabQI; is Instance(TInI3); // eliminate TInI3
 // TInab4b1 := {x ; Q} <: A ->  {x1 ; Q} = A /\ {x;Q};      by Axsym;
 // TInab4b2 := {x ; Q} <: A ->  A /\ {x;Q} = {x1 ; Q};      is Instance(TInI);

!! TInab5 := {x; x in t & Q(x)} <: t; 
!! TInab5a := {x; x in t; Q(x)} <: t;
!! TInab5b := {x; x in t; Q(x); Q1(x)} <: t;

! TInab6:= B <: t -> {x:t; x in B} = B;
 Proof TInab6;
F0 := B <: t;                                                assume;
G0 := {x:t; x in B} = B;                                     by AxextA;  // !! AxextA := X = Y == All(x, x in X == x in Y); 
G1 := All(x, x in {x:t; x in B} == x in B);                  by Axab;
G2 := All(x, x in t & x in B == x in B);
  Proof G2;
K0 := assume(x);
G3 := x in t & x in B == x in B;                             by Deqv; L1 & L2;
L1 := x in t & x in B -> x in B;                             is Taut(p&q -> q);
L2 := x in B -> x in t & x in B; 
   Proof L2;
K0 := x in B;                                                assume;
K1 := x in t;                                                is TinIn(K0 & F0); // TinIn := x in X & X <: Y -> x in Y;
K2 := x in t & x in B;                                       is K1 & K0;
   end Proof L2;
  end Proof G2;
 end Proof TInab6;

!! TInab7:= B <: t -> ({x ; x in t} && x in B) = {x; x in B};

! Tab2In := {x,y ; [x,y] in S & Q1(x,y)} <: S;
 Proof Tab2In;                                               by AxIn;
G0 := All(z,z in {x,y ; [x,y] in S & Q1(x,y)} -> z in S);
  Proof G0;
assume(z);
F0 := z in {x,y ; [x,y] in S & Q1(x,y)};                     assume;  by Axab;
F01 := Existx(x0, Existx(y0, (F01a := z=[x0,y0]) & ((F01b := [x0,y0] in S) &  Q1(x0,y0))));
 Goal := z in S;                                             is Axeqconj1(F01a & F01b);  // !! Axeqconj1 := a=b & Q -> Sb(Q,b,a);
  end Proof G0;
 end Proof Tab2In;

     //--------------------------------------P[X]---------------------------
dcl[P[,set,set];                            // all subsets
!! AxP := Z in P[Y] == Z <: Y;
! TempinP := {} in P[X];                         by AxP; is TempIn;     //  TempIn := {} <: X
! TPneqemp := P[X] ~= {};                        is Tinnemp(TempinP);   //  Tinnemp := x in X -> X ~= {}
! TSinP := {a} in P[X] == a in X;                byeq AxP, TSIn;        //  variables in TSinP and AxP must be all different

! TininP := x in X2 & X2 in P[Y2] -> x in Y2;    by AxP; is TinIn;
!! TinInP := X in Y & Y <: P[Z] -> X <: Z;                 

!! TabinP := {x:t; Q(x)} in P[t];

// dcl[<<, set, set, bool];                                   // Inclusion strict

!! AxIns := X << Y == X <: Y & X ~= Y;           by Axneq;
!  AxIns1 := X << Y == X <: Y & ~(X = Y);
 
!  TIns1 := X <: Y == X << Y or X = Y;           // was Axcoll1
 EqProof -TIns1;
F1 := X << Y or X = Y;                           by AxIns1;
F2 := X <: Y & ~(X =Y) or X=Y;                   by Taut10b;  // Taut10b := p & ~q or q == p or q; 
F3 := X <: Y or X=Y;                             by TIneq1;
F4 := X <: Y;
 end EqProof -TIns1;

! TIns2 := X1 << Y1 -> Exist(z, z in Y1 & z nin X1);  // was Axcoll1E
 Proof TIns2;
F0 := X1 << Y1;                                  assume; by AxIns; F0a & F0b;
F0a := X1 <: Y1;                                 // 772, not 773
F0b := X1 ~= Y1;
F01 := ~(Exist(z, z in Y1 & z nin X1));          assume; by Axnin, NExist, Taut(~(p & ~q) == (p->q)); // ??? add simp(~(z nin X))
F02 := All(z, z in Y1 -> z in X1);               by -AxIn;  // !! AxIn := X2 <: Y2 == All(x, x in X2 -> x in Y2);
F03 := Y1 <: X1;                                 //  with F0a;  // ! Axext01 := X <: Y & Y <: X -> X = Y;
F1 := X1 = Y1;                                   is F0a ! F03;   with F0b;
false;                                           // F2 := false; 
 end Proof TIns2;

! TinPIIn := X in P[Z] & Y in P[Z] -> X/\Y <: Z; by AxP,AxP; is Staut;  // ! TInI5 := Y <: X & Y1 <: X -> Y/\Y1 <: X;    is Staut;
  
! TPm := X1 <: Y1 == P[X1] <: P[Y1];             // ! TPm := A[X,Y, X <: Y == P(X) <: P(Y)];  
 Proof TPm;                                      by Deqv; L1 & L2;
// Goal := X1 <: Y1 == P[X1] <: P[Y1];           by Deqv; L1 & L2;
L1 := X1 <: Y1 -> P[X1] <: P[Y1];
  Proof L1;
F0 := X1 <: Y1;                                  assume;
Goal1 := P[X1] <: P[Y1];                         by AxIn, AxP;
G0 := All(Z, Z <: X1 -> Z <: Y1);
   Proof G0;
assume(Z);
K0 := Z <: X1;                                   assume;
Goal1a := Z <: Y1;                               is TInIn(K0 & F0);  // ! TInIn := X0 <: Y0 & Y0 <: Z0 -> X0 <: Z0; // was K0 ! F0;
   end Proof G0;
  end Proof L1;
L2 := P[X1] <: P[Y1] -> X1 <: Y1;
  Proof L2;
K00 := P[X1] <: P[Y1];                           assume; by AxIn, AxP;
K01 := All(Z, Z <: X1 -> Z <: Y1);
K02 := X1<:X1 -> X1<:Y1;                         is K01(X1); by TInrefl;               // ! TInrefl := X <: X; 
K03 := true -> X1<:Y1;                           by Taut((true -> p) == p);
Goal2 := X1 <: Y1;                                 // is K01(X1) ! X1 <: X1;           implement later !!!!!
  end Proof L2;
 end Proof TPm;

! TPin1 := X in P[X];                              by AxP; is Staut;  // X <: X;
! TInI5 := Y <: X & Y1 <: X -> Y/\Y1 <: X;         is Staut;
! TPinI := A in P[X] & B in P[X] -> A/\B in P[X];  by AxP,AxP,AxP; is TInI5;
!! TPinIn :=  X in P[A] & A <: B -> X in P[B];

dcl[P1[,set,set];                           // all nonempty subsets
!! AxP1 := S in P1[Y] == S <: Y & S ~= {};
! TP1P := S in P1[Y] == S ~= {} & S in P[Y];       by AxP1,AxP;      is Taut;   // (S <: Y & S ~= {} == S ~= Y & S <: Y;
! TP1inP := P1[Y] <: P[Y];                         by AxIn,AxP1,AxP; is Taut;   // AxIn := X2 <: Y2 == All(x, x in X2 -> x in Y2);
!! TP1nemp := x in P1[X] -> x~={};
!! TP1in := X ~= {} -> X in P1[X];
!! TP1emp := X = {} == P1[X] = {};
!! TP1Nemp := X ~= {} == P1[X] ~= {};
!! TP1emp0 := P1[{}] = {};
!! TP1m := X <: Y -> P1[X] <: P1[Y];
!! TP1m1 := X <: Y -> P1[X] <: P[Y];
!! TP1inin := S in P1[Y] & x in S  -> x in Y;        
!! TP1inIn :=  X in P1[A] & A <: B -> X in P1[B];

!! AxU := a1 in X1\/Y1 == a1 in X1 or a1 in Y1 ;             // TinU := a in X\/Y == a in X or a in Y;
!! Axcoll3 := z in {a1,a2,a3} == z=a1 or z=a2 or z=a3;

! TUab := {x; x in X0\/Y0 & P} = {x; x in X0 & P} \/ {x; x in Y0 & P};
 Proof TUab;                                                     by AxextA;   // !! AxextA := X = Y == All(x, x in X == x in Y); 
G0 := All(x, Goal_G0 := x in {x; x in X0\/Y0 & P} == x in {x; x in X0 & P} \/ {x; x in Y0 & P});  // scopeden(Goal_G0) = G0;
  Proof G0;                                               // G0 depends on Goal_G0, so wrdep(G0,Goal);
assume(x);  // opens the scope htbv(x) = G0;                                         
Goal_G0;    by Axab, AxU, AxU, Axab;                       // rnam will look for Goal_G0 in htbv(x) = G0;  
F1 := (x in X0 or x in Y0) & P == x in X0 & P or x in Y0 & P; is Taut((p or q)&r == p&r or q&r);
  end Proof G0;
 end Proof TUab;
                                                                         // ((p or q)&r == p&r or q&r);
! TUab_1 := {x; x in X0\/Y0 & Q} = {x; x in X0 & Q} \/ {x; x in Y0 & Q}; by AxextA, Axab, AxU, AxU, Axab, Axab; is Taut; 
! TninU := a nin X0\/Y0 == a nin X0 & a nin Y0;          byeq Axnin,AxU,TNor,Axninr;
! TU1 := X \/ X = X;                                     is Staut;
! TU2 := X <: Y == X\/Y = Y;                             is Staut;
! TU2a := X <: Y == Y\/X = Y;                            is Staut;
! TUnIn := X = Y\/Z -> Y <: X;                           is Staut; // not Taut((p==q\/r))->(q->p))!!!;
! TUemp := X \/ {} = X;                                  is Staut;
! TUcomm := X \/ Y = Y \/ X;                             is Staut;
! TinUS := a in X0 \/ {a};                               by AxU, TinS; is Taut(p or true);
! TinU1 := a in X0 -> a in X0 \/ Y0;                     by AxU; is Taut(p -> p or q); // by TUcomm; ??? 12.16.19 correct !!!
! TinU1a := a in X0 -> a in Y0 \/ X0;                    by AxU; is Taut(p -> q or p);
!! TUin_nin := x in X\/Y & x nin Y -> x in X;
!! TUin1 := x in X -> x in X\/Y;
! TUIn2 := X \/ Y <: Z == X <: Z & Y <: Z;               is Staut; // (p or q)->r == (p->r)&(q->r);
! TUIn3 := X1 \/ Y1 \/ Z1 <: S == X1 <: S & Y1 <: S & Z1 <: S; is Staut;
! TUI2nS := X\/{a}\/Y  <: Z == X <: Z & a in Z & Y <: Z; byeq TUIn3, TSIn;
! TIninUS1 := X1 \/ {a} <: Y1 == X1 <: Y1 & a in Y1 ;    byeq TUIn2, TSIn; by Teqvsym;
! TIninUS := X1 <: Y1 & a in Y1 == X1 \/ {a} <: Y1;            
! TIU1 := X <: X \/ Y;                                   is Staut; // p -> p or q
! TIU2 := Y <: X \/ Y;                                   is Staut; // q -> p or q
! TInU := X <: Y -> X \/ Z <: Y \/ Z;                    is Staut; // (p->q) -> ((p or r) -> q or r);
! TInU1 := X <: Y & X1 <: Y1 -> X\/X1 <: Y\/Y1;          is Staut; // (p->q) & (p1->q1) -> (p or p1 -> q or q1); 

! TUcoll2 := {a,b} = {a} \/ {b};
 Proof TUcoll2;                                          by AxextA;
G0 := All(x, x in {a,b} == x in {a} \/ {b});             by Axcoll2, AxU,Axcoll1; // ,Axcoll1;
G1 := All(x, x=a or x=b == x=a or x=b);                  is Taut; // by Axcoll1; is Taut;
 end Proof TUcoll2;

! TUcoll3 := {a,b,c} = {a,b} \/ {c};
 Proof TUcoll3;                                                  by AxextA;
G0 := All(x, x in {a,b,c} == x in {a,b} \/ {c});                 by Axcoll3, AxU;
G1 := All(x, x=a or x=b or x=c == x in {a,b} or x in {c});       by Axcoll2, Axcoll1;
G2 := All(x, x=a or x=b or x=c == (x=a or x=b) or x = c);        is Taut;
 end Proof TUcoll3;

! TUabor := {x ; P1(x) or Q1(x)} = {x;P1(x)} \/ {x;Q1(x)};                   by AxextA, Axab, AxU, Axab,Axab; is Taut;

/* !! Axab2 := z in {x,y; P} == Exist(x,Exist(y, z = [x,y] & P));
!! Axab2 := z in {x,y; P} == E[dxy, z = [x,y] && P];

! TUabor2 := dxy && (P1 or Q1) = dxy && P1 \/ dxy && Q1;
 Proof TUabor2;                                                            by AxextA;                            
G0 := All(z, z in dxy && (P1 or Q1) == z in (dxy && P1 \/ dxy && Q1));     by AxU;
G1 := All(z, z in dxy && (P1 or Q1) == z in dxy && P1 or z in dxy && Q1); 
// G1 := All(z, z in {x,y ; P1 or Q1} == z in {x,y ; P1} or z in {x,y ; Q1}); by Axab2;  // ,Axab;
G2 := All(z, _Goal := Exist(x, Exist(y, z=[x,y] &(P1 or Q1))) == Exist(x,Exist(y, z=[x,y] & P1)) or Exist(x, Exist(y, z=[x,y] & Q1)));
  Proof G2; assume(z);
   EqProof _Goal;                                                             // _Goal;
// F1 := Exist(x, Exist(y, z=_(x,y) &(P1 or Q1)));                      by AxSbor;
F2 := Exist(x, Exist(y, z=[x,y] &(P1 or Q1)));                          by Taut(p&(q or r) == p&q or p&r);
F3 := Exist(x, Exist(y,  z=[x,y] & P1 or z=[x,y] & Q1));                by HB9;
F4 := Exist(x, Exist(y,  z=[x,y] & P1) or  Exist(y,  z=[x,y] & Q1));    by HB9;
F5 := Exist(x, Exist(y,  z=[x,y] & P1)) or  Exist(x, Exist(y,  z=[x,y] & Q1));
   end EqProof _Goal;
  end Proof G2;
 end Proof TUabor2; 

! TUabor2 := {x,y ; P1 or Q1} = {x,y ; P1} \/ {x,y ; Q1};
 Proof TUabor2;                                                            by AxextA;                            
G0 := All(z, z in {x,y ; P1 or Q1} == z in {x,y ; P1} \/ {x,y ; Q1});      by AxU;
G1 := All(z, z in {x,y ; P1 or Q1} == z in {x,y ; P1} or z in {x,y ; Q1}); by Axab2;  // ,Axab;
G2 := All(z, _Goal := Exist(x, Exist(y, z=[x,y] &(P1 or Q1))) == Exist(x,Exist(y, z=[x,y] & P1)) or Exist(x, Exist(y, z=[x,y] & Q1)));
  Proof G2; assume(z);
   EqProof _Goal;                                                             // _Goal;
// F1 := Exist(x, Exist(y, z=_(x,y) &(P1 or Q1)));                      by AxSbor;
F2 := Exist(x, Exist(y, z=[x,y] &(P1 or Q1)));                          by Taut(p&(q or r) == p&q or p&r);
F3 := Exist(x, Exist(y,  z=[x,y] & P1 or z=[x,y] & Q1));                by HB9;
F4 := Exist(x, Exist(y,  z=[x,y] & P1) or  Exist(y,  z=[x,y] & Q1));    by HB9;
F5 := Exist(x, Exist(y,  z=[x,y] & P1)) or  Exist(x, Exist(y,  z=[x,y] & Q1));
   end EqProof _Goal;
  end Proof G2;
 end Proof TUabor2;

 !! Axab2a := z in {x,y; P(x,y)} == Exist(x,Exist(y, z = [x,y] & P(x,y)));

! TUabor2a := {x,y ; P1(x,y) or Q1(x,y)} = {x,y ; P1(x,y)} \/ {x,y ; Q1(x,y)};
 Proof TUabor2a;                                                            by AxextA;                            
G0 := All(z, z in {x,y ; P1(x,y) or Q1(x,y)} == z in {x,y ; P1(x,y)} \/ {x,y ; Q1(x,y)});      by AxU;
G1 := All(z, z in {x,y ; P1(x,y) or Q1(x,y)} == z in {x,y ; P1(x,y)} or z in {x,y ; Q1(x,y)}); by Axab2a;  // ,Axab;
G2 := All(z, _Goal := Exist(x, Exist(y, z=[x,y] &(P1(x,y) or Q1(x,y)))) == 
                      Exist(x, Exist(y, z=[x,y] & P1(x,y))) or Exist(x, Exist(y, z=[x,y] & Q1(x,y))));
  Proof G2; assume(z);
   EqProof _Goal;                                                             // _Goal;
// F1 := Exist(x, Exist(y, z=_(x,y) &(P1 or Q1)));                      by AxSbor;
F2 := Exist(x, Exist(y, z=[x,y] &(P1(x,y) or Q1(x,y))));                          by Taut(p&(q or r) == p&q or p&r);
F3 := Exist(x, Exist(y,  z=[x,y] & P1(x,y) or z=[x,y] & Q1(x,y)));                by HB9;
F4 := Exist(x, Exist(y,  z=[x,y] & P1(x,y)) or  Exist(y,  z=[x,y] & Q1(x,y)));    by HB9;
F5 := Exist(x, Exist(y,  z=[x,y] & P1(x,y))) or  Exist(x, Exist(y,  z=[x,y] & Q1(x,y)));
   end EqProof _Goal;
  end Proof G2;
 end Proof TUabor2a;
*/
// ! TUscor := d && (P or Q = {x|P(x)} \/ {x|Q(x)};        not used

! TUabneg := {x; x in T & P} \/ {x; x in T & ~P} = T; 
 Proof TUabneg;                                                  by AxextA;
G0 := All(x, _G01 := x in {x; x in T & P} \/ {x; x in T & ~P} == x in T);  // _G01 - global name
  Proof G0;  assume(x);
   EqProof _G01;
F1 := x in {x; x in T & P} \/ {x; x in T & ~P};            by AxU, Axab,Axab;
F2 := x in T & P or x in T & ~P;                           by Taut(p&q or p&(~q)==p);
F3 := x in T;
   end EqProof _G01;
  end Proof G0;
 end Proof TUabneg;

!! TUS1 := X in {X} \/ Y;
                                                           // !! Axcoll2 := x1 in {a1,b1} == x1=a1 or x1=b1;
! TUS2 := {x} \/ {y} = {x,y};                              by AxextA, AxU, Axcoll1,Axcoll1, Axcoll2; is Taut;
! TU4Eor := X1\/X2\/X3\/X4 ~= {} == X1 ~= {} or X2 ~= {} or X3 ~= {} or X4 ~= {};  // Staut; ??? not Horn formula ???
! TUASIn := A \/ {a} <: B == A <: B & a in B;              byeq TUIn2, TSIn;                     
// TIncoll2 := {a,b} <: X == a in X & b in X;              // see Tcoll2In := {a,b} <: Z == a in Z & b in Z;
!! TInE := X <: Y == Exist(Z, Y = X\/Z);                    /// Proof in 13 Dp
// TIninS :=  X \/ {a} <: Y == X <: Y & a in Y;            byeq TSIn, TUIn2; // not used
!! TinPU := X in P[A] & Y in P[A] == X \/ Y in P[A];        // use X <: A & Y <: A == X\/Y <: A;

// ----------------/\----------Intersection(continue)   TinnempE := X ~= {} == Exist(x, x in X);
! TIAS := All(x, x in B/\{a1} -> R(x)) == (a1 in B -> R(a1)); byeq AxI,Axcoll1,Taut((p&q -> r) == (q->(p->r))),TAlleq; 
! TISnemp := {a1} /\ {b1} ~= {} == a1=b1;                     byeq TinnempE, AxI, Axcoll1, Axcoll1, TExisteq ;
! TISemp1 := {a1} /\ {b1} = {} == a1 ~= b1;                   by Teqvneg, Axneqr, TNneq; TISnemp;
!! TinPI := X in P[A] & Y in P[A] == X /\ Y in P[A];        // use X <: A & Y <: A == X/\Y <: A;
!! TinIax := All(a,All(X,All(Y, a in X/\Y == a in X & a in Y)));     byeq AxI;
! TinIemp := All(a,All(X1,All(Y1, a in X1 & a in Y1 -> X1/\Y1 ~= {})));
 Proof TinIemp; assume(a); assume(X1); assume(Y1);
F0 := a in X1;                                        assume;
F01 := a in Y1;                                       assume;
F1 := a in X1/\Y1;                                    by AxI; F0 & F01;
Goal := X1/\Y1 ~= {};                                 is Tinnemp(F1);
 end Proof TinIemp;

! TinIemp1 := a in X1 & a in Y1 -> X1/\Y1 ~= {};        is TinIemp(a,X1,Y1);
! TninI := All(a,All(X,All(Y, a nin X/\Y == a nin X or a nin Y)));  byeq Axnin,AxI,TNand,Axninr,Axninr; 
! TIcomm := X/\Y = Y/\X;                                is Staut;
! TIIn1 := X/\Y <: X;                                   is Staut;
! TIIn2 := X/\Y <: Y;                                   is Staut;
! TInII := X<:Y -> X/\Z <: Y/\Z;                        is Staut;
! TInI4 := X<:Y == X/\Y = X;                            is Staut;
! TIn14a := X<:Y == Y/\X = X;                           is Staut;
! TInI2b := Y <: X1 /\ X2  == Y <: X1 & Y <: X2;        is Staut;
! TInI3a := Y <: X1 /\ X2 /\ X3  == Y <: X1 & Y <: X2 & Y <: X3; is Staut;
! TInI4a := A <: B & A <: C == A <: B/\C;               is Staut;
! TIemp1 := {} /\ X = {};                               is Staut; // false & p == false
! TIemp2 := X /\ {} = {};                               is Staut; // p & false == false

! TIemp3 := Y1 <: X1 & Y1 ~= {} -> X1/\Y1 ~= {};
 Proof TIemp3;
F0 := Y1 <: X1;              assume;               
F01 := Y1 ~= {};             assume; by TinnempE;
F1 := Existx(z, F1a := z in Y1);
F2 := z in X1;               is TinIn(F1a & F0);      // TinIn := x in X & X <: Y -> x in Y;
F3 := X1/\Y1 ~= {};          is TinIemp1(F2 & F1a);
 end Proof TIemp3;

! TIempU := X2/\Y2 = {} & Y2 ~= {} -> X2\/Y2 ~= X2;
 Proof TIempU; 
F0 :=  X2/\Y2 = {};           assume;
F01 := Y2 ~= {};              assume;
F02 := X2\/Y2 = X2;           assume; by -TU2a;          // TU2a := X <: Y == Y\/X = Y; 
F1 := Y2 <: X2;
F2 := X2/\Y2 ~= {};           is TIemp3(F1 & F01); with F0;
false;
 end Proof TIempU;
 
! TinI := {x; x in A ; x in B} = A/\B;                     // same as AxI
! TIaband := {x ; P & Q} = {x ; P} /\ {x ; Q};        by AxextA, AxI, Axab, Axab,Axab; is Taut;
! TIneqvI := A<:B == A/\B = A;                        is Staut;

! TIS := All(A,All(X,All(a, A/\X = {a} -> a in A & a in X)));
 Proof TIS; assume(A); assume(X); assume(a);
F0 := A/\X = {a};                                     assume;        // TInI2b := Y <: X1 /\ X2  == Y <: X1 & Y <: X2;
F01 := {a} <: A/\X;                                   is Axext2(F0); by TInI2b;     // Axext2 := X=Y -> Y<:X;
F1 := {a} <: A & {a} <: X;                            by TSIn;   // by TSIn; (isbe: double TSIn not needed)
F2 := a in A & a in X;
 end Proof TIS;

! TISemp := All(A, All(x, A/\{x} = {} == x nin A));                     // byeq TempAll,TinI,Taut(~(p & q) == (q -> ~p)),TinS,TAlleq;
 EqProof TISemp;                                                          // !! Axnin := x nin X == ~(x in X); 
assume(A); assume(x);
F1 := A/\{x} = {};                                    by TempAll, Axnin;  // TempAll := X = {} == All(x, x nin X);
F2 := All(z, ~(z in A/\{x}));                         by AxI;
F3 := All(z, ~(z in A & z in {x}));                   by Taut(~(p & q) == (q -> ~p)), Axcoll1, Axninr;
F4 := All(z, z=x -> z nin A);                         by TAlleq;
F5  := x nin A;
 end EqProof TISemp;

! TInempE := A/\B ~= {} == Exist(x, x in A & x in B); byeq TinnempE, AxI;

! TIempin := X1/\Y1 = {} & a in X1 & b in Y1 -> a ~= b;      //    Tinnemp := x in X -> X ~= {};
 Proof TIempin;
F0 := X1/\Y1 = {};                                    assume;
F01 := a in X1;                                       assume;
F02 := b in Y1;                                       assume;
F03 := a = b;                                         assume;  // !! Axeqconj1 := a=b & Q -> Sb(Q,b,a);
F04 := a in Y1;                                       is Axeqconj1(F03 & F02);
F1 := a in X1/\Y1;                                    by AxI; F01 & F04; 
F2 := X1/\Y1 ~= {};                                   is Tinnemp(F1);
false;                                                is F0 ! F2;      // Tneq1a := x=y & x~=y -> false;
 end Proof TIempin;

! TInIemp := A<:B & B/\C = {} -> A/\C = {};              is Staut;
! TIAemp := X1/\Y1 = {} == All(a, ~(a in X1 & a in Y1)); byeq TempAll, Axnin, AxI; // line 1000 main.his:1001  s= ! TIAemp := ...
// TIAS := All(xx, xx in B/\{a} -> Q) == a in B -> Sb(Q,xx,a); byeq AxI,Axcoll1,Taut((p&q -> r) == (q->(p->r))),TAlleq; 
// TISnemp := {a} /\ {b} ~= {} == a=b;                   byeq TinnempE, AxI, TExisteq ; by Teqvneg,TNneq,Axneqr; ///
 
! TI1 := X/\X = X;                                    is Staut;
! TIU := X/\Y <: X\/Y;                                is Staut;

dcl[NI,set,set,bool]; // Not Intersecting          // NI is a new binary relation symbol
!! AxNI := All(X,All(Y,  X NI Y == X/\Y = {}));
!! AxNI1 :=  X NI Y == X/\Y = {};                        by Teqvsym;
! AxNI1r := X/\Y = {} == X NI Y;
! TNIsym := X NI Y == Y NI X;                            is Staut;
! TNI1 := a in X1 & a in Y1 -> ~(X1 NI Y1);              by AxNI,Axneqr; is TinIemp1;
! TNIN := ~(X NI Y) == Exist(x, x in X & x in Y);        by AxNI,Axneqr; is TInempE; TNIN; by Teqvneg, TNN,NExist;
! TNI := X NI Y == All(x, ~(x in X & x in Y));           by TNand;
! TNI2 := X NI Y == All(x, ~(x in X) or ~(x in Y));
! TNI3 := X NI Y & Y ~= {} -> X\/Y ~= X;                 by AxNI; is TIempU;
! TNI4 := X NI Y & a in X & b in Y -> a ~= b;            by AxNI; is TIempin;
!! TNI4a := X NI Y & x in X -> x nin Y;
! TNI5 := A<:B & B NI C -> A NI C;                       by AxNI,AxNI; is TInIemp;   // TInIemp := A<:B & B/\C = {} -> A/\C = {};
! TNI5a := A<:B & A NI B -> A = {};                      is Staut;
// TNI6 := (A NI B & A1 NI B1 & A <: A1 & B <: B1 -> (A\/B = A1\/B1) == A=A1 & B=B1); is Staut;// proof in 13 Dp
// ! TNI6a := A NI B & A1 NI B1 & A <: A1 & B <: B1 & (A\/B = A1\/B1) -> A=A1 & B=B1; 

! TNI6a := A NI B  & A\/B = A1\/B1 & B1 <: B -> A <: A1;           // x in A, x nin B, x nin B1, x in A\/B, x in A1\/B1, x in A1;
 Proof TNI6a;                          // goal = TNI6a;  hnasume must change goal to A <: A1 and wrdep(TNI6a, A<:A1); 
F0 := A NI B;                          assume;
F01 := A\/B = A1\/B1;                  assume;
F02 := B1 <: B;                        assume;                     // goal is now G0;
G0 := A <: A1;                         by TInAall;                 // !! TInAll := All(A, All(B, A <: B == A[x:A, x in B]));
G1 := A[x:A, x in A1];                 // write link(G0, G1) into wrdep;
  Proof G1;                            // goal = G1; goal1=goal;
K0 := x in A;                          assume;                     // change goal to goal1 = x in A1, wrdep(goal,goal1), goal = goal1;
K1 := x nin B;                         is TNI4a(F0 & K0);          // !! TNI4a : X NI Y & x in X -> x nin Y;
K2 := x nin B1;                        is TIn_nin(F02 & K1);       // !! TIn_nin := X <: Y & z nin Y -> z nin X;            
K3 := x in A\/B;                       is TUin1(K0); by F01;       // !! TUin1 := x in X -> x in X\/Y;
K4 := x in A1\/B1;
K5 := x in A1;                         is TUin_nin(K4 & K2);       // ! TUin_nin := x in X\/Y & x nin Y -> x in X;
  end Proof G1;
 end Proof TNI6a;

! TNI6b := A NI B & A1 NI B1 & A <: A1 & B <: B1 & A=A1 & B=B1 -> A\/B = A1\/B1;
! TNI7 := A <: S & B NI S -> A NI B;                     is Staut;
// ! TNI8, TNI9;                                         // moved to 13 D
! TNI10 := A NI B & C <: A/\B -> C = {};                 is Staut;
! TNI11 := A NI B & A1 <: A & B1 <: B -> A1 NI B1;       is Staut;
// ! TNI12 := A NI B & A1 <: A & B1 <: B  -> (x in A1\/B1 == if(x in A, x in A1, x in B1)); // not used
// ! TNI13 := {a,b} NI {c,d} == a ~= c & a ~= d & b ~= c & b ~= d;          // not used
! TNI14 := B NI {a} == a nin B;                          by AxNI; is TISemp; // TISemp := A/\{x} = {} == x nin A;
! TNI14a := {a} NI B == a nin B;                         by TNIsym; TNI14;
! TNI15 := B NI A1 & B NI A2 -> A1\/B = A2\/B == A1 = A2; // move to D
! TNI16 := ~(X NI Y) == X/\Y ~= {};                      byeq AxNI1,Axneqr; by Teqvsym;
! TNI16a := X/\Y ~= {} == ~(X NI Y);
! TNIS := {a1} NI {b1} == a1 ~= b1;                      byeq TNI14, TninS, Tneqsym ;  // TninS;  !!!	replace !!!
! TninSNI := a nin X == {a} NI X;                        by Teqvsym; is TNI14a;
! TNIab := {Z ; P} NI {Z ; Q} == All(Z, ~(P & Q));       byeq TNI, Axab;
// ! TNIxor := A NI B == All(x, x in A\/B -> x in A xor x in B); // by TNI2,AxU;
// ! TNIxor1 := All(x, ~(x in A) or ~(x in B)) == All(x, x in A or x in B -> x in A xor x in B);  byimp HB17a;
// ! TNIxor2 := All(x, ~(x in A) or ~(x in B) == x in A or x in B -> x in A xor x in B); is Taut;
! TNIU := A NI B\/C == A NI B & A NI C;                  is Staut;

dcl[IN,set,set,bool];                                    // IN: intersecting;

!! AxIN := X IN Y == X/\Y ~= {};                         by Teqvsym; // Not Intersecting  X/\Y ~= {}
AxINr := X/\Y ~= {} == X IN Y;                                                                  
TINsym := X1 IN Y1 == Y1 IN X1;                          byeq AxIN, TIcomm, AxINr;
TINNI := X IN Y == ~(X NI Y);                            byeq AxIN,TNI16a; by Teqvsym;
TINNIr := ~(X NI Y) == X IN Y;
TINNI1 := X NI Y == ~(X IN Y);                           by Taut((p == ~q) == (q == ~p)); TINNI;
TIN1 := a in X & a in Y -> X IN Y;                       by AxIN; is TinIemp1;
TINS := {a} IN {b} == a = b;                             by AxIN; is TISnemp;
TINE := X IN Y == Exist(z, z in X & z in Y);             by AxIN; is TInempE;

// Set difference: --  
!! Lsetdift := X in finset &  Y in set -> X--Y in finset;
setdif := dcl[--, set,set,set]; // AxD := X--Y = {a | a in X & a nin X}; // difference of X,Y               
!! AxD := a1 in X1 -- Y1 == a1 in X1 & a1 nin Y1;  by Teqvneg,Axninr,TNand,Axninr,TNnin;
! TninDin := a1 nin X1--Y1 == a1 nin X1 or a1 in Y1;
! AxD1 :=  a1 in X -- Y == a1 in X & ~(a1 in Y); by -Axnin; is AxD;            // Taut((p==q&r) -> (p->q)) stopped working ! 12.11.21
! TDin1 := a1 in X1 -- Y1 -> a1 in X1;              is Taut3(AxD);             // Taut3 := (p==q&r) -> (p->q); 
! TDin2 := a1 in X1 -- Y1 -> a1 nin Y1;             is Taut3a(AxD);            // ! Taut3a := (p==q&r) -> (p->r); 
// ! TDin_1 := a in X -- {b} == a in X & (a ~= b);     byeq AxD, TninS;  // line 1060 correct!!! same as TDSin beloa
! TDin_2 := a in X -- {b,c} == a in X & (a ~= b & a ~= c); byeq AxD, Tcoll2nin;
! TDemp := X -- {} = X;                       is Staut; // p & (~false) == p
! TDemp1 := X -- X = {};                      is Staut; // p & (~p) == false
! TDemp2 := X <: Y & (Y--X = {}) -> X = Y;    is Staut;
! TDempIn := C -- D = {} ==  C <: D;          is Staut;   by Teqvneg, Axneqr;
! TDempIn1 := C -- D ~= {} ==  ~(C <: D);       // Axext03 := X <: Y & X ~= Y -> ~(Y <: X);
! TDemp3 := X--Y = {} & X ~= Y -> ~(Y <: X);  by TDempIn,Axneq; Axext02;
! TDemp4 := A <: B & A ~= B -> B--A ~= {};    by TDempIn1; is Axext03;
! TInD := X <: Y--Z == X <: Y & X NI Z;       is Staut;
! TInDInD := X <: Y -> X--Z <: Y--Z;          is Staut;             
! TInDIn := X <: Y -> X--Z <: Y;              is Staut;     // line 20
! TInDIn1 := X <: Y -> Z--Y <: Z--X;          is Staut;          
! TInDU := X <: Y -> (Y -- X) \/ X = Y;       is Staut;     // TSIn := {a} <: X1 == a in X1;
! TinDU := a in Z -> Z--{a} \/ {a} = Z;       by -TSIn; is TInDU;
! TInDU1 := X1 <: X -> (X -- X1) \/ (X1 \/ Y) = X \/ Y; is Staut;
! TInDU2 := X <: X1 -> (X \/ Y) -- X1 <: Y;   is Staut;
!! TInDU3 := All(X, All(Y, X <: Y -> Y = X \/ (Y -- X)));    // is Staut; 
!! TInDU3a := X <: Y -> Y = X \/ (Y -- X);
! TDInU := X -- Y <: X \/ Z;                  is Staut; // p & ~q -> p or r;
! TDIn := X -- Y <: X;                        is Staut; // p & ~q -> p;
! TInID := X <: Y -> Z /\ (X -- Y) = {};      is Staut; // TInDemp ! TIemp2;
! TDInUD := X -- A <: (X\/Y) -- A;            is Staut;     // line 30
! TDI := X -- X/\Y = X--Y;                    is Staut;   
! TID := X/\(X--Y) = X--Y;                    is Staut;
! TUDIn := (X \/ Y) -- X <: Y;                is Staut;
! TIempD1 := X NI Y ->  (X \/ Y) -- X = Y;    is Staut;  // TninS := x nin {a} == x ~= a;
! TIempD2 := X NI Y ->  (X \/ Y) -- Y = X;    is Staut;
! TIempD3 := X NI Z -> X <: (X \/ Y) -- Z;    is Staut;  // TninDin := a nin X--Y == a nin X or a in Y;
// TNI7 := A <: S & B NI S -> A NI B;          is Staut;     // line 40
! TNI8 := B <: A & B NI C -> B <: A--C;       is Staut;
! TNI9 := B NI A--B;                          is Staut;  // TNI14 := B NI {a} == a nin B; 
! TNII4 := Z = X\/Y & X NI Y -> Y = Z--X;     is Staut;
! TDInIn := Y--X <: Z & X <: Z -> Y <: Z;     is Staut;  // TISemp := A/\{x} = {} == x nin A; 
! TInNID := X <: Y & Z NI X -> X <: Y -- Z;   is Staut;
! TInninD := X <: Y & a nin X -> X <: Y -- {a}; by -TNI14a; is TInNID;  // is Staut; // ! TNI14a := {a} NI B == a nin B; // was TNI14: C3;
! TDSin := a in X--{b} == a in X & a ~= b;    byeq AxD,TninS;          // line 1094, correct !!!
! TninUSD := a nin X -> X \/ {a} -- {a} = X;  by -TNI14; is TIempD2;   // is Staut;
! TDIn1 := B <: A & a in B & b in A & b nin B -> B--{a} <: A--{a,b};   ///
! TDD := (A--B)--C = A--(B\/C);               is Staut;  // (a & ~b)& ~c == a & ~(b or c) 
! TDNI := B /\ (A--B) = {};                   is Staut;  // B NI (A--B)
! TDIU := (A--B)/\(A--C) = A--(B\/C);         is Staut;  // AxD := a in X -- Y == a in X & a nin Y; line 50
! TninD := a nin X--{a};                      by TninDin, TinS; is Taut(p or true);
! TDneq := a in X--{b} -> a ~= b;             by AxD,TninS; is Taut(p & q ->q);

! TDinS := a in X1 -> X1--{a} ~= X1;
 Proof TDinS;                                 //  AxextA := X = Y == All(x, x in X == x in Y);
F0 := a in X1;                                assume;
F01 := X1--{a} = X1;                          assume; by AxextA;
F02 := All(z, z in X1--{a} == z in X1);       by AxD;
F03 := All(z, z in X1 & z nin {a} == z in X1);
F1 := a in X1 & a nin {a} == a in X1;         is F03(a); by TninS1;   // TninS1 := a nin {a} == false;
F2 := a in X1 & false == a in X1;             by Taut((p & false == q) == ~q); 
F3 := ~(a in X1);                             with F0;
false;
 end Proof TDinS;

! TDSIns := a in X1 -> X1 -- {a} << X1;
 Proof TDSIns;                              // !! AxIns := X << Y == X <: Y & X ~= Y;
F0 := a in X1;                              assume;
Goal := X1 -- {a} << X1;                    by AxIns; F1 & F2;
F1 := X1 -- {a} <: X1;                      is TDIn;
F2 := X1 -- {a} ~= X1;                      is TDinS(F0);
 end Proof TDSIns;

// TD1 := All(A, All(B, All(C, All(D, D <: A -> B/\C <: D == A--D <: A--B \/ A--C)))); not needed, use Rtaut(A);

! TD2 := a1 nin X1--Y1 & a1 nin Y1 -> a1 nin X1;
 Proof TD2;                                   // TninDin := a nin X--Y == a nin X or a in Y;
F0 := a1 nin X1--Y1;                        assume; by TninDin;
F01 := a1 nin X1 or a1 in Y1;               
F02 := a1 nin Y1;                           assume; by Axnin;
F03 := ~(a1 in Y1); 
F04 := a1 nin X1;                           is Taut((p or q) & ~q -> p)(F01 & F03);  
 end Proof TD2;

! TIA := A/\B <: C == All(x, x in A--C -> x nin B);    /// by AxIn; is Staut;
! TNIU0 := A = B\/C & B NI C -> B = A -- C;   is Staut;
! TNIU1 := A NI B -> (A\/B)--A = B;           is Staut;
! TNIU1a := A NI B -> (A\/B)--B = A;          is Staut;                        // line 60
! TNIU2 := A NI B & A1 NI B1 & A\/B = A1\/B1 -> A<:A1 == B1<:B;   /// is Staut;

! TInDUin := X <: Y -> (Goal_TInDUin := a in Y == a in (Y -- X) or a in X); 
 Proof TInDUin;
F0 := X <: Y;                                 assume; by AxIn;
F01 := All(z, z in X -> z in Y);
F02 := a in X -> a in Y;                      is F01(a);
  EqProof -Goal_TInDUin;
F1 := a in (Y -- X) or a in X;                by AxD;
F2 := (a in Y & a nin X) or a in X;           by Axnin;
F3 := (a in Y &(~(a in X))) or a in X;        by Taut(p & ~q or q == p or q);
F4 := a in Y or a in X;                       add F02;    // we can add to a formula P a true formula Q, receiving P&Q, P == P & Q;
F5 := (a in Y or a in X) & (a in X -> a in Y); by Taut((p or q)&(q->p) == p);
F6 := a in Y;
  end EqProof -Goal_TInDUin;
 end Proof TInDUin;

!! Axtp2a := [x1,x2] = [y1,y2] == y1 = x1 & y2 = x2;
!! Axtp2 := [x1,x2] = [y1,y2] == x1 = y1 & x2 = y2;                by Teqvneg, TNand, Axneqr,Axneqr,Axneqr;
! Ttp2N := [x1,x2] ~= [y1,y2] == x1 ~= y1 or x2 ~= y2;
! Ttp2E := All(x,All(a,All(b, Exist(y, [x,y] = [a,b]) == x = a)));                 ///
! Ttp2Ea := All(y,All(a,All(b, Exist(x, [x,y] = [a,b]) == y = b)));                ///

! Ttp2a := [x,y] = [x,z] == y = z;                                 by Axtp2,Axrefl1; is Taut;

// !! Axtp3 := (x1,x2,x3) = (y1,y2,y3) == x1=y1 & x2=y2 & x3=y3;     
// Ttp3a := (x1,x2,x3) = (y1,y2,y3) == (x2,x1,x3) = (y2,y1,y3);     ///
// and so on

!! Axdp := z in X # Y == Exist(z1,Exist(z2, z = [z1,z2] & (z1 in X & z2 in Y)));
// !! Axdp := z in X # Y == E[dxy, z = [x,y] & (x in X & y in Y)];     // dxy := {x,y; true};

!! Tdp := X2 # Y2 = {x,y ; x in X2 & y in Y2} ; //  by AxextA, Axdp, Axab2; is Taut(All(x,p == p));

// Tx1 := All(z, z in X # Y == z in {x,y ; x in X & y in Y});        by Axdp, Axab;
// Tx2 := All(z, Exist(z1,Exist(z2, z = [z1,z2] & (z1 in X & z2 in Y))) == 
//           Exist(z1,Exist(z2, z = [z1,z2] & (z1 in X & z2 in Y)))) ;  is Taut(All(x,p == p));

!! Tindp := All(x,All(y,All(X,All(Y, [x,y] in X # Y == x in X & y in Y))));                     //        by Axdp;
/* EqProof Tindp;
assume(x); assume(y); assume(X); assume(Y);
F1 := [x,y] in X # Y;                                              by Axdp;
F2 := Exist(z1,Exist(z2, [x,y] = [z1,z2] & (z1 in X & z2 in Y)));  by Axtp2a;
F3 := Exist(z1,Exist(z2, (z1=x & z2=y) & (z1 in X & z2 in Y)));    by Taut((p&p1)&(p2&p3) == (p1&p3) & (p&p2));
F4 := Exist(z1,Exist(z2, (z2=y & z2 in Y) & (z1=x & z1 in X) ));   by HB10b;   
F5 := Exist(z1, (z1=x & z1 in X) & Exist(z2, z2=y & z2 in Y ));    by TExisteq;
F6 := Exist(z1, (z1=x & z1 in X) & y in Y);                        by Taut((p&q)&r == p&(q&r));
F7 := Exist(z1, z1=x & (z1 in X & y in Y));                        by TExisteq;
F8 := x in X & y in Y;
 end EqProof Tindp;
*/
! Tindp1 := A1#A2 <: C == A[x1:A1,x2:A2, [x1,x2] in C];            // {x1,x2; x1 in A1, x2 in A2}

begin("Tdp0");

! Tdp0 := X#Y <: X1#Y1 == All(x,All(y, x in X & y in Y -> x in X1 & y in Y1));  
 Proof Tdp0;                                                       by Deqv; L1 & L2;
L1 := X#Y <: X1#Y1 -> All(x,All(y, x in X & y in Y -> x in X1 & y in Y1));
  Proof L1;
F0 := X#Y <: X1#Y1;                                                assume;
G1 := All(x,All(y, x in X & y in Y -> x in X1 & y in Y1));
   Proof G1;  assume(x); assume(y);                                // TinIn := x in X & X <: Y -> x in Y;
K0 := x in X;                                                      assume;
K01 := y in Y;                                                     assume;
K02 := [x,y] in X#Y;                                               by Tindp; K0 & K01; // Tindp := [x,y] in X # Y == x in X & y in Y; 
K1 := [x,y] in X1#Y1;                                              is TinIn(K02 & F0); by Tindp;      //   is F0 ! K02; 
K2 := x in X1 & y in Y1;
   end Proof G1;
  end Proof L1;

L2 := All(x,All(y, x in X & y in Y -> x in X1 & y in Y1)) -> X#Y <: X1#Y1;
  Proof L2;
K00 := All(x,All(y, x in X & y in Y -> x in X1 & y in Y1));         assume;
Goal := X#Y <: X1#Y1;                                               by AxIn;
G0 := All(z, z in X#Y -> z in X1#Y1);
   Proof G0;  assume(z);
M0 := z in X#Y;                                                     assume; by Axdp;
M1 := Existx(u,Existx(v,(_M1a := z = [u,v]) & ( _M1b := (u in X & v in Y)) ));
M2 := u in X & v in Y -> u in X1 & v in Y1;                         is K00(u,v);
Goal := z in X1#Y1;                                                 by _M1a;
G2 := [u,v] in X1#Y1;                                               by Tindp;    // Tindp := [x,y] in X # Y == x in X & y in Y;
G3 := u in X1 & v in Y1;                                            is M2(_M1b); // K00(u,v)(_M1b);
   end Proof G0;
  end Proof L2;
 end Proof Tdp0;

! Tdp1 := X#Y <: X1#Y1 == (Y~={} -> X <: X1) & (X~={} -> Y <: Y1);  // HB16a := All(x, P(x) -> Q) == Exist(x, P(x)) -> Q;
 EqProof Tdp1;                                                      // HB13 := All(x, All(y, P(x,y))) == All(y, All(x, P(x,y))); 
F1 := X#Y <: X1#Y1;                                                 by Tdp0;
F2 := All(x,All(y, x in X & y in Y -> x in X1 & y in Y1));          by Taut((p->q&r)==(p->q)&(p->r)); 
F3 := All(x,All(y, (x in X & y in Y -> x in X1) & (x in X & y in Y -> y in Y1)));             by TAllconj,TAllconj;
F4 := All(x,All(y, x in X & y in Y -> x in X1)) & All(x,All(y, x in X & y in Y -> y in Y1));  by Taut25a,Taut25;
F5 := All(x,All(y, y in Y -> (x in X -> x in X1))) & All(x,All(y, x in X -> (y in Y -> y in Y1)));  by HB16a,HB13,HB16a;
// F5a := All(x,Exist(y, y in Y) -> (x in X -> x in X1)) & All(x,All(y, x in X -> (y in Y -> y in Y1)));  by HB13; 
// F5b := All(x,Exist(y, y in Y) -> (x in X -> x in X1)) & All(y,All(x, x in X -> (y in Y -> y in Y1)));  by HB16a;
F6 := All(x, Exist(y, y in Y) -> (x in X -> x in X1)) &  All(y,Exist(x, x in X) -> (y in Y -> y in Y1)); by HB4,HB4;
F7 := (Exist(y,y in Y) -> All(x,x in X -> x in X1)) & (Exist(x,x in X) -> All(y,y in Y -> y in Y1)); by -TinnempE,-AxIn,-TinnempE,-AxIn;
F8 := (Y ~= {} -> X <: X1) & (X ~= {} -> Y <: Y1);
 end EqProof Tdp1;

! Tdp2 := X~={} & Y~={} -> (X#Y <: X1#Y1 == X <: X1 & Y <: Y1);            // was EqProofC(Tdp2;...
 Proof Tdp2;
F0 := X ~= {};                                                         assume;
F01 := Y ~= {};                                                        assume;
Goal := X#Y <: X1#Y1 == X <: X1 & Y <: Y1;
  EqProof Goal;
F1 := X#Y <: X1#Y1;                                                    by Tdp1;
F2 := (Y~={} -> X <: X1) & (X~={} -> Y <: Y1);                         by F01, F0;
F3 := (true -> X <: X1) & (true -> Y <: Y1);                           by Taut26, Taut26;
F4 := X <: X1 & Y <: Y1;
  end EqProof Goal;
 end Proof Tdp2;

! Tdp2AB := A~={} & B~={} -> (A#B <: A1#B1 == A <: A1 & B <: B1);     is Tdp2;

! Tdpeq := X~={} & Y~={} & X1 ~= {} & Y1 ~= {} -> (X#Y = X1#Y1 == X = X1 & Y = Y1);
 Proof Tdpeq;   // here was ERROR: adds: x in y, x= X y=X#Y
F0 := X ~= {};                                                assume;
F01 := Y ~= {};                                               assume;
F02 := X1 ~= {};                                              assume;
F03 := Y1 ~= {};                                              assume;
Tdp2a := X#Y <: X1#Y1 == X <: X1 & Y <: Y1;                   is Tdp2(F0 & F01);
Tdp2b := X1#Y1 <: X#Y == X1 <: X & Y1 <: Y;                   is Tdp2AB(F02 & F03);
Goal := X#Y = X1#Y1 == X = X1 & Y = Y1;
  EqProof Goal;
F1 := X#Y = X1#Y1;                                            by AxextAB;     // ! AxextAB := A=B == A <: B & B <: A;
F2 := X#Y <: X1#Y1 & X1#Y1 <: X#Y;                            by Tdp2a;       // Tdp2a := X#Y <: X1#Y1 == X <: X1 & Y <: Y1;            
F3 := (X <: X1 & Y <: Y1) & (X1#Y1 <: X#Y);                   by Tdp2b;       // Tdp2b := X1#Y1 <: X#Y == X1 <: X & Y1 <: Y;  
F4 := (X <: X1 & Y <: Y1) & (X1 <: X & Y1 <: Y);              by Taut((p&p1)&(p2&p3) == (p&p2)&(p1&p3));
F5 := (X <: X1 & X1 <: X) & (Y <: Y1 & Y1 <: Y);              by -AxextAB; // second -AxextAB is not needed, because isbe !!!
F6 := X = X1 & Y = Y1;
  end EqProof Goal;
 end Proof Tdpeq;

! Tdpm1 := A1 <: A -> A1 # B <: A # B;
 Proof Tdpm1;
F0 := A1 <: A;                                                assume;
F1 := A1 # B <: A # B;                                        by Tdp1;            // Tdp1 := X#Y <: X1#Y1 == (Y~={} -> X <: X1) & (X~={} -> Y <: Y1);
F2 := (B~={} -> A1 <: A) & (A1~={} -> B <: B);                by F0, TInrefl;     // ! TInrefl := X <: X; 
F3 := (B~={} -> true) & (A1 ~= {} -> true);                   by Taut26b,Taut26b; is Taut;  // ! Taut26b := (p->true) == true;
 end Proof Tdpm1;

! Tdpm2 := B1 <: B -> A # B1 <: A # B;                       // ??? X ~= {}
 Proof Tdpm2;
F0 := B1 <: B;                                                assume;
F1 := A # B1 <: A # B;                                        by Tdp1;
F2 := (B1~={} -> A <: A) & (A~={} -> B1 <: B);                by TInrefl, F0;
F3 := (B1~={} -> true) & (A~={} -> true);                     is Taut;        // by Taut26b,Taut26b; is Taut;
 end Proof Tdpm2;

dcl[dp3,set,set,set,set]; 

!! Axdp3 := z in dp3(X,Y,Z) == Exist(z1,Exist(z2,Exist(z3, z = [z1,z2,z3] & (z1 in X & z2 in Y & z3 in Z)))); 

! Tdp3 := dp3(X1,Y1,Z1) = {x,y,z ; x in X1 & y in Y1 & z in Z1};  by AxextA, Axdp3, Axab; is Taut(All(x,p == p));

! Tdp3a := a in A & b in B & c in C -> [a,b,c] in dp3(A,B,C);   
 Proof Tdp3a;
F0 := a in A;                                                          assume;
F01 := b in B;                                                         assume;
F02 := c in C;                                                         assume;
Goal := [a,b,c] in dp3(A,B,C);                                         by Tdp3;
G0 := [a,b,c] in {x,y,z ; x in A & y in B & z in C};                   by Axab; F0 & F01 & F02;
 end Proof Tdp3a;

!! Tdp4 := A<:B -> A#A <: B#B; 

// ! AxextA2 := X = Y == All(z1, z2, (z1,z2) in X == (z1,z2) in Y);       // not used, wrong

// dp3(X,Y,Z: class) := {pr1:X, pr2:Y, pr3:Z};

//   ------------------------------------------------------ 15 Restricted Quantification

// Another(better) solution: A[{x,y; P(x,y)},Q(x,y)] denotes All(x,All(y, P(x,y) -> Q(x,y)));

!! AxA := A[d, Q] == All(x, x in d -> Rep(d,Q,x) );        // A[d::P:bool] := A[z, z in d -> P(z)]; // was Q1 2.9.20
!! AxAimp := A[x:X, Q(x)] == All(x, x in X -> Q(x));       // was TAimp                  // TAlleq := All(x, x=K -> Q(x)) == Q(K);
! TAeq1 := A[x:A, x=a -> P(x)] == (a in A -> P(a));          byeq AxAimp, Taut27, TAlleq;  // Taut27 := p->(q->r) == q->(p->r);
!! TAeqvcon := B ~= {} -> A[x:B, P(x) == R] == (A[x:B, P(x)] == R);
! TAA1 := A[d,Q] == A[x:d, Rep(d,Q,x)];                    byeq AxA, -AxAimp;  // was P1, changed to Q 2.9.20
!! TAAN := A[x:B, P(x)== Q(x)] == A[x:B, ~P(x) == ~Q(x)];
!! AxE := E[d, Q] == Exist(x, x in d & Rep(d,Q,x) );
!! AxEconj := E[x:B, Q(x)] == Exist(x, x in B & Q(x));                  // by Teqvsym;
! TEeq1 := E[x:A, x=a & P(x)] == a in A & P(a);              byeq AxEconj, Taut28, TExisteq;
! TEE1 := E[d,Q] == E[x:d, Rep(d,Q,x)];                      byeq AxE, -AxEconj;   // !! AxEconj := E[x:B, Q(x)] == Exist(x, x in B & Q(x));
! TEab1 := {x; x in A & Q(x)} ~= {} == E[x:A, Q(x)];         byeq TinnempE, Axab, -AxEconj; by Teqvsym; // ! TinnempE := X ~= {} == Exist(x, x in X);
! TEab := E[x:A, Q(x)] == {x; x in A & Q(x)} ~= {};        
! TES := E[x: {a}, Q(x)] == Q(a);                            byeq AxEconj,Axcoll1,TExisteq;   


// ! TAE := d ~= {} -> (A[d, P] -> E[d,P]);                                  /// HB1
! TNA := ~A[d, P] == E[d, ~P];                                               /// HB2
 EqProof TNA;
F1 := ~A[d,P];                              by AxA;         // !! AxA := A[d, Q] == All(x, x in d -> Rep(d,Q,x) ); 
F2 := ~All(z, z in d -> Rep(d,P,z) );       by TNAll;       // TNAll := ~(All(x, Q(x))) == Exist(x, ~(Q(x)));
F3 := Exist(z, ~(z in d -> Rep(d,P,z)) );   by Taut(~(p->q) == p & ~q);
F4 := Exist(z, z in d & ~Rep(d,P,z) );      by -AxRepN;    //  AxRepN := Rep(d,~P,zd) == ~Rep(d,P,zd);
F5 := Exist(z, z in d & Rep(d,~P,z) );      by -AxE;
F6 := E[d, ~P];
 end EqProof TNA;

! TNAN := ~A[d, ~p] == E[d, p];             byeq TNA, TNN;                 // HB3  if P then overflow of st
! TNE := ~E[d, q] == A[d, ~q];              byeq -TNAN,TNN;                // HB3p
! TNEN := ~E[d, ~p] == A[d, p];             byeq TNE,TNN;                  // HB2p

! TfreeAimp1 := free(d, p1) -> (A[d, p1->q2] == (p1 -> A[d, q2]));                /// HB4 //   == is stronger than ->
 EqProof TfreeAimp1;
F0 := free(d, p1);                                                       assume;  // d,P are constants below;
// F01 := A[z:d, Rep(d,P,z) == P];                                        //A[z:d, Rep(d,P,z) == P]
F1 := A[d, p1->q2];                                                      by AxA;
F2 := All(z, z in d -> Rep(d,p1->q2,z));                                 by AxRepimp; // AxRepimp := Rep(d,P->Q,zd) == (Rep(d,P,zd) -> Rep(d,Q,zd));
F3 := All(z, z in d -> (Rep(d,p1,z) -> Rep(d,q2,z)));                    by AxRepfree(F0); // AxRepfree := free(d, P) -> (Rep(d,P,zd) == P);
F4 := All(z, z in d -> (p1 -> Rep(d,q2,z)));                             by Taut((p->(q->r)) == (q->(p->r)));
F5 := All(z, p1->(z in d -> Rep(d,q2,z)));                               by HB4; //  HB4 :=  All(x, Q -> P(x)) == Q -> All(x, P(x));
F6 := p1 -> All(z, z in d -> Rep(d,q2,z));                               by -AxA;
F7 := p1 -> A[d, q2];                                                    // 
 end EqProof TfreeAimp1;


!! TfreeAor := free(d, P) & d ~= {} -> A[d, P or Q] == P or A[d, Q];        /// HB5 
!! TfreeA1 := free(d, P) -> A[d, P] == P or d = {};                         /// HB4a1
!! TfreeA := free(d, P) & d ~= {} -> A[d, P] == P;                          /// HB4a
!! TfreeAconj := free(d, P) & d ~= {} -> A[d, P & Q] == P & A[d, Q];        /// HB6
!! TAconj := A[d, P & Q] == A[d, P] & A[d, Q];                              /// HB7 TAllconj
!! TAconj1 := A[x:A, P(x) & Q(x)] == A[x:A, P(x)] & A[x:A, Q(x)];           /// HB7 TAllconj
!! TEor := E[d, P or Q] == E[d, P] or E[d, Q];                              /// HB9
!! TfreeE1 := free(d, P) -> E[d, P] == P & d ~= {};                         ///
!! TfreeE := free(d, P) & d ~= {} -> E[d, P] == P;                          ///
!! TfreeEor := free(d, P) & d ~= {} -> E[d, P or Q] == P or E[d, Q];        /// HB8
!! TfreeEor1 := free(d, Q) & d ~= {} -> E[d, P or Q] == E[d, P] or Q;       /// HB8a
!! TfreeEand := free(d, P) -> E[d, P & Q] == P & E[d, Q];                   /// HB10
!! TfreeEand1 := free(d, Q) -> E[d, P & Q] == E[d, P] & Q;                  /// HB10

!! TAimp1 := A[d, P -> Q] -> (A[d, P] -> A[d, Q]);                          /// HB11
!! TAimpE := A[d, P -> Q] -> (E[d, P] -> E[d, Q]);                          // HB12
!! TAor := A[d, P or Q] -> E[d,P] or A[d, Q];                               /// because it follows from well-formedness of the both
!! TAA := A[d1, A[d2, P]] == A[d2, A[d1, P]];                               /// HB13    // removed free(d1, d2) -> 10.3.20 formulas;
!! TEE := E[d1, E[d2, P]] == E[d2, E[d1, P]];                               /// HB13p   // removed free(d1, d2) -> 10.3.20;
!! TfreeAimp2 := free(d, Q) -> (A[d, P->Q] == E[d, P] -> Q);                /// HB16a
!! TfreeEimp := free(d, Q) & d ~= {} -> (E[d, P->Q] == A[d, P] -> Q);       /// HB16b
!! TAeqvA := A[d, P == Q] -> (A[d, P] == A[d, Q]);                          /// HB17a
!! TAeqvE := A[d, P == Q] -> (E[d, P] == E[d, Q]);                          /// HB17b
// ! TAconj1 := A[d, P & Q] -> A[d,P];
// ! TAconj2 := A[d, P & Q] -> A[d,Q];
!! TEA := free(d1,d2) & d1 ~= {} -> E[d1, A[d2, P]] -> A[d2, E[d1, P]];     /// HB18                      
// ! HB18 := Exist(x, All(y, P)) -> All(y, Exist(x, P));
// ! HB19 := All(x, Q->R) -> (All(x,P->Q) -> All(x, P->R));
// ! HB20 := All(x, Q->R) -> (Exist(x, P&Q) -> Exist(x, P&R));
!! TAdeqIn := A[d, A = B ] -> A[d, A <: B];
!! TAdeqAA := A[d, A=B] == A[d, A<:B] & A[d, B<:A];
!! TAdd1AA := A[d&&d1, P] == A[d,A[d1,P]];
!! TAin := A[x:A, x in A];                                                  ///
!! TninA := x nin A == A[a:A, a ~= x];                                      ///
!! TinEeq := x in A == E[a:A, a = x];                                       // is TninA ! Teqvneg ! TNA;
!! TInA := A <: B == A[x:A, x in B];                                        ///
!! TAIn := d1 <: d2 -> (A[d2, P] -> A[d1, P]);                              ///                           
!! TInAall := All(A, All(B, A <: B == A[x:A, x in B]));
!! TAIn1 := A <: B & A[x:B, P(x)] -> A[x:A, P(x)];                          ///
!! TAIn2 := A <: B & A[x,y:B, P(x,y)] -> A[x,y:A, P(x,y)];                  ///
!! TInAA := A <: B & A[x:B, P(x)] -> A[x:A, P(x)];                          // is TAIn1 ! Taut((p->(q->r)) == (p&q ->r));
!! TInAA2 := A <: B & A[x1,x2:B, P(x1,x2)] -> A[x1,x2:A, P(x1,x2)]; 
!! TInAA3 := A <: B & A[x1,x2,x3:B, P(x1,x2,x3)] -> A[x1,x2,x3:A, P(x1,x2,x3)]; 
!! TEIn := d1 <: d2 -> (E[d1, P] -> E[d2, P]);                              ///
!! TInEE := A <: B & E[x:A, P] -> E[x:B, P];                                ///    
// ! TAsc(d::P) := A[d, P] == (d && P) = d;                                   ///
// ! TEscemp := E[d, P] == (d && P) ~= {};                                    ///
!! TEtrue := E[d, true] == d ~= {};                                        // byeq TEsc, Tsctrue;         
!! TEfalse := E[d, false] == false;                                        // byeq TEsc, Tscfalse, Taut(x ~= x == false);
!! TEemp := E[{}, P] == false;                                             //  byeq TEsc, Tscemp, Taut(x ~= x == false);
!! TAtrue := A[d, true] == true;                                           //  byeq TAsc, Tsctrue, Axrefl;
!! TAfalse := A[d, false] == d = {} ;                                      // byeq TAsc, Tscfalse;
// A[d, false] == ~E[d];
!! TAemp := A[{}, P];                                                       // byeq TAsc, Tscemp, Axrefl;             
!! TAemp1 := A[x:{}, P(x)];                                                    // by TAimp; Taut;
!! TAemp1a := A[x:{}, P(x)] == true;                             // move to root !!!
!! TAemp2a := A[x,y:{}, P(x,y)] == true; 
!! TAllA := free(d,x) -> All(x, A[d, P]) == A[d, All(x, P)];          ///
!! TExistE := free(d, x) -> Exist(x, E[d, P] ) == E[d, Exist(x, P) ];       ///
// ! TEconj := E[x:B, P] == Exist(x, x in B & P);
!! TIAr := A/\B <: C == A[x:A--C, x nin B];                                  ///
// ! TEdp := E[x:A#B, P(x)] == E[{x1:A,x2:B | P(x1,x2)];                      ///
// ! AxErE2 := E[x:A, y:B, P(x,y)] == E[x:A, E[y:B, P(x,y)]];
// ! TErE2 := E[x:A, y:B, P(x,y)] == E[x,y, x in A & y in B & P(x,y)];        ///
// ! TEdp0 :=  E[{x1:A,x2:B | P(x1,x2)}] == E[x1:A, x2:B, P(x1,x2)];          ///
// ! TEdp1 := E[x:A#B, P(x)] == E[x1:A,x2:B,  P(x1,x2)];                     // byeq TEdp, TEdp0;
// ! TEdp2 :=  E[x:A, y:B, P(x,y)] == E[{x:A, y:B}, P(x,y];                   /// 
// ! TAdp := A[x:A#B, P(x)] == A[{x1:A,x2:B | P(x1,x2)}];                  // not used
// ! TAdp1 := A[x:A#B, P(x)] == A[x1:A,x2:B, P(x1,x2)];                       ///
!! TarbE := E[y:B, P(y)] -> arb({y; y in B & P(y)}) in B & P(arb({y; y in B & P(y)}));     ///
!! TEeq := A[a:A, E[x:A, x=a & P(x)] == P(a)];                              ///
!! TAeq := A[a:A, A[x:A, x=a -> P(x)] == P(a)];                             ///
// ! TEAEA := E[x:d, P(x) & A[x1:d, P(x1) -> x=x1]] == E[d, P] & A[x1,x2:d, P(x1) & P(x2) -> x1=x2]; // not used
!! TEUEE := E[x: A\/B, P] == E[x:A, P] or E[x:B, P];                        ///
!! TAab := {z; z in t & P} = t == A[z:t, P];                                    //  by TAimp; TabeqA;                          
!! TAab0 := A[x: {x; x in t & P(x)}, x in t & P(x)];                                 ///
!! TAab1 := A[x: {x; x in t & P(x)}, P(x)];                                      //    is TAab;
!! TAab2 := A[z:t, z in {x; x in t & P(x)} == P(z)];                            ///
!! TAabimp := A[{x; x in t & P(x)}, Q(x)] == A[x:t, P(x) -> Q(x)];                ///
// ! TAscin := A[z:d, z in d&&P == P(z)];             by TAimp; Taut(q -> (q&p == p));  // z in d&&P == z in d & P(z); 
// ! TAscAimp := A[d&&P, Q] == A[d, P -> Q];                                  ///
// ! TAscAimp1 := A[z: d&&P, Q(z)] == A[z:d, P(z)->Q(z)];    byeq TAimp, Tscin, Taut((p&q->r)==(p->(q->r)), -TAimp;
// ! TAscIn1 := A[d, P -> Q] == d&&P <: d&&Q;                                 /// was TscIn1;
// ! TAscIn3 := A[d&&p,q] == d&&p <: d&&q;                                    by TAsc; TAscIn1;
// ! Tsceqv := d && P = d && Q == A[d, P==Q];                                 ???
!! TAinIn := A[d, g in A] & A<:B -> A[d, g in B];                           ///
!! TAInin := A[z:A, z <: B] == A[z:A, A[x:z, x in B]];                      //    byeq TInA, AxA2;
!! TAS := A[x: {a}, P(x)] == P(a);       // by TAimp; TAlleq; ??? x is local ???
!! TAS2 := A[x: {a,b}, P(x)] == P(a) & P(b);                                ///
!! TAS2a := A[x,y: {a}, P(x,y)] == P(a,a);
!! TES2 := E[x: {a,b}, P(x)] == P(a) or P(b);                              //  by TNE; TAS2;
!! TAInAA:= A[x:A, P] == All(B, B<:A -> A[x:B, P]);                        ///
!! TAcoll2 := A[x:t, x=a or x=b] == t <: {a,b};                            ///
!! TAInab := {x; x in t & P(x)} <: {x; x in t & Q} == A[x:t, P -> Q];                      ///
!! TAabnin := A[z:t, z nin {x; x in t & Q(x)} == ~Q(z)];                          ///
// ! AxE2:= E[x:A,y:B, P] == E[x:A, E[y:B, P]];                        // see TE2a
// ! AxA2, TA2a, TA2 := A[x:B1,y:B2, Q] == A[x:B1, A[y:B2, Q]];        // TA2a, TA2
// ! AxA2a := A[x,y:B, Q] == A[x:B, A[y:B, Q];
// ! AxA3 := A[x:B1,y:B2, z:B3, Q] == A[x:B1, A[y:B2, A[z:B3, Q]]];
// ! TAr3 := A[x:B1, A[y:B2, A[z:B3, Q]]] == 
//          A[x,x in B1 -> A[y,y in B2 -> A[z,z in B3 -> Q]]];               byeq -AxAd,-AxAd,-AxAd;
// ! TAr3z := A[x:B1,y:B2, z:B3, Q] == A[x,x in B1 -> A[y,y in B2 -> A[z,z in B3 -> Q]]]; is AxA3 ! TAr3;
// ! AxA3a := A[x,y,z:B, Q] == A[x:B, A[y:B, A[z:B, Q]];
// ! TA2b := A[x:B1,y:B2, Q] == A[y:B2, A[x:B1, Q]];                          ///
// ! TA3c,TA3_12 := A[x,y,z:B, Q] == A[z:B, A[x,y:B, Q]];                     -byeq AxA2a, -Ax3a; ///
// ! TA12_3a := A[x,y,z:B, Q] = A[x,y:B, A[z:B, Q]];                          ///         
// ! TA23_1a := A[x,y,z:B, Q] = A[y,z:B, A[x:B, Q]];                          ///
!! TA1_23 := A[x1:A1,x2:A2,x3:A3, Q(x1,x2,x3)] = A[x1:A1, A[x2:A2, x3:A3, Q(x1,x2,x3)]];        ///
!! AxextA1 := A <: t & B <: t -> A=B == A[x:t, x in A == x in B];           ///
!! Tabeq := {x; x in t & Q1(x) } = {x; x in t & Q2(x)} == A[x:t, Q1(x) == Q2(x)];       ///
!! TAU := A[x:A, Q(x)] & A[x:B, Q(x)] == A[x: A\/B, Q(x)];                    ///
!! TAI := A[x:A, Q(x)] & A[x:B, Q(x)] -> A[x: A/\B, Q(x)];                    /// 
!! TAeqimp := A[x,y:A, G(x)=G(y) -> x=y] -> A[x,y:A, G(x)=G(y) == x=y];           
!! TEin := z in X == E[x:X, z=x];                                           // -byeq TEconj, TExisteq; 
!! TEelim1 := E[x:A, x=f & P(x)] == P(f) & f in A; 
!! TEelim2 := E[x:A, P(x) & x=f] == P(f) & f in A; 
!! TEelim3 := E[x:A, P(x) & f=x] == P(f) & f in A;
!! TAnin := z nin X == A[x:X, x ~= z];                                      // is TEin ! Teqvneg ! TNE;
!! TAemp2 := A[x,y:{}, P(x,y)];                                                  // by AxA2a; TAemp1;
!! TAA2 := A[x:t,x1:t1, P(x,x1)] == A[x:t, A[x1:t1, P(x,x1)]];
!! TAA3 := A[x:t,x1:t1,x2:t2, P(x,x1,x2)] == A[x:t, A[x1:t1,x2:t2, P(x,x1,x2)]];
!! TEE2 := E[x:t,x1:t1, P(x,x1)] == E[x:t, E[x1:t1, P(x,x1)]];
!! TEE2c := E[x:t,x1:t1, P(x,x1)] == E[x1:t1,x:t, P(x,x1)];
// ! TAimp2 := A[x:t1, y:t2, Q] == A[x,y, x in t1 & y in t2 -> Q];            ///
// ! TAimp2a := A[x,y:t, Q] == A[x,y, x in t & y in t -> Q];                  /// // is AxArA
// ! TAcoll3 := A[A1,A2: {B1,B2,B3}, Q(A1,A2)] == Q(B1,B1) & Q(B1,B2) & Q(B1,B3) & //---
//                                               Q(B2,B1) & Q(B2,B2) & Q(B2,B3) &
//                                               Q(B1,B1) & Q(B1,B2) & Q(B1,B3);
// ! TAcoll3a := A[A1,A2: {B1,B2,B3}, A1 ~= A2 -> Q(A1,A2)] == Q(B1,B2) & Q(B1,B3) & Q(B2,B3) & //---
                                                            Q(B2,B1) & Q(B3,B1) & Q(B3,B2);
// ! TAcoll3b := symm(Q) -> A[A1,A2: {B1,B2,B3}, A1 ~= A2 -> Q(A1,A2)] == Q(B1,B2) & Q(B1,B3) & Q(B2,B3); //---
// ! TESEE := E[X1,X2: B, a in X1 & b in X2] == E[X:B, {a,b} <: X] or E[X1,X2: B, X1 ~= X2 & a in X1 & b in X2]; ///

// ------------------------------------------Exist1(x, P(x) )
// !! AxE1v := E1[x,P(x)] == E1[{x | P(x)];                             
// ! TE1v := E1[x,P(x)] == E[x,P(x)] & M1[x,P(x)];                      by AxE1v,AxEv,AxM1v; AxE1cls;
// ! TE1M1a := E1[x,P(x)] -> M1[x,P(x)];                                by AxE1v, AxM1v; TE1M1;       
!! AxExist1 := Exist1(x, P(x)) == Exist(x,P(x)) & All(x1,All(x2, P(x1) & P(x2)));
!! TE1eq := All(y,All(y1, Exist1(x,P(x)) & P(y) & P(y1) -> y=y1));     // is TE1in ! AxE1v ! Axab; by Taut; 
!! TE1AN := All(x1,All(x2, P(x1) & P(x2) & x1~=x2 -> ~Exist1(x,P(x)) ));
// ! TE1v1 := E1[x, x=a];                                              // by AxE1v,TSab; TE1S1;
// ! TE1ES := E1[X] == E[a, X = {a}];                                  ///
!! TE1pair1 := All(a,All(b, Exist1(y, [y,b] = [a,b])));                 ///
!! TE1pair1a := All(a,All(b, Exist1(y, [a,y] = [a,b])));                ///
!! TE1pair2 := All(a,All(b,All(b1, Exist1(y, [a,y] in {[a,b], [a,b1]}) == b=b1)));   ///
!! TE1pair3 := a ~= a1 -> Exist1(y,[a,y] in {[a,b], [a1,b1]});           ///
!! TE1pair3a := a ~= a1 -> Exist1(y,[a1,y] in {[a,b], [a1,b1]});         ///
!! TExist1 := Exist1(x,P(x)) & P(z) & P(z1) -> z = z1;
!! TExist1a := A[x:A, E1[y:B, P(x,y)]] -> Exist1(f, f in fn(A,B) & A[x:A, P(x,f(x))]);
// ! TE1v := E1[X] == E[x, x in X] & A[x,y:X, x=y];                     byeq TE1A2, TEEv;
// ! TE1v2 := E1[X] == E1[x, x in X];                                   byeq Tabin, -AxE1v;
// ! TE1I := E1[X/\Y] == E1[c, c in X & c in Y];                        byeq TE1v2, TinI;

// -----------------E1[d,P]              // P(x) means Sb(P,d,x),  P(x1) means Sb(P,d,x1)  
// dcl[E1[ : (d:open, P:bool, bool); AxE1d := E1[d, P] == E1[d&&P]];
!! TE1d := E1[d, P] == E[d,P] & A[x1:d, A[x2:d, Rep(d,P,x1) & Rep(d,P,x2) -> x1=x2]];  // TE1d byeq AxE1d, AxE1c, AxEd,TM1scA; 
!! TE1d1 := E1[d, P] == E[x:d, Rep(d,P,x) & A[x1:d, Rep(d,P,x1) -> x=x1]];        /// 
!! TE1dE := E1[d, P] -> E[d,P];                                       // is Taut3(TE1d);  // p==q&r -> (p->q); 
!! TE1dA := E1[d,P] -> A[x1:d, A[x2:d, Rep(d,P,x1) & Rep(d,P,x2) -> x1=x2]];           // is Taut3a(TE1d);  // was TE1A; // from TE1d;
!! TE1a := E1[x:A, P(x)] == E[x:A, P(x)] & A[x1,x2:A, P(x1) & P(x2) -> x1=x2]; // is TE1d; // (x:A) = {x | x in A} !!!
// ! TE1ab := E1[{x:X | P}] == E1[x:X, P];                              // byeq AxE1c, TEab, TM1a, TE1a; 
!! TE1c := E1[x:A,Q] ==  E[x:A, Q(x) & A[x1:A, Q(x1) -> x1=x]];       // is TE1d1;
!! TEE1L2 := E[d,P] == E1[d,P] or E[x1:d,E[x2:d, x1 ~= x2 & Rep(d,P,x1) & Rep(d,P,x2)]]; // byeq AxE1d, TEE1NM1, -AxEd, AxM1d, TNM1d;
!! TAorE1 := A[d, P or Q] -> E1[d,P] or E[x1:d,E[x2:d, x1 ~= x2 & P(x1) & P(x2)]] or A[d,Q]; // is TAor ! TEE1L2;
!! TE1ADS := {x; x in A & P(x)} = {x} -> A[z:A--{x}, ~P(z)];                ///
// --------------------------------nemp(X),most1(X),one(X),the(X)-- (previous E[X], M[X],E1[X], T[X])
// dcl[nemp,set,bool];
!! Axnemp := nemp(X) == X ~= {};          // was E[X]

// dcl[most1,set,bool];                      // was M[X]
!! Axmost1 := most1(X) == All(x1,All(x2, x1 in X & x2 in X -> x1 = x2));
!! Tatm1a := most1(X) -> one(X) == ~(X={});
!! Tatm1or := most1(X) -> X={} or one(X);

// dcl[one,set,bool];                        // was E1[X]
!! Axone := one(X) == nemp(X) & most1(X);
!! ToneS := one({x});
!! ToneE := one(X) == E[a:X, X = {a}];

dcl[atl2,fn(set,bool)];   // atl2(X): X has atleast 2 elements; (#X >= 2, but we have to prove that X is a finite set); dcl[atm1, not most1 !!!
!! Axatl2 := atl2(X) == E[a,b:X, a ~= b];
!! Tatl2 := a in X & b in X & a ~= b -> atl2(X);
!! Tatl2a := X ~= {} -> X ~= {a} == atl2(X);
!! Tatl2b := ~(atl2(X) & one(X));
!! Tatl2S :=  atl2(X) -> All(x, X ~= {x});
!! Temp_one_atl2 := X = {} or one(X) or atl2(X);

// dcl[the,set,any];                         // was T[X}
!! Axthe := one(X) -> the(X) = arb(X);
!! Tthe1 := one(X) -> the(X) in X & A[z: X, z = the(X) ];                                    ///
// ! TT1ab := E1[{x:X | P}] -> {x:X | P}] in X & A[z: X, P(z) -> z = T[{x:X | P}] ]; // not used
!! Ttheeq := one(X) -> (z = the(X) == z in X);                                               ///
!! Ttheeqab := one({x; x in X & P(x)}) -> (z = the({x; x in X & P(x)}) == z in X & P(z) );   // is TTeq({x:X | P(x)}) ! Axab;
!! Ttheab1 := one({x; x in X & P(x)}) -> the({x; x in X & P(x)}) in X & P(the({x; x in X & P(x)}));  ///
!! Tthe2 := one(X) -> X = {the(X)};                                                          ///
!! Tthe2a := one(X) -> the(X) in X;              // from TT1; // is Taut((p->q&r)->(p->q)) ! TT1;
! Ttheeq1 := All(A,All(B, one(A) & one(B) -> A=B == the(A) = the(B)));                       ///
dcl[least2,set,bool];                     // was E2[S:set) := E[a,b, a~=b & S = {a,b}];
!! Axleast2 := All(S, Exist(a, Exist(b, a~=b & S = {a,b} )));

// ----------------------------------------union(A)---- union of all sets from A
dcl[union,set,set]; 
!! Axunion := union(A) = {x ; Exist(y, y in A & x in y) };
!! Tunionemp := union({}) = {};                          //  byeq Axunion, TEcolemp, Axemp;
!! Tunionin := x in union(A) == Exist(Y, Y in A & x in Y);
!! TunioninE := x in union(A) == E[y:A, x in y];          //  byeq Axunion, AxAb;
!! TunionU := union(A\/B) = union(A)\/union(B);          ///
!! Tunionm := A <: B -> union(A) <: union(B);            ///
!! TunionmP := A[A:P[B], union(A) <: union(B)];
!! Tunion2a := Z in A & x in Z -> x in union(A);         ///
!! Tunion2 := z in A & B <: z -> B <: union(A);          ///
!! Tunion3 := union(A) <: B == A[z:A, z <: B];           ///
!! Tunion3a := union(A) <: B == A[z:A, A[x:z, x in B]];  // byeq Tunion3,TAInin;
!! Tunion3b := All(A,All(B, union(A) <: B == All(z,All(x, z in A & x in z -> x in B)) )); // byeq Tunion3a,TAimp2;
!! Tunion4 := A[z:A, z <: union(A)]; // is SBV(Tunion3, B, union(A)), TInrefl, Taut((true == p) == p);
!! Tunion5 := X in A -> X <: union(A);                   // is Tunion4 ! TAimp;
// !! AxU := A\/B = union({A,B});
!! Tunion6 := {a,b} <: union(B) == E[X1:B,E[X2:B, a in X1 & b in X2]]; // byeq TIncoll2,Tunionin,HB15b1; by TESEE;
!! Tunion7 := {a,b} <: union(B) == E[X:B, {a,b} <: X] or E[X1:B,E[X2:B,X1 ~= X2 & a in X1 & b in X2]]; //
!! Tunion8 := {a,b} IN union(B) == one({a,b}/\union(B)) or E[X:B, {a,b} <: X] or E[X1:B,E[X2:B,X1 ~= X2 & a in X1 & b in X2]]; ///
!! Tunion9 := {a,b} NI union(B) or one({a,b}/\union(B)) or E[X:B, {a,b} <: X] or E[X1:B,E[X2:B,X1 ~= X2 & a in X1 & b in X2]]; ///
!! Tunion_1 := union({A1}) = A1;                           ///
!! Tunion_2 := union({A1,A2}) = A1\/A2;                    ///
!! Tunion_3 := union({A1,A2,A3}) = A1\/A2\/A2;             ///
!! TunionE1 := one(B) == B = {union(B)};                   /// one(B) was E1[B]
// !! Tprt12 := A[Q:B, union(B)=Q -> B={Q}];                  // wrong: B = { Q, {} }

// ------------------------------------------II(A)---- Intersection of all sets 
// dcl[II,set,set];
!! AxII := A ~= {} -> II(A) = {x ; A[z:A, x in z]};

// ! TII0 := II({}) = set;                                    // byeq AxII, TAbcolemp, Axset; // {z:{}
!! TIIin := A ~= {} ->All(x, x in II(A) == A[z:A, x in z]);   // is AxII; // byeq AxII, AxAb; // TIIin(x, Z)
!! TIIam := A ~= {} & B ~= {} & A <: B -> II(B) <: II(A);     ///
!! TII2 := z in A & z <: B -> II(A) <: B;                     ///
!! TII3 := A <: II(Z) == A[z:Z, A <: z];                      ///  implies, that II({}) = set
!! TII4 := A[z:A, II(A) <: z];                                // is TII3{A := II(A)};
!! TII5 := A ~= {} -> A[z:A, z <: B] -> II(A) <: B;           ///  not used, the same as TII4
!! TII6 := All(B, A[z:A, B <: z] -> B <: II(A));              /// from TII3; // not needed
!! TII7 := II(A) in A -> A[X:A, A[Y:A, X <: Y] -> X = II(A)]; ///

// ---------------------------------------------R[d,f]------ (im(F[d,f]))
!! AxR := R[d, f] = {z ; E[d, z = f]};

// var d::f:any, z: any, B: class, P: formula; 
!! TRin := z in R[d,f] == E[d, z = f];      // byeq AxR, AxAb;                  // was TRE
!! TRin1 := z in R[x:A, G(x)] == Exist(x, x in A & z = G(x));
// ! TRin2 := z in R[(x,y):t, f] == Exist(x, Exist(y, (x,y) in t & z = f(x,y)));  move to REL  ///
!! TRnin := z nin R[d,f] == A[d, z ~= f];   // by Taut((p==q) == (~p == ~q)), TNnin, TNAN; is TRin;
!! TAinR   := A[d, f in R[d,f]];            // by TRin, AxRefl, TEtrue; is TAE; ///
!! TAR  := A[x: R[d, f], Q(x)] == A[d, Q(f) ];                               ///            
!! TRA  := R[d, f] <: B == A[d, f in B];                                     /// was TRI
!! TRAS := R[d, f] <: {a} == A[d, f = a];                                    // byeq TRA, 
!! TRA1 := B <: R[d,f] == A[z:B, E[d, z = f]];                               ///
!! TER   := E[x: R[d,f], P(x)] == E[d, P(f) ];                                ///
!! TRR  := R[x:R[d,f], G(x)] = R[d, G(f)];                                   /// former TRRR
!! TRU := R[x: A\/B,F(x)] = R[x:A, F(x)] \/ R[x:B, F(x)];                    ///
!! TRI := R[x: A/\B,F(x)] = R[x:A, F(x)] /\ R[x:B, F(x)];                    // see TimreI
// ! TabR := {x:R[d,f] | P} = R[d&&P,f];                                       /// was TSR
!! TRS := E[d, f=a] -> R[d,f] = {a} == A[d,f=a];                             ///                                
!! TRcol1 := R[x:{a}, F(x)] = {F(a)};                                        ///
!! TRcol2 := R[x:{a,b}, F(x)] = {F(a),F(b)};                                 //
!! TRmon := A <: B -> R[x:A, G(x)] <: R[x:B, G(x)];                          /// mon: monoton
!! TRx := R[x:d, Rep(d,q,x)] = R[d,q];                                       /// 
!! TRwhole := R[x:S, x] = S;
!! TR1 := A ~= {} -> R[x:A, F(x)] ~= {};                                     // ??? == ???
!! TRset := {z: R[d, F]; P(z)} = R[d && P(F), F]; 
!! TRS1 := X ~= {} -> R[x:X, c] = {c}; 
!! TRinN := ~(a in R[d,g]) == A[d, a ~= g];
!! TRAC1 := X ~= {} -> A[x:X, G(x)=C] == R[x:X, G(x)] = {C};
!! TRAP  := R[d, f] in P[B] == A[d, f in B];  
!! TimFA := im(F[d, f]) <: B == A[d, f in B];           // !! TRA  := R[d, f] <: B == A[d, f in B];
!! TimFin := z in im(F[d,f]) == E[d, z = f];            // from !! TRin := z in R[d,f] == E[d, z = f];

! TR2 := R[a:A,b:B, F(a,b)] = R[b:B,a:A, F(a,b)];          
 Proof TR2;                                                        by AxextA;
F1 := All(z, z in R[a:A,b:B, F(a,b)] == z in R[b:B,a:A, F(a,b)]);  by TRin;
F2 := All(z, E[a:A,b:B, z = F(a,b)] == E[b:B,a:A, z = F(a,b)]);    is TEE2c; // TEE2c := E[x:t,x1:t1, P(x,x1)]==E[x1:t1,x:t, P(x,x1)]];
 end Proof TR2;  

!! TR3 := R[d, [F,G]] in REL;                               //after TR2
!! TR4 := dom(R[d, [F,G]]) = R[d, F];
!! TR5 := im(R[d, [F,G]]) = R[d, G]; 

!! TRE2 := [x,y] in R[z:A, [F(z), G(z)]] == E[a:A, x = F(a) & y = G(a)];

// The syntax "R[(x,y):t, f(x,y)]" means {z | E[x,y, (x,y) in t & z = f(x,y)]}; 
// see also Rp.v! TAllRA  := free(d, P) -> All(x, x in R[d, f] -> P] == A[d, P[x:=f] ];

// ----------------------------------------------U[d,w]----- ( union(R[d,w]) )-------------
//dcl[U[,abterm,set,set];

!! AxUbr := U[d, w] = {z ; E[d, z in w]} ;                    // U bracketed
! TUin := x in U[d, w] == E[d, x in w];                       byeq AxUbr, Axab;       
!! TUA := U[d, w] <: A == A[d, w <: A];                        ///      
!! TUR := U[x:R[d,w], F(x)] = U[d, F(w)];                      ///
!! TEU := E[x:U[d,w], P(x)] = E[d, E[x:w, P(x)]];              ///   
!! TRUU   := R[x:U[d,w], F(x)] = U[d, R[x:w, F(x)]];           /// was TRU
!! TUun := U[S:X, S] = union(X);                               ///
!! TRUn := R[x:union(X), F(x)] = U[S:X, R[x:S, F(x)]];         // byeq TUun; TRUU;
!! TUS := U[x:{a}, F(x)] = F(a);                               ///
!! TUU := U[x:A\/B, F(x)] = U[x:A, F(x)] \/ U[x:B, F(x)];      ///            
!! TUU1 := U[x:B\/{a}, F(x)] =  U[x:B, F(x)] \/ F(a);          ///
!! TUI := U[d,F]/\B = U[d,F/\B];                               // not used, use Axexta;
!! TUNI := U[d, F] NI B == A[d, F NI B];                       // not used, use TUI ??? f(x)
!! TUD1 := A[b:B, U[x:B, F(x)] = U[x:B--{b}, F(x)] \/ F(b)];   ///
!! TUunion := U[d,w] = union(R[d,w]);                          /// 
!! TURin := x in U[d,R[d1,f1]] == E[d,E[d1,x=f1]];             byeq TUin,TRin;  // ! TRin := z in R[d,f] == E[d, z = f];
!! TUUin := z in U[x:U[d1,f1],F(x)] == E[d1,E[x:f1,z in F(x)]]; byeq TUin,TEU;    // ! TUin := x in U[d, w] == E[d, x in w];
// ! TURin1 := x in U[d,R[d1,f1]] == E[d!d1, x=f1]];          // d!d1: not imp. yet; // !! TEU := E[x:U[d,w], P(x)] = E[d, E[x:w, P(x)]]; 
!! TUfree := d~={} & free(d,G) -> U[d, G] = G;
!! TUfree1 := A ~= {} -> U[x:A, G] = G;                        // G without parameters means that G is free from x; 
!! TUIn1 := A[x:A, G(x) <: A] & A[x:A, x in G(x)] -> U[x:A, G(x)] = A;

! TUR1 := U[d,R[d1,f]] = U[d1,R[d,f]];
 Proof TUR1;                                                  by AxextA;     // !! AxextA := X = Y == All(x, x in X == x in Y); 
F1 := All(x, x in U[d,R[d1,f]] == x in U[d1,R[d,f]]);
  EqProof F1;
H0 := assume(x);
H1 := x in U[d,R[d1,f]];                                      by TURin;
H2 := E[d,E[d1,x=f]];                                         by TEE;        // ! TEE := E[d1, E[d2, P]] == E[d2, E[d1, P]];
H3 := E[d1,E[d,x=f]];                                         by -TURin;
H4 := x in U[d1,R[d,f]];
  end EqProof F1;
 end  Proof TUR1;

! TUR2 := U[x:t,R[x1:t1, F(x,x1)]] = R[x:t,x1:t1, F(x,x1)];  
 Proof TUR2;                                                  by AxextA;
F1 := All(z, z in U[x:t,R[x1:t1, F(x,x1)]] == z in R[x:t,x1:t1, F(x,x1)]);
  EqProof F1;
H0 := assume(z);
H1 := z in U[x:t,R[x1:t1, F(x,x1)]];                          by TURin;
H2 := E[x:t,E[x1:t1, z = F(x,x1)]];                           by -TEE2;  // TEE2 := E[x:t,x1:t1, P(x,x1)] == E[x:t, E[x1:t1, P(x,x1)]];
H3 := E[x:t,x1:t1, z = F(x,x1)];                              by -TRin;
H4 := z in R[x:t,x1:t1, F(x,x1)];
  end EqProof F1;
 end Proof TUR2;

// F0 := A[x:{}, x ~= x];           is TAemp1;                   // !! TAemp1 := A[x:{}, P(x)]; 
// F1 := z ~= z;                    is F0;
// ERROR: hnis: Q is not instance of J and J:A[d1,P1] and not Q:A[d,P]), Q= F1#3763 
// J= !1F0#3759 ---------------------OK, the test was successful !!! 12.2.20

! TUA1 := A[x:A, F(x) <: A & x in F(x)] -> U[x:A, F(x)] = A;
 Proof TUA1;                                                  // ! TAconj1 := A[x:A, P(x) & Q(x)] == A[x:A, P(x)] & A[x:A, Q(x)]; /// HB7 TAllconj
F0 := A[x:A, F(x) <: A & x in F(x)];                          assume; by TAconj1; F01 & F02;
F01 := A[x:A, F(x) <: A ];
F02 := A[x:A, x in F(x)];
G0 := U[x:A, F(x)] = A;                                       by Axext;  L1 & L2;
L1 := U[x:A, F(x)] <: A;                                      by TUA; F01;         // ! TUA := U[d, w] <: A == A[d, w <: A];
L2 := A <: U[x:A, F(x)];                                      by TInA;             // ! TInA := A <: B == A[x:A, x in B];
G1 := A[z:A, z in U[x:A, F(x)]];
  Proof G1;
F03 := z in A;                                                assume;
F04 := z in F(z);                                             is F02;              // F02 := A[x:A, x in F(x)];
G2 := z in U[x:A, F(x)];                                      by TUin; // ! TUin := x in U[d, w] == E[d, x in w]; 
G3 := E[x:A, z in F(x)];                                      is Witness(z);
  end Proof G1;
 end Proof TUA1;

!! TUm1 := A <: B -> U[x:A, G(x)] <: U[x:B, G(x)];             // m: monotone
!! TUwhole := U[x:S, {x}] = S;

// ------------------------------------------------if(p,a,b)----if5(p1,a1,p2,a2,a3)------------
dcl[if,bool,any,any, 2];              // check in typ: if(p,a,b): typ(a)= typ(b)
!! Axif1 := if(true,a,b) = a; 
!! Axif2 := if(false,a,b) = b;

!! Tif1 := p -> if(p,a,b) = a;                     ///

!! Tif2 := ~p -> if(p,a,b) = b;                    ///
!! Tif3 := if(p,a,a) = a;                          ///
!! Tif4 := (p -> a=c) -> if(p,a,b) = if(p,c,b);
// ! Tif4 := Q(if(p,a,b)) == p -> Q(a) & ~p -> Q(b); /// is Tautif;
// ! Tif4a := Q(a) & Q(b) -> Q(if(p,a,b));           /// is Tautif;
// ! Tif4b := Q(if(p,a,b)) -> Q(a) or Q(b);          // is Tautif; // checks for p == true,false
!! Tifin2 := if(p,a,b) in X == (p -> a in X) & (~p -> b in X); /// is Tif4;
!! Tifin2a := a in X & b in X -> if(p,a,b) in X;        // is Tif4a;
!! Tifin2b := if(p,a,b) in X -> a in X or b in X;       // is Tif4b;
!! Tifin2in := if(p,a,b) in X == if(p, a in X, b in X); // is Tautif;
!! Tifin2eq := if(p,a,b) = c == if(p, a = c, b = c);    // is Tautif;
!! Tifeq2 := if(p,a,b) = x == (p -> a=x) & (~p -> b=x); // is Tautif; by Taut((p -> q1)&(~p -> q2) == p&q1 or ~p&q2);
!! Tifeq2a := if(p,a,b) = x == (p & a=x) or (~p & b=x);

dcl[if5,bool,any,bool, any,any,any];           // if-terms are embedded ! 
!! Axif5 := if5(p1,a,p2,b,c) = if(p1,a, if(p2,b,c)) ;

!! Tif5in := if5(p1,a1,p2,a2,b) in X == (p1 -> a1 in X) & (p2 -> a2 in X) & (~p1 & ~p2 -> b in X); /// is Tautif;
!! Tif5_1 := p1 -> if5(p1,a1,p2,a2,b) = a1;         // is Tautif;
!! Tif5_2 := p2 -> if5(p1,a1,p2,a2,b) = a2;         // is Tautif;
!! Tif5_3 := ~p1 & ~p2 -> if5(p1,a1,p2,a2,b) = b;   // is Tautif;
!! Tif5_4 := a1 in X & a2 in X & b in X -> if5(p1,a1,p2,a2,b) in X; // by Tifin2; Taut; was Tifin3a

// ! TifP := "P(a1, ..., if(p, a, b), ... , ak) ==  // for the first occurrence of 
//            (p -> P(a1, ...,a, ... ak)) & (~p -> P(a1, ...,b, ... ak))";          // not used

// Tifeq1 := if(P,a,b) = b == P -> a=b; Proof: if(P,a,b) = b == ifl(P,a=b,b=b) == P -> a=b;
// ifl(P,Q,R) := (P->Q)&(~P->R);  ifl(P,Q,true) == P->Q;

// dcl[if2: (bool, any) -> any;   if2(true,a) = a]d;  // not used

// ! Tif1s := p1 -> if(p1,a1, ...) = a1;             // Theorem schemata (s means schemata)
// ! Tif2s := p2 -> if(p1,a1,p2,a2, ...) = a2;       // Theorem schemata
// ! Tif3s := p3 -> if(p1,a1,p2,a2,p3,a3 ...) = a3;  // Theorem schemata

// -----------------------------------dsjs(S)------ disjoint(S) ------ S is a set of sets
dcl[dsjs,set,bool]; // := A[Q1,Q2: S, Q1 ~= Q2 -> Q1 NI Q2];  // Q1 NI Q2 == Q1/\Q2 = {};
!! Axdsjs := A[S:P[set], dsjs(S) == A[Q1:S,A[Q2: S, Q1 ~= Q2 -> Q1 NI Q2]] ];

!! Tdsjs1 := dsjs(S) -> A[Q:S, Q NI union(S--{Q})];                                      ///                        
!! Tdsjs3NI := dsjs({B1,B2,B3}) == B1 NI B2 & B1 NI B3 & B2 NI B3; //   by Axdsjs; TAcoll3b;                     
!! Tdsjsxor3 := dsjs({B1,B2,B3}) == A[x:union({B1,B2,B3}), xor3(x in B1, x in B2, x in B3)]; ///
!! Tdsjs3NIU := dsjs({B1,B2,B3}) -> B2 NI B1\/B3;                                           ///
 
// dsjs1(S: P(set)) := dsjs(S) & {} nin S;

// ----------------------------------partition(A,B): B is a partition of A
partition := {A, B ; Axprt1 := A=union(B); Axprt2 := {} nin B; Axprt3 := A[Q1_Q2_B, Q1 ~= Q2 -> Q1/\Q2 = {} ] };

!! Tprtin := [A,B] in partition == union(B)=A & A[Q:B, Q ~= {}] & A[Q1,Q2:B,  Q1/\Q2 ~= {} -> Q1=Q2]; 

partition :: [                                             // 1
Q1_Q2_B := {Q1,Q2; Q1 in B, Q2 in B};
!! Tprt1 := A[Q:B, Q <: A];                                // by Axprt1; Tunion4;
!! Tprt2 := A[Q1_Q2_B, Q1/\Q2 ~= {} -> Q1 = Q2];           // is Axprt3 ! CP; // ContraPosition
!! Tprt2a := A[Q1_Q2_B, Q1 ~= Q2 == Q1 NI Q2];
!! Tprt3 := A[Q1_Q2_B, A[z: Q1/\Q2,  Q1 = Q2]];            /// use Tprt2, Tinnemp;
!! Tprt4 := All(z, A[Q1_Q2_B, z in Q1 & z in Q2 -> Q1=Q2]); /// use Tprt3;
!! TprtIN := A[Q1_Q2_B, Q1 IN Q2 ->  Q1 = Q2];             ///
!! TprtIn := A[Q1_Q2_B, Q1 <: Q2 ->  Q1 = Q2];             ///
!! TprtE1 := A[x:A, E1[Q:B, x in Q]];
!! Tprt5 := B1 <: B & B1 ~= {} -> union(B1) ~= {};
!! Tprt6 := B1 <: B & x in union(B1) -> E[Q:B1, x in Q];   ///
// ! Tprt6 := A[Q:B, Q/\A ~= {} == Q<:A];                  // not used
// ! Tprt7 := A[B1:P[B], A[X:B, X in B1 == X <: union(B1)]];  // not used
// ! Tprt8 := A[Q:B, (A--Q, B--{Q}) in partition];         // not used
!! TprtINun := A[B1:P[B],A[B2:P[B], B1 IN B2 == union(B1) IN union(B2)]]; ///
!! TprtNI := A[B1:P[B],A[B2:P[B], B1 NI B2 == union(B1) NI union(B2)]]; // is TprtIN ! Teqvneg ! TINNI1;
!! Tprt9 := A[B1:P[B],A[B2:P[B], B1/\B2 = {} == union(B1)/\union(B2) = {}]]; ///
!! Tprt10 := {a,b} <: A == E[Q:B, {a,b} <: Q] or E[X1,X2: B,  X1 ~= X2 & a in X1 & b in X2]; // by Axprt1; Tunion7;
!! Tprt11 := {a,b}/\A={} or one(S/\A) or E[X:B, S=X] or E[X:B, S<<X] or 
                                E[X1,X2:B, X1~=X2 & E[X1:B, a in X1] & E[X2:B, b in X2] ]; // by Axprt1; Tunion9;
!! Tprt12 := A[Q:B, A=Q -> B={Q}];                        /// --- move to unionII ---
!! Tprt12a := A[Q:B, A=Q -> one(B)];                       ///
!! Tprt12b := one(B) == B ={A};                            // by Axprt1; TunionE1;
!! Tprt12c := A[Q:B, A=Q -> B={A}];                       ///
!! TprtU := A = U[Q:B, Q];                                // is TUun;
!! Tprt13 := A[Q:B, Q ~= {}];                             // is Axprt2 ! Axprt2;
!! Tprt14 := x in X & X in B -> x in union(B);
!! Tprt15 := A ~= {} == B ~= {};
!! Tprt16 := A[Q:B, B={Q} == union(B)=Q];
// see definition of cl in the file 7a cl in folder Fun

]; // partition :: [                                     // 1
// ===========================================END of SNAM, beginning REL====================================
// -----------------------------pair, pr1?,pr2?,ispair(z)------------------------------
pair  := {pr1, pr2 ; true};  
!! Tpair1 := pair = {z ; Exist(x,Exist(y, z = [x,y]))};         ///
!! Tpair2 := [x,y] in pair;

dcl[pr1,any,any];          // big problem: maybe new syntax will be needed , like z.pr1 ???
dcl[pr2,any,any];

!! Tpr1 := pr1([x,y]) = x;                                     // is ESb;  // DotElim
!! Tpr2 := pr2([x,y]) = y;                                     // is ESb;
!! Tpr3 := A[z:pair, z = [pr1(z), pr2(z)] ];                   ///
!! Tpr4 := [x,y] = [pr2(z), pr1(z)] == z = [y,x];              ///
!! Tpr5 := x = pr1(z) == Exist(y, z = [x,y] );                 ///

dcl[ispair,any, bool];

!! Axispair := All(z, ispair(z) == Exist(x,Exist(y, z = [x,y])) ); 
!! Tispair1 := All(x,All(y, ispair([x,y]) ));                  ///
// ! Tispair2 := ALL(d, ispair([a,b]) );                    // isA Tispair1(q1,q2); ///
// ------------------------------------------------REL---------------------------------
begin("REL");
REL := {R ; R in set; AxREL := A[z:R, ispair(z)] };          //   {R:set | ... };
// REL1 := {R; R in REL};
!! TRELemp := {} in REL;                                     //            by Def; TAemp;
!! TRELin := All(Q, Q in REL == A[z:Q, ispair(z)] );            //            is Axabin; 
!! TRELin1 := All(Q, Q in REL == A[z:Q, Exist(x,Exist(y, z = [x,y] )) ] );  //            is TRELin ! Axispair;
!! TabinREL := {x,y ; P} in REL;                                           ///
!! TREL1 := A[d, ispair(z)] -> R[d,z] in REL;                              ///
!! TREL2 := R[d, [x,y] ] in REL;                //            is TREL1(d,q1\/g2) ! Tispair2;

REL :: [
!! TRELA :=  A[z:R, Exist(x,Exist(y, z = [x,y] )) ];        //             is AxREL ! Axispair;
!! TREL0 := {x,y; [x,y] in R} = R;                                         ///
!! TRELnemp := R ~= {} == Exist(x,Exist(y, [x,y] in R ));                  ///
!! AxR1 := R in REL;
]; // REL :: [

RQ := {R,Q; R in REL; Q in REL};
RQ :: [
!! LRQ1 := A[z:R, ispair(z)];                                // is AxREL(R); // use AxR := R in REL;
!! LRQ2 := A[z:Q, ispair(z)];                                // is AxREL(R);
!! TRELIn := R <: Q == All(x,All(y, [x,y] in R -> [x,y] in Q ));                    ///
!! TRELIn1 := All(Q, Q <: R -> Q in REL);                                     /// 
!! TRELeq := R=Q == All(x, All(y, [x,y] in R == [x,y] in Q ));                     ///
!! TRELU := R\/Q in REL;                            /// use ProofC,TRELin,TAU;
!! TRELI := R/\Q in REL;                            /// use ProofC,TRELin,TAU;
!! TRELD := R--Q in REL;                            /// use ProofC,TDIn,TRELIn;
]; // RQ :: [

// dab := {a,b; a in any; b in any};
// dab :: [
ab := {[a,b]};
ab11 := { [a,b],[a1,b1] };
ab1 := { [a,b],[a,b1] };
abba := {[a,b],[b,a]};
// ]; // dab :: [

!! TRELS := ab in REL;                                /// line 1826, not 1827
!! TRELS2 := ab11 in REL;                             /// 
!! TRELS3 := ab1 in REL;                              /// 
!! Tabba1 := abba = {[a,b]} \/ {[b,a]};               // is TUS2;
!! Tabbat := abba in REL;                             // is TRELS2;

// ----------------------------------------------id---------------------------------
// begin("id");
dcl[id, fn(A:set, fn(A,A))];  //dcl[id, A:set, fn(A,A)]; all names in dcl-composite types must be unique for merging in pars;
!! Axid := id(A) = R[a:A, [a,a] ];
!! TidREL := id(A) in REL;                             ///   line 1836, not 1837
!! Tidin := [x,y] in id(A) == x=y & x in A;            ///
!! Tid1 := id(A) = {x,y; x=y & x in A};               ///
// ! Tidin1 := [x,y] in id(A) -> x=y;                            // not used
!! Tidin2 := All(x,All(y, [x,y] in id(A) == [y,x] in id(A) )); ///
!! TidU := id(A\/B) = id(A) \/ id(B);          ///

// ----------------------------------------------dom---------------------------------
// begin("dom");              // dcl[dom,REL,set];
REL :: [    // 1              // REL1 :: [    // 1
// dom := {x ; Exist(y, [x,y] in R)};
!! Axdom := dom(R) = {x ; Exist(y, [x,y] in R)};
!! Tdomin := All(x, x in dom(R) == Exist(y, [x,y] in R) );   //    is Axab;
!! Tdom1 := dom(R) =  R[z:R, pr1(z)];                        ///
!! Tdom2 := [x,y] in R -> x in dom(R);                       // by Contraposition;
!! Tdom3 := x nin dom(R) -> [x,y] nin R ;                    ///
!! Tdomemp1 := R = {} == dom(R) = {} ;                       ///
!! Tdom4 := [x,y] in R == x in dom(R) & [x,y] in R;          // isA Absorb ! Tdom2(x,y);
];  // REL1 :: [ // 1

!! Tdomemp := dom({}) = {};                         //  i = 1187
!! TdomS := dom(ab) = {a};                          ///
!! TdomS2 := dom(ab11) = {a,a1};                    ///
!! TdomS2a := dom(ab1) = {a};                       // byeqA TdomS2(a,b,a,b1),Tcoll2S; // ab1 = {[a,b], [a,b1]}
!! Tdomabba := dom(abba) = {a,b};                   //       is TdomS2(a,b,b,a); 
!! Tdomid := dom(id(A)) = A;                        ///  line 1861, not 1864

RQ :: [
!! TdomUin := All(x,  x in dom(R\/Q) == x in dom(R) or x in dom(Q) ); ///
!! TdomU := dom(R\/Q) = dom(R) \/ dom(Q);                             ///
!! TdomI := dom(R/\Q) <: dom(R) /\ dom(Q);                            ///
!! TdomD := dom(R--Q) <: dom(R) -- dom(Q);                            ///
!! TdomIn := R <: Q -> dom(R) <: dom(Q);                              ///

]; // RQ :: [
// -----------------------------------------im-------------------------------
// begin("im");           // dcl[im,REL,set];
REL :: [   // 2           // REL1 :: [   // 2 
// im := {y ; Exist(x, [x,y] in R)}; 
!! Axim := im(R) = {y ; Exist(x, [x,y] in R) };
!! Timin := y in im(R) == Exist(x, [x,y] in R);              // is Axab; by Taut((p==q) == (~p == ~q));
!! Timnin := All(y, y nin im(R) == All(x, ~([x,y] in R) ));
!! Tim0 := im(R) = {y ; E[x:dom(R), [x,y] in R] };           // byeq TEconj,Tdom4,Axim; 
!! Tim1 := im(R) = R[z:R, pr2(z)];                           ///
!! Tim2 := All(x,All(y, [x,y] in R -> y in im(R) ));  
           
// begin("Tim2E1");                                                   // Tim2E1: was overflow of sbst;
!! Tim2E1 := A[x:dom(R), E1[y:im(R), [x,y] in R] == Exist1(y, [x,y] in R )];  ///
!! Tim3 := R <: dom(R) # im(R);                                               ///
!! Timemp1 := R = {} == im(R) = {};                                           ///   
!! Timpdomemp := dom(R) = {} == im(R) = {};                          // is Tdomemp1 ! Timemp1;
!! Tim4 := im(R) <: A == All(x,All(y, [x,y] in R -> y in A ));       ///
]; // REL1 :: [ // 2

// !! TRELx3 := id(A) in REL;             // same as ! TidREL := id(A) in REL;
!! Timemp := im({}) = {};                 ///
!! TimS2 := im(ab11) = {b, b1};           ///
!! TimS := im(ab) = {b};                  /// im.REL(ab) = {b};
!! Timabba := im(abba) = {a,b};           // is TimS2(a,b,b,a);
!! Timid := im(id(A)) = A;                ///  line 1895, not 1924 ??? a lot of comments below !!!

// RQ :: [
// ! TimUt := R\/Q in REL;                                          ///
// ! TimIt := R/\Q in REL; 
// ! TimDt := R--Q in REL;      
// ! TimU := im(R\/Q) = im(R) \/ im(Q);                             ///
// ! TimI := im(R) /\ im(Q) <: im(R/\Q);                            ///              
// ! TimD := im(R) -- im(Q) <: im(R--Q);                            ///
// ! Timpdomemp := dom(R) = {} == im(R) = {};       // is Tdomemp1 ! Timemp1; move to REL1
// ! Timm := R <: Q -> im(R) <: im(Q);                              ///

// ]; // RQ :: [

// REL1 :: [ // ------------------------------ inv ------------------------

// begin("inv");              // inv := {x,y ; [y,x] in R};
// !! Axinv := inv(R) = {x,y ; [y,x] in R};
// ! Tinvt := inv(R) in REL;                                  // is TabinREL;
// ! Tinv := inv(R) = R[z: R, [pr2(z), pr1(z)] ];             ///
// ! Tinv0 := inv(R) = R[(x,y):R, (y,x)];                   ///
// ! Tininv := All(x,All(y, [x,y] in inv(R) == [y,x] in R )); ///
// ! Tininv1 := z in inv(R) == [pr2(z), pr1(z)] in R;         // byeq Tpr3; Tininv(pr1(z),pr2(z));
// ! Tdominv := dom(inv(R)) = im(R);                          ///
// ! Timinv := im(inv(R)) = dom(R);                           ///

// ];  // REL1 :: [

RQ :: [
! TinvU := inv(R\/Q) = inv(R) \/ inv(Q);         ///
! TinvI := inv(R/\Q) = inv(R) /\ inv(Q);         ///
! TinvD := inv(R--Q) = inv(R) -- inv(Q);         ///
]; // RQ :: [

// REL1 :: [
// !! Axinv1 := inv(R) in REL;
// ! Tinv1 := inv(inv(R)) = R;            ///  ??? inv(inv) = this;
// ]; // REL1

// ! Tinvid := inv(id(A)) = id(A);         ///
// ! Tinvab11 := inv(ab11) = {[b,a], [b1,a1]};      // byeq Tinv0, TRcol2;          
// ! TinvabS := inv(ab) = {[b,a] };                 // byeq Tinv0, TRcol1;
// ! Tinvabba := inv(abba) = abba;                  // is Tinvab11(a,b,b,a);

// --------------------------------------comp--o-------------------------------------------
// begin("comp");
!! Lo1_ptd := f in afn(A) & g in afn(A) -> f o g in afn(A);
!! Lo_ptd := f in bfn(A,A) & g in bfn(A,A) -> f o g in bfn(A,A);    // _ptd : precizing type definition;
dcl[o, REL,REL, REL]; 
RQ :: [
// o, comp := {x,z | E[y, (x,y) in R & (y,z) in Q]};          // Suppes
// o, comp := {x,z | E[y, (x,y) in Q & (y,z) in R]};          // Bourbaki: like function composition
!! Axcomp := R o Q = {x,z ; Exist(y, [x,y] in Q & [y,z] in R)}; 
!! Tcompt := R o Q in REL;            // by Axcomp; TabinREL; /// Sup 3.19
!! Tcompin := All(x,All(z, [x,z] in R o Q == Exist(y, [x,y] in Q & [y,z] in R) )); // by Axcomp; Tab2in;
!! Tcompdom := dom(R o Q) <: dom(Q);                         ///  Sup 3.21
!! Tcompim := im(R o Q) <: im(R);                            ///
!! Tcompnemp := dom(R)/\im(Q) ~= {} == R o Q ~= {};          // by Taut((~p == ~q) == (p==q)); ///
!! Tcompemp := dom(R)/\im(Q) = {} == R o Q = {};             //// TcompNI
!! Tcomp6 := inv(R o Q) = inv(Q) o inv(R);                     ///
!! Tcomp8 := R o Q ~= {} == dom(R)/\im(Q) ~= {};              /// see Tcompnemp
]; // RQ :: [

!! Lcomp0 := SS\/TT in REL;
!! Lcomp01 := QQ\/SS\/TT in REL;
!! Lcomp02 := SS/\TT in REL;
!! Lcomp03 := SS--TT in REL;
TRELemp;                           // TRELemp := {} in REL; for Tcomp1;
!! Tcomp1 := A[R:REL, {} o R = {}];                                                /// Sup 3.20
!! Tcomp2 := A[R,R1,S,S1:REL, R <: R1 & S <: S1 -> R o S <: R1 o S1 ];   /// Sup 3.22
!! Tcomp3 := RR o (SS \/ TT) = RR o SS \/ RR o TT;          /// Sup 3.23
!! Tcomp3a := A[S,T,R:REL, (S \/ T) o R = R o S \/ R o T ];        // A[S:REL,A[T:REL : multiple subst-ns !!!
!! Tcomp3b := A[R,Q,S,T:REL,(R\/Q) o (S\/T) = R o S \/ R o T \/ Q o S \/ Q o T]; // use Tcomp3, Tcomp3a;
!! Tcomp3c := RR o (QQ\/SS\/TT) = RR o QQ \/ RR o SS \/ RR o TT;    // use Tcomp3;
!! Tcomp4 := RR o (SS /\ TT) <: (RR o SS) /\ (RR o TT);             /// Sup 3.24 o < \/ < /\;
!! Tcomp5 := (RR o SS) -- (RR o TT) <: RR o (SS -- TT);             /// Sup 3.25
!! Tcomp7 := A[R,S,T:REL,(R o S) o T = R o (S o T)];                ///
!! Tcompid := id(A) o id(B) = id(A/\B);                             ///

REL :: [  // 3          // REL1 :: [  // 3
!! Tcompid0 := id(A) o R <: R;                                    ///
!! Tcompid0a := R o id(A) <: R;                                   ///
!! Tcompid1 := im(R) <: A -> id(A) o R = R;                       ///
!! Tcompid2 := dom(R) <: A -> R o id(A) = R;                      ///
]; // REL1 :: [ // 3

// -----------------------------------Restriction--|--R|A------------------------
// begin("REL_restriction");   // dcl[|,REL,set,REL];
REL :: [  // 4                 // REL1 :: [  // 4
!! Axrestr := R|A = {x,y ; [x,y] in R & x in A};
!! TrestrIn := R|A <: R;                                           // by Axrestr; Tab2In;
!! Trestrt := R|A in REL;                                          // is TRELIn1(R|A) ! TrestrIn;
!! Trestrin := All(x,All(y, [x,y] in R|A == [x,y] in R & x in A)); //  by Axrestr; Axab2in; 
!! TrestrdomIn := A <: dom(R) -> dom(R|A) = A;                     /// line 1986, not 1987
!! Trestrdom := dom(R|A) = dom(R)/\A;                              ///
!! Trestrdom1 := dom(R) <: A -> R|A = R;                           ///
!! Trestrim := im(R|A) = {y ; E[x:A, [x,y] in R]};                 ///
!! Trestrim1 := im(R|A) <: im(R);                                  // is Timm ! TrestrIn;
!! Txx1 := R|dom(R) in REL;
!! Trestrim2 := im(R|dom(R)) = im(R);                              // is SBEt(im(R)) ! Trestr7(R);
// !! Txx0 := R|dom(R) in REL;                                     // same as Txx1;
!! Txx2 := R|(dom(R)--A) in REL; 
!! Txx3 := R|(A\/B) in REL;
!! Txx4 := R|(A/\B) in REL;
!! Txx5 := R|(A--B) in REL;
! TrestrD := R = R|A \/ R|(dom(R)--A);                            ///
// ! Trestr0 := R|A = R /\ (A # im;                // not used
!! Trestr1 := X <: Y -> R|X <: R|Y;                   /// Sup3.29 line 2000, main.his: 2001  s= !! Trestr1 := X <: Y -> R|X <: R|Y; 
!! TrestrU := R|(A\/B) = R|A \/ R|B;                  /// Sup3.31     // was Trestr2
!! TrestrI := R|(A/\B) = R|A /\ R|B;                  /// Sup3.30     // was Trestr3
!! Trestr4 := R|(A--B) = R|A -- R|B;                  /// Sup3.32     // was TrestD
!! Trestr7 := R|dom(R) = R;                           ///
!! Trestr8 := dom(R|A) = dom(R)/\A;                   /// with Staut(X<:Y -> Y/\X = X);
// begin("Trestr8a"); // was wrlist:overflow: z= #13652R(0 1 7742)|#13649R(0 1 7742)|R(0 1 7742) sizelist= 100
// !! Trestr8a := A <: dom(R) -> dom(R|A) = A;           /// line 2007, not 2008; same as TrestrdomIn above;
!! Trestr9 := All(A, R o id(A) = R|A);                ///
!! Trestr10 := All(A, id(A) o R = {x,y; [x,y] in R & y in A}); ///
!! Trestremp := R|{} = {};                                     ///
!! Trestrm := All(A,All(B, A<:B -> R|A <: R|B ));             ///
];   // REL1 :: [ // 4

! Trestr11 := All(A,All(B, B <: A -> id(A)|B = id(B) ));             ///
// ! Trestr12 := All(A,All(B, B<:A -> id(A) o id(B) = id(A/\B) ));       // byeq Trestr9, Trestr11;

RQ :: [
K := dom(R)/\dom(Q);
! Txx6 := R|K in REL;
! Txx7 := Q|K in REL;
! Txx8 := Q|B in REL;
! LKR := K <: dom(R);                                 //  is TIIn1;
! LKQ := K <: dom(Q);                                 //  is TIIn2;
! TredomRK := dom(R|K) = K;                           // is TrestrdomIn ! LKR;
! TredomQK := dom(Q|K) = K;                           // is TrestrdomIn ! LKR;
! TRQ1 := dom(R|K) = dom(Q|K);                        // is TredomRK ! TredomQK;
! TreU := R|A \/ Q|B <: R\/Q;                        ///
! TreU1 := All(A, R|A \/ Q|A <: R\/Q);                /// is TreU(,A);
! Trestr5 := All(A,(R o Q)|A = R|A o Q);           /// Sup3.33
! Trestr6 := All(A, (R\/Q)|A = R|A \/ Q|A);       /// is not in Suppes
]; // RQ :: [
/*
// -----------------------------------valr---%---R%A = im(R|A)-------------------------------
// RA :: begin
// begin("valr_%");
dcl[%,REL,set,set];
// %, valr, R(A) := im(R|A);
REL :: [ // 5              // REL1 :: [ // 5
!! Axvalr := R%A = im(R|A);
! Tvalr := R%A = {y ; E[x:A, [x,y] in R]};                      // is Axvalr ! Trestrim;
! Tvalrin := All(y, y in R%A == Exist(x, [x,y] in R & x in A)); //  isA Axab; R
! Tvalremp := R%A = {} == dom(R) /\ A = {};                     ///
! Tvalr0 := dom(R) /\ A <: inv(R) % (R % A);                    ///
! Tvalrim := R%A <: im(R);                                      // is Timm ! TrestrIn;      
! TvalrS := All(x, R%{x} = {y ; [x,y] in R} ); // {y | E[x:A, (x,y) in R]}; ///
! TvalrU := R%(A\/B) = R%A \/ R%B;                        // byeq Axvalr,TrestrU,TimU; 
! TvalrI := R%(A/\B) <: R%A /\ R%B;                       // bytr Axvalr,TrestrI,TimI;
! TvalrD := R%A -- R%B <: R%(A--B);                       // bytr Axvalr, TimD, -Axvalr;
! Tvalr4 := A <: B -> R%A <: R%B;                         ///
! Tvalr5 := (R%A) /\ B <: R % (A /\ inv(R) % B);          ///

]; // REL1 :: [ // 5
*/
// --------------------------------------vals--vals(R,x) = R%{x} = im(R|{x})---------------------
// begin("vals");
dcl[vals,REL,any,set];    // dcl[vals,REL,any,set];   // vals(x) := {y | [x,y] in R};
REL :: [ // 6           // REL1 :: [ // 6
// vals(R,x) := F[x:any, {y ; [x,y] in R}];
!! Axvals := All(x, vals(R,x) = {y ; [x,y] in R});
! Tvalsin := All(x,All(y, y in vals(R,x) == [x,y] in R));           // isA Axab;
! Tvals1 := All(x, vals(R,x) = im(R|{x}));                          // was R%{x} = im(R|{x}; by Axvals; TvalrS;
! Tvalsim := A[x:dom(R), vals(R,x) <: im(R)];                       // by Tvals1; Tvalrim;
! Tvalsab := A[x:dom(R), vals(R,x) = {y; y in im(R); [x,y] in R}];  //  is TInab4 ! Axvals;
! Tvalsemp := All(x, vals(R,x) = {} == x nin dom(R));               ///
! Tvalsrestr := A[x:A, A <: dom(R) -> vals(R|A,x) = vals(R,x)];     ///

]; // REL1 :: [ // 6

// RQ := {R:REl, Q:REL};
RQ :: [

! TRELeq1 := R = Q == dom(R)=dom(Q) & A[x:dom(R), vals(R,x) = vals(Q,x)];   // with Taut8; ///
! Tvals2 := dom(R) = dom(Q) -> R=Q == A[x:dom(R), vals(R,x) = vals(Q,x)];   // by Teqvneg,TNA;
! Tvals3 := dom(R) = dom(Q) -> R~=Q == E[x:dom(R), vals(R,x) ~= vals(Q,x)]; 
! TvalsU := All(x, vals(R\/Q,x) = vals(R,x) \/ vals(Q,x));                   /// was Tvals4

]; // RQ :: [
!! TRELimm := A[R,Q:REL, R <: Q -> im(R) <: im(Q)];
// ------------------------------------------ func --------------------------- 

REL :: [ // 7                // REL1 :: [ // 7
// begin("func");
// func := A[x:dom, one(vals(x)) ];                                             // was func1
! Axfunc := func(R) == A[x:dom, one(vals(R,x)) ];                              //  by Axvals;
! Tfunc := func(R) == A[x:dom, Exist1(y, [x,y] in R )];                       // was Axfunc1a replace on Tfunc
func1 := All(x,All(y,All(y1, [x,y] in R & [x,y1] in R -> y = y1 )));       // was func1a
!! Axfunc1 := func1 == All(x,All(y,All(y1, [x,y] in R & [x,y1] in R -> y = y1 )));
!! AxfuncR := func(R) == [x,y] in R & [x,y1] in R -> y=y1;
! Tfunc1 := func(R) == func1;                                                // is L1 ! L2; by Axfunc1;
! Tfunc1a := func == All(x,All(y,All(y1, [x,y] in R & [x,y1] in R -> y = y1 )));
! L1 := func(R) -> func1;                                                     ///
! L2 := func1 -> func(R);                                                     ///
! Tfunc1b := func(R) == All(x,All(x1,All(y,All(y1, [x,y] in R & [x1,y1] in R -> x ~= x1 or y = y1 ))));
!! TfuncR := func(R) == A[X,Y,Y1:any, [X,Y] in R & [X,Y1] in R -> Y=Y1];
!! TRELfn := func(R) -> R in fn(dom(R), im(R));         // for checking R(x) in TfuncRin; see TRELfn below;
!! TfuncRin := func(R) & [x,y] in R -> R(x) = y;  
!! Tfunc2 := func(R) -> func(R|A);                      ///
]; // REL1 :: [ // 7 LAST

! Tfuncemp := func ({});                                                  // by Def, Tdomemp; TAemp;                                            
! TfuncS := func(ab);                                                     ///
! Tfunc2a := func(ab1) == b=b1;       ///
! Tfunc2b := a ~= a1 -> func(ab11);                      /// ab1 := {a,b,a1,b1: any};
! Tfunc2c := func(ab11) == (a=a1 -> b=b1);                          /// ab11 := {(a,b), (a1,b1)}
! Tfuncabba := func(abba);                                           ///

// RQ := {R:REl, Q:REL};             // see file REL
RQ :: [

// K := dom(R)/\dom(Q);
! R|A in REL;
! Tfunc3 := R <: Q & func(Q) -> func(R);                                   ///
! Tfuncre := func(R) -> func(R|A);                                         ///
// begin("TfuncUeq");                                     // overflow of lot
! TfuncUeq := dom(R)=dom(Q) & func(R) & func(Q) -> func(R\/Q) == R=Q;      ///
! TfuncUemp := dom(R)/\dom(Q) = {} & func(R) & func(Q) -> func(R\/Q);      ///
! Tfunc4 := func(R\/Q) == func(R) & func(Q) & R|K = Q|K;                   ///
! Tfunc4a := K={} -> func(R\/Q) == func(R) & func(Q);                      /// not used
! Tfunc5 := func(R\/Q) -> A[x:dom(R), vals(R\/Q,x) = vals(R,x)];           ///

]; // end RQ :: [;

// ! Tfuncemp := func(REL({}));                                             //  by Tfunc,Tdomemp; TAemp;

vith := [TFNREL,Tindp,TfnREL,TfnFN]; // very important theorems,TInrefl,AxP,Tindp1,Tcaret1,TRA,,TDIn,Tidt removed;
// begin("FN");
FN := {f ; AxFN0 := f in REL, AxFN1 := func(f)};                   // A[x:dom, E1[y, (x,y) in R]];
// FN1 := {f; Axf := f in FN };

!! TFNREL := FN <: REL;                                             // is TabIn;
!! TFNemp := {} in FN;                                              // by Def; TRELemp & Tfunc5;
!! TFN3 := All(a, {[a,a]} in FN);                                   // ???
!! TFNin := All(f, f in FN == f in REL & func(f));                  // is Axab;   // & A[x:dom, E1[y, (x,y) in f]]
!! TFNin1 := A[R:REL, R in FN == func(R)];                          // is TAab2;
!! TFN2 := A[R:FN, All(S, S <: dom(R) -> R|S in FN) ];                             ///
// ! TFNU := A[R:FN,A[Q:FN, dom(R)/\dom(Q) = {} -> R\/Q in FN]];   ///   moved to fg;
// ! TFN4 := A[R:FN,A[Q: FN, R|(K1 := dom(R)/\dom(Q)) = Q|K1 -> R\/Q in FN]]; /// moved to fg;

Tabbat;  // ! Tabbat := abba in REL;  for Tdomabbaina;
!! TFNab := ab in FN;             // ab := {[a,b]}; ab1 := { [a,b],[a,b1] };
!! TFNabba := abba in FN;         // abba := {[a,b],[b,a]};
!! Tdomabin := a in dom(ab);
!! Tval1 := ab(a) = b;                            /// was TfnS1 
!! Tval2 := A[f:FN, f\/{[a,b]} in FN == (a in dom(f) -> f(a) = b)];   // see proof in 30 etcp.v     ///
!! Tdomabbaina := a in dom(abba);
!! Tdomabbainb := b in dom(abba);
!! Tvalabba1 := abba(a) = b;                      // is TvalG1(a,b);
!! Tvalabba2 := abba(b) = a;                      // is TvalG1(b,a);

!! Tvalfunc := A[f:FN, func(f) -> A[x:dom(f), Exist(y, y = f(x))]]; // was ==, // is Tfunc ! TvalG1a;

dcl[vals2,set,any,set];

fx := {f,x ; Axf1 := f in FN, Axfx2 := x in dom(f)};
fx :: [                 // istr2: seek only in fx ???
!! L0a := f in REL;                                  // for checking im(f) in L2;
!! L0 := vals2(f,x) = {y ; [x,y] in f};               // is Axvals(x);
!! L1 := Exist1(y, [x,y] in f);                      // is TFN1(x);  with Tim2E1;
!! L2 := E1[y:im(f), [x,y] in f];                    // by TE1ab;
!! L3 := one({y; y in im(f) ; [x,y] in f});
!! L4 := one(vals2(f,x));                             // is L1 ! Axvals;

// val, f(x) := the({y: im(f) | (x, y) in f});       // the(A) was T[A];
// !! Axval := f(x) = T[{y: im(f) | (x, y) in f}] ;
val := the(vals2(f,x));                               // f(x) = val;
!! Axval := f(x) = the(vals2(f,x)) ;
!! Tvalim := f(x) in im(f);
!! TvalG := [x, f(x)] in f;   // Tvalim & TvalG;     // is TTab1 ! L3;
!! TvalG1 := All(y, [x, y] in f == y = f(x));        ///
!! TvalD := f = {[x,f(x)]} \/ f -- {[x,f(x)]};       // is TinDU ! TvalG
!! TvalD1 := All(a, All(b, [a,b] in f -- {[x,f(x)]} == [a,b] in f & a ~= x)); ///
!! TvalG1a := [x,b] in f == b = f(x);          // isA TvalG1(f,a)(b);
// ! TvalG2 := [z1,z2] in f == z1 in dom(f) & z2 = f(z1);    /// see TvalG1a
// ! TvalG2a := A[f:FN, [z1,z2] in f -> f(z1) = z2];      // is TvalG2 ! Taut((p == q&r)->(p->r));
// ! Leib :=  x=b -> f(x)=f(b)];     /// not needed, use Sbet: Leib(f,a,b) == Sbet(f(a))
// ! TGR := f = R[x:dom(f), [x, f(x)]];              /// not used
]; // fx :: begin
   
  begin("fg");
 
fg := {f,g; f in FN; g in FN};
fg :: [
!! L0 := f in REL; !! L01 := g in REL;
!! Tfgeq := f = g == dom(f) = dom(g) & A[x: dom(f), f(x) = g(x)];    ///
!! TfgU_type := f\/g in REL;                                              // line 2182, not 2183;  same as L0_type below;               
!! TfgdomU := dom(f) <: dom(f\/g);                                   // : Tfgdp simr: [x,x1] in dom(f); by lot;
!! Tfgdomin := x in dom(f\/g) & ~(x in dom(f)) -> x in dom(g);       //       [x,x1] in A*B;    by Tindp;
!! TfgdomIn := f <: g -> dom(f) <: dom(g);                           //       x in A & x1 in B;is lot;
// ! Tfgdp := dom(f) = A#B -> (f = g == dom(f) = dom(g) & A[x:A, x1:B, f([x,x1]) = g([x,x1]) ]); ///
!! TvalU := A[x: dom(f), f\/g in FN -> (f\/g)(x) = f(x)];     //                               ///
!! TvalUif := A[x:dom(f\/g), f\/g in FN -> (f\/g)(x) = if(x in dom(f), f(x):any, g(x):any)];  "nosimr";         ///
!! TvalIn := A[x:dom(f), f <: g -> f(x) = g(x)];     
!! TfgdomNIU :=  dom(f) NI dom(g) -> f\/g in FN;                  /// was TFNU 
]; // fg :: [

// module im;   // 4 im 5/02/10 15 17
begin("im");
FN :: [             // FN1 :: [               // !! AxR := R[d, f] = {z ; E[d, z = f]} #1 FN

!! Tim := im(f) = R[x:dom(f), f(x)];                           ///            
!! Tim0f := im(f) = {y ; E[x:dom(f), y = f(x)] };              // byeq Tim0, TvalG1;
!! TimE := All(y, y in im(f) == E[x:dom(f), y = f(x)]);  // by Axim; TRin; // Timin
!! Tim2E := All(A, A <: im(f) & least2(A) -> E[x1:dom(f),E[x2:dom(f), A = {f(x1),f(x2)}]]); ///
!! Timnin := y nin im(f) == A[x:dom(f), y ~= f(x)];            // byeq Timin, TNE;
!! TimAE := A[y:im(f), E[x:dom(f), y = f(x)] ];                // by TAAll; TimE;
!! TimA := All(B, im(f) <: B == A[x:dom(f), f(x) in B]);               // by Tim; TRA; 
!! TimA1 := All(B, B <: im(f) == A[z:B, E[x:dom(f), z = f(x)]]);        // by Tim; TRA1;
!! Timemp := dom(f) = {} == im(f) = {};                        // is Timemp1.f;
!! Timval := A[x:dom(f), f(x) in im(f)];                          // is Tvalim; // replace with Tvalim!
!! TRim := R[y:im(f), Q(y)] = R[x:dom(f), Q(f(x))];                            ///
!! TAimA := A[y:im(f), Q(y)] == A[x:dom(f), Q(f(x))];                          ///
!! TAimA2 := A[y:im(f),A[y1:im(f), Q(y,y1)]] == A[x:dom(f),A[x1:dom(f), Q(f(x),f(x1))]];          ///
!! Toneim := one(im(f)) == dom(f) ~= {} & A[x:dom(f),A[x1:dom(f), f(x)=f(x1)]];  // was TE1im

];  // module im;   // FN1 ::[    #1 FN

begin("fn");
// module fn;   // 5 fn function 3/26/10 4.16 24 10/10/11

!! Axfn := f in fn(A,B) == f in FN & dom(f) = A & im(f) <: B;    // was Tfnin
!! TRELfn := A[R:REL, func(R) -> R in fn(dom(R), im(R))];        // moved to REL1.7
!! TfnFN := fn(A,B) <: FN;                                       // is TabIn; by Def;
!! TfnFNA := f in fn(A,B) -> f in FN;                            // by Absorb;
// ! TFnFNA := f in Fn(A,B) -> f in FN;
!! TfnFNA1 := f in fn(A,B) & f in FN == f in fn(A,B);            // ???
!! TfnE1A := f in fn(A,B) -> (A ~= {} & A[x1:A, A[x2:A, f(x1)=f(x2)]] == E1[b:B, A[x:A, f(x)=b]]); 
!! Tfndp := f in fn(A#B,C) -> A[x:A,y:B, f(x,y) in C];
!! Tfndp1 := f in fn(A#B,D) & x in A & y in B -> f(x,y) in D;
// ! TFndp := f in Fn(A#B,C) -> A[x:A,y:B, f(x,y) in C];
!! Tim2 := f in fn(A#B,C) -> im(f) = {z; E[x1:A,x2:B, z = f(x1,x2)] };
// ! Tim2Fn := f in Fn(A#B,C) -> im(f) = {z; E[x1:A,x2:B, z = f(x1,x2)] };
!! Tim2In := f in fn(A#B,C) -> im(f) <: C;

// dgHA := {g,H,A; g in fn(A#A,A), H in P[A], A in set, A[x,y:H, g(x,y) in H] }; // move out there to Functions!
// dgHA :: [
// ! L0_type := g|(H#H) in fn(H#H,H);
// ! L01 := H <: A;
// ! L02 := f1 in fn(A,B) -> f1|H in fn(H,B);                                       //           g         A     H
// ! TclosedH := f1 in fn(A,B) -> A[x,y:H, (f1|H)( (g|(H#H))(x,y) ) = f1(g(x,y))];  // M1 := [*(group).G, elg.G, H];
// ]; // dgHA :: [  

!! AxFn := f in Fn(A,B) == f in FN & A <: dom(f) & im(f) <: B;
!! TFnFN := Fn(A,B) <: FN;                                       // is TabIn; by Def;
!! TFnFNA := f in Fn(A,B) -> f in FN;                            // by Absorb; 
!! Tim2FnIn := f in Fn(A#B,C) -> im(f) <: C;
!! TFnim1 := f in Fn(A,B) &  A[y:B, E[x:A, y = f(x)]] -> im(f|A) = B;
!! TredomFn := f in Fn(A,B) -> dom(f|A) = A; 
!! TFnAE1 := A ~= {} & g in Fn(A,B) & A[a,b:A, g(a) = g(b)] -> E1[c:B, A[a:A, g(a)=c]];

FN :: [         //  FN1 :: [  // FN1 := {f; Axf := f in FN };   #2 FN
!! TfninA := f in fn(A,B) == dom(f) = A & A[x:dom(f), f(x) in B];         // Tindp := [x,y] in X # Y == x in X & y in Y;  
!! Tfndomim := f in fn(dom(f), im(f));                                    ///  [x,y] in dom(f) ==(lot) [x,y] in A#B ==(Tindp)

x_A1_y_B1 := {x,y; x in A1; y in B1};                                    // introduced for checking f([x,y]);
x_A1_y_B1 :: [ L0_type := [x,y] in A1#B1; by Tindp; x in A1 & y in B1; ];                             
// ! Tfnin2 := f in fn(A1#B1,C1) == dom(f) = A1#B1 & im(f) <: C1 & A[x_A1_y_B1, f([x,y]) in C1]; 
];  // FN :: [                                                  #2 FN
               
!! TfnREL := fn(A,B) <: REL;              
!! Tfndom := f in fn(A,B) -> dom(f) = A;                                  // is Tfnin;
// ! TFndom := f in Fn(A,B) -> A <: dom(f);  
!! Tfnim := f in fn(A,B) -> im(f) <: B;                                   // is Tfnin;  
!! Tfnim1 := f in fn(A,B) -> (im(f)=B == A[y:B, E[x:A, y = f(x)]]);       ///
!! Tfnim1a := f in fn(A,B) & A[y:B, E[x:A, y = f(x)]] -> im(f) = B;
!! Tfnval := f in fn(A,B) & x in A -> f(x) in B;                          ///  
!! TfnM := All(A,All(B,All(B1, B <: B1 -> fn(A,B) <: fn(A,B1))));         ///
!! TfnA := f in fn(A, B) -> A[x:A, f(x) in B];                           /// All(f, f in fn(A, B) -> A[x:A, f(x) in B]);
// ! TFnA := f in Fn(A, B) -> A[x:A, f(x) in B];
!! Tfnd := f in fn(d, B) ->  A[d, f(^d) in B];
!! TfnS0 := {[a,b]} in fn({a},{b});                                      ///
!! TfnS := b in B -> {[a,b]} in fn({a},B);                               ///
!! Tfnemp1 := fn({},B) = {{}};                                           // is Trelemp1;                        
! Tfnemp := fn({},{}) = {{}};                                           // is Trelemp;
// ! Tfnfn := f in fn(A, fn(B, C)) & a in A   -> All(b, b in B -> f(a)(b) in C);        ///
// ! Tfnin3 := A[f:FN,a,b, f\/{(a,b)} in FN == (a in dom(f) -> f(a) = b)]; // same as Tval2
begin("Tfnfn");         //was: hgt1 overflow of depth=  100
! Tfnfn := f in fn(A, fn(B, C)) & a in A & b in B -> f(a)(b) in C;       ///
! TE1Anemp := t ~= {} & f in fn(t,t) & A[x1:t,A[x2:t, f(x1) = f(x2)]] -> E1[c:t, A[x:t, c = f(x)]]; ///

// module F;   // 6 F[d,f] - Lambda-notation 10/02/11
begin("F");
dAB := {a,b; a in A; b in B}; 
!! AxF := F[d,G] = R[z:d, [z, Rep(d,G,z)]];                 // q.z = q(z) = Sb(q, ^d, z)
!! TFREL := F[d,G] in REL;                                  // by AxF; TREL2; 
!! TFfunc := func(F[d,g]);                                  // was G
!! TF := F[x:A, G(x)] = R[x:A, [x,G(x)] ];                  // is AxF;
!! TFred1 := A[x:A, F[x:A, P(x)](x) == P(x)];
!! TFin := All(x,All(y, [x,y] in F[d,G] == x in d & y = Rep(d,G,x) ));    ///
!! TFFN    := F[d, g] in FN;                                // by TFNin; TFREL & TFfunc; // was G;
!! TFdom   := dom(F[d,g]) = d;                              // by AxF; is TFNdom;
!! TimF   := im(F[d,g]) = R[d,g];                           /// was TimFR                // was G;
!! TFim := A[d, G in B] == im(F[d, G]) <: B;                // by TimF; TRA;
!! TFred   := A[x:d, F[d,g](x) = Rep(d,g,x)];              /// beta reduction,  not used ???
// ! TFred1  := A[d, F[d,q](^d) = q];                      // is TFred(^d);
!! TFinfn := F[d,g] in fn(d,B) ==  A[d, g in B];  // byeq TfninA,TFdom,Axrefl,TAdAr;
FAGx := F[x:A, G(x)];
!! TF1t := FAGx in fn(A, im(FAGx));
!! TFinfn1 := FAGx in fn(A,B) ==  A[x:A, G(x) in B];
!! TFinj := injective(FAGx) == A[x1,x2:A, G(x1)=G(x2) -> x1=x2];
!! TFinj1 := injective(FAGx) == A[x1,x2:A, G(x1)=G(x2) == x1=x2]; // FAGx := F[x:A, G(x)];
!! TFdom1 := dom(FAGx) = A; 
!! TFim1 := im(FAGx)=B == FAGx in fn(A,B) & A[y:B, E[x:A,y=G(x)]]; // Tfnim1 := f in fn(A,B)->(im(f)=B == A[y:B,E[x:A, y = f(x)]]); 
!! TFt := All(B, g in B -> F[d,g] in fn(d,B) );                             ///
!! TFx := F[d,g] = F[x:d, Rep(d,g,x)];                                             ///
!! TFinfn2 := F[dAB,G(a,b)] in fn(A#B,C) ==  A[dAB, G(a,b) in C];     // is TFinfn; // dAB := {a,b; a in A; b in B}; 
!! TFfnA := F[d,g] in fn(A,B) == d=A & A[d, g in B];        // is TfninA;     ///
!! TFFA := F[d,f] = F[d,g] == A[d, f=g];                    ///
!! TFcol1 := F[x: {a}, G(x)] = {[a,G(a)]};                  // by TF; TRcol1;
!! TFcol2 := F[x:{a,b}, G(x)] = {[a,G(a)], [b,G(b)]};       //  by TF; TRcol2;
// ! TFin1 := A[A,a,b, (a,b) in F[x:A, G(x)] == a in A & b = G(a)];  not used, see TFin; 
!! TFf := A[f:FN, f = F[x:dom(f), f(x)]];

// ! Lfch := d ~= {} -> ^d in d;                                      ///
// ! TFch := d ~= {} -> A[f: fn(d, B), F[d, f(^d)] = f];              /// ch : choice --
// ! TFemp := d = {} == F[d,g] = {};                       // is Tdomemp1;
// ! TFemp1 := F[{}, g] = {};                              // by AxF; TRemp;
// TFif1 := if f has the form "F[d,if(p1,a1, ...)]" then A[d, p1 -> f(^d) = a1] is a theorem;
// ! TFif1(f) := f =: F[d,if(p1,a1, ...)] -> A[d, p1 -> f(^d) = a1];        /// Theorem schemata
// ! TFif2(f) := f =: F[d,if(p1,a1,p2,a2 ...)] -> A[d, p2 -> f(^d) = a2];       ///  
// ! TFif3(f) := f =: F[d,if(p1,a1,p2,a2,p3,a3 ...)] -> A[d, p3 -> f(^d) = a3]; ///

// module chv;   // 7 change value of function f, at the point a, on b; // skipped !!!
 begin("module_TfnE");   //9 Theorems about function existence
!! TfnAE1   := A[x:A, E1[y:B, Q(x,y)]] -> Exist1(f, f in fn(A,B) & A[x:A, Q(x,f(x))]);

// module cl;   // 8 class function  // 4/18/13
begin("cl");
partition :: [             //   2  cl        
dax := {a,x; a in A, x in A};
// cl := F[a:A, the({Q; Q in B, a in Q}) ]; // T[Q:B, a in Q]];        // T[Q:B, a in Q] = the({Q; Q in B, a in Q}
! Tprtcl := Exist1x(cl, (Axcl1 := cl in fn(A,B)) & (Axcl2 := A[x:A, x  in cl(x)])); is TfnAE1(TprtE1); // ! TprtE1 := A[a:A, E1[Q:B, a in Q]];
// ! Tclt1 := cl in REL;
// ! Axcl := cl = F[a:A, the({Q; Q in B, a in Q}) ];
!! Tcldom := dom(cl) = A;                                         // is TFdom;
!! Tcl1 := A[a:A, cl(a) in B];                                  
// ! Tclt := cl in fn(A,B);                                       // same as Axcl1;   // by TfninA; Tcldom & Tcl1;
// ! Tcl2 := A[a:A, a in cl(a)];                                  // same as Axcl2;   // ! Tcl2 := A[a:A, A[a:A, a in cl(a)]];  ///
!! Tcl3 := A[dax, x in cl(a) == cl(x) = cl(a)];                   ///
!! Tcl4 := A[dax, x in cl(a) == a in cl(x)];                      ///
!! Tcl5 := A[x:A, cl(x) = A -> B = {A}];                          ///
!! TprtR := B = R[x:A, cl(x)];                                    ///
// ! Tclfn := A[f:fn(A,B), A[x:A, x in f(x)] -> f = cl];          /// ???

unPB := F[Q:P[B], union(Q)];
!! TunPB := unPB in fn(P[B], P[A]);
!! TunPBinj := injective(unPB);

]; // partition :: [                //   2 cl

  begin("module_TfnE");   //9 Theorems about function existence
// ! TfnE := d ~= {} & A[d, S <: B & nemp(S) ] -> E[f: fn(d,B), A[d, f(^d) in S]];             ///

// ! TfnE1 := d ~= {} & A[d, S <: B & one(S) ] -> E1[f: fn(d,B), A[d, f(^d) in S]];            ///
  
// ! TfnE1a := d ~= {} & A[d, S <: B & one(S) ] -> E1[f: fn(d,B), A[d, A[x:S, f(^d) = x]]];    ///
// ! TfnE1R := d ~= {} & A[d, R[d1,g] <: B & one(R[d1,g]) ] ->
//                               E1[f: fn(d,B), A[d, A[d1, f(^d) = g]]];                       ///
// ! TfnE1R1 := d ~= {} & A[d, R[d1,g]<:B & A[x1:d1, A[x2:d1, Rep(d1,g,x1) = Rep(d1,g,x2)]]] ->
//                       E1[f: fn(d,B), A[d, A[d1, f(^d) = g]]];                              ///
// ! Lfndom := f in fn(A,B) -> dom(f) = A;
// !! TfnAE    := A[x:A, E[y:B, Q]] == E[f:fn(A,B), A[x:A, Sb(Q,y,f(x))]];
// ! TfnAE1   := A[x:A, E1[y:B, Q]] == E1[f:fn(A,B), A[x:A, Sb(Q,y,f(x))]];
// !! TfnAE1   := A[x:A, E1[y:B, Q(x,y)]] -> E1[f:fn(A,B), A[x:A, Q(x,f(x))]]; moved up


// 10 composition 2/10/09 4.5 4.29 12.05 4/28/10 10/8/11

fgcomp := {f,g ; f in FN, g in FN, Axfg := im(g) <: dom(f)};  // was fg1, replaced on fgcomp;
fgcomp :: [
!! L03 := z in dom(g) -> g(z) in dom(f);             // for f(g(x)) in Tcomp;
!! Tcomptf_type := f o g in fn(dom(g), im(f));       // by Tfnin(f o g, dom(g),im(f)); Tcompdom & Staut(im(f)<:im(f)); ///
!! Tcomp := f o g = F[x:dom(g), f(g(x))];            ///
// ! TcompFN := f o g in FN;                        // see Tcompt   // by Tcomp; TFFN;
!! Tcompdom := dom(f o g) = dom(g);                  // by Tcomp; TFdom'
!! Tcompim := im(f o g) <: im(f);                    // is Rel.compim;
// begin("compval"); // wrlist:overflow: z= #16443#16443f(0 1 10459)(#16442g(0 2 10459)(x(0 1 16370))) sizelist= 100
!! Tcompval := A[x:dom(g), (f o g)(x) = f(g(x))];    // by Tcomp: TFred;
!! Tcomp1 := A[x:dom(g), f(g(x)) in im(f)];          ///
!! Tcompinj := injective(f) & injective(g) -> injective(f o g);

]; // fgcomp :: [

// TcompF(f:FN, d::q) := R[d,q] <: dom(f) -> f o F[d, q] = F[d, f(q)];   /// use Tcomp, TFred;
FN :: ! TcompF := A[d, z in dom(f)] -> f o F[d, z] = F[d, f(z)];   /// use Tcomp, TFred; // was FN;

fgh := {f,g,h ; f in FN, g in FN, h in FN, im(h) <: dom(g), im(g) <: dom(f) };

! Tcompass := A[fgh, (f o g) o h = f o (g o h)];                        ///
! Tcompfn :=  f in fn(A,B) & g in fn(C,A) -> f o g in fn(C,B);          ///
fgh :: [
// ! L04 := h in REL;
// ! L05 := g in REL;
// ! L06 := f in REL;
// x_dom_h := {x; x in dom(h)};
!! L07 := (f o g) o h in fn(dom(h), im(f));
!! L08 := x in dom(h) -> h(x) in dom(g) & g(h(x)) in dom(f);
!! L09 := F[d,f] in REL;
!! L10 := dom((f o g) o h) = dom(h);
!! Tcompval3 := A[x:dom(h), ((f o g) o h)(x) = f(g(h(x))) ] ;    ///
]; // fgh :: [

// ! TcompF1(d,q,t,g) := F[d, q, t] o g = F[x:dom(g), Sb(q,d,g(x)), t];  // not used
!! L09 := F[d,f] in REL;
!! L10 := {[a,b]} in REL;                                // same as TRELS := ab in REL; line 2393, not 2394
!! TcompFF := im(F[d,f]) <: d1 -> F[d1,g] o F[d,f] = F[d, Sb(g,d1,f)];   ///
!! TcompS := A[f:FN, A[y:dom(f), f o {[x,y]} = {[x,f(y)]} ]];            ///

// 11 identity function 5/17/10 9.11

// Aset :: begin
// id was defined in Rel.v as:                      id(A:set) := R[a:A, (a,a)];
// !! Axid := id(A) = R[x:A, (x,x)];
!! TidF := id(A) = F[x:A, x];                        // by Axid; TF;
!! Tidt := id(A) in fn(A,A);                         // by TFinfn; TAin;
// !! Tiddom := dom(id(A)) = A;                      // is Tdomid; // see Rel line 2404, not 2405 same as Tdomid above
!! Tidim := im(id(A)) = A;                           // is Timid;  // same as Timid; line 2405, not 2406
!! Tidcompl := A[f:fn(A,B), id(B) o f = f];          ///
!! Tidcompr := A[f:fn(A,B), f o id(A) = f];          ///
!! Tidcomp := id(A) o id(A) = id(A);                 // is Tidcompr(A,idA));
!! Tidval := A[x:A, id(A)(x) = x];                   ///
!! Tideq := A[f:FN, f=id(A) == dom(f)=A & A[x:A, f(x)=x]];

// end; // Aset :: begin

// ! TidU := A[A,B: set, id(A\/B) = id(A) \/ id(B)];                           // see Rel.id
!! TidU1 := All(X,All(Y, Y <: X -> id(Y) \/ id(X--Y) = id(X) ));                             ///
!! TcompidA := All(A, All(B, f in fn(A,B) & g in fn(B,A) -> (f o g = id(B) == A[z:B, f(g(z)) = z]) )); ///

dcl[assoc,any,set,bool];
!! Axassoc := assoc(f,A) == f in fn(A#A,A) & A[x,y,z:A, f(x,f(y,z)) = f(f(x,y),z)];

  begin("module_re");   // 12 function restriction 2/10/09 12.29 3/26/10 4.29 9.02 10/09/11
// dcl[|,set,set,set];            //  Restriction R|A
// ! TRA  := R[d, f] <: B == A[d, f in B];                                     /// was TRI
// ! Tx5 := x in A1 & y in A2 == [x,y] in A1 # A2;
!! Tre1 := f in fn(A,B) & C <: A -> f|C in fn(C,B); 
!! Tre2 := f in fn(A,B) & C <: A -> A[x: C,  (f|C)(x) = f(x)];
!! Tre2a := f in fn(A,B) & C <: A -> A[x: C,  f(x) = (f|C)(x)];
!! Tre3 := g in fn(A#A,A) & f in fn(A,B) & C <: A & g|(C#C) in fn(C#C,C) -> A[x,y:C, (f|C)((g|(C#C))(x,y)) = f(g(x,y))]; "hint"; Tfndp1;
!! Tre4 := f in fn(A#A,A) & B <: A -> (f|(B#B) in fn(B#B,B) == A[x,y:B, f(x,y) in B]);
!! Tre4a := f in fn(A#A,B) & C <: A -> f|(C#C) in fn(C#C,B);  
!! Tre5 := f in fn(A,A) & B <: A -> (f|B in fn(B,B) == A[x:B, f(x) in B]);
!! Tre6 := f in fn(A#A,A) & B <: A -> A[x,y:B, (f|(B#B))(x,y) = f(x,y)]; 
!! Tre6a := f in fn(A#A,A) & B <: A -> A[x,y:B, f(x,y) = (f|(B#B))(x,y) ];  
! Tre7 := f in fn(A#A,A) & B<:A & A[x,y:B, f(x,y) in B] -> f|(B#B) in fn(B#B,B); is Taut((p&q->(r==s))->(p&q&s->r))(Tre4);
!! Treassoc := assoc(f,A) & B<:A & f|(B#B) in fn(B#B,B) -> assoc(f|(B#B),B);      
// !! Tre8 := f in fn(A#A,A) & B<:A & f|(B#B) in fn(B#B,B) & A[x,y,z:A, f(x,f(y,z)) = f(f(x,y),z)] -> 
//             A[x,y,z:B, (f|(B#B))(x,(f|(B#B))(y,z)) = (f|(B#B))((f|(B#B))(x,y),z)]; // A[x,y:B, f(x,y) in B]

FN :: [                        // was FN1 :: [       // FN1 := {f; Axf := f in FN }; #3 FN
!! L0 := z in dom(f) -> f|{z} in REL; 
!! L01 := f in FN;
!! L03 := A <: dom(f) -> f|A in REL;
!! L04 := A <: dom(f) -> dom(f|A) = A;          // was f|A in REL;
!! L05 := x1 in A1 & x2 in A2 -> [x1,x2] in A1#A2;  
!! Treemp := f|{} = {};                                                             // is Trestremp; 
!! TreimS := A[x:dom(f), im(f|{x}) = {f(x)}];  ///                                  // Tindp := [x,y] in X # Y == x in X & y in Y; 
// Tindp1;  // ! Tindp1 := A1#A2 <: C == A[{x1,x2; x1 in A1, x2 in A2}, [x1,x2] in C]; // lot: A[x1:B1,x2:B2, [x1,x2] in dom(f)];

x_B1_y_B2 := {x,y; x in B1, y in B2};
// x_B1_y_B2 :: [
// ! L0_type := [x,y] in B1#B2;
// ! L01 := [x,y] in dom(
// ! Trein2 := B1#B2 <: dom(f) -> (f|(B1#B2) in fn(B1#B2,B) == A[x_B1_y_B2, f([x,y]) in B]);    /// [x,y] in dom(f) <= Tindp1;
// ! Treval2 := B1 # B2 <: dom(f) -> A[x_B1_y_B2, (f|(B1#B2))([x,y]) = f([x,y])];        
// ]; // x_B1_y_B2 :: [

// ! TimreE2 := B1#B2 <: dom(f) -> ( z in im(f|(B1 # B2)) == E[x_B1_y_B2, z = f([x,y]) ] );    ///
// ! TimreA2 := B1#B2 <: dom(f) -> (im(f|(B1#B2)) <: C == A[x_B1_y_B2, f([x,y]) in C] );            ///
!! Trecoll2 := A[a:dom(f), b:dom(f), f|{a,b} = {[a,f(a)], [b,f(b)]}] ;      // byeqA TreF; TFcol2;
!! TimreI := im(f|(A/\B)) = im(f|A) /\ im(f|B); 
!! TimreU := im(f|(A\/B)) = im(f|A) \/ im(f|B);
!! Timreun := im(f|union(X)) = U[S:X, im(f|S)];                                                   ///
!! L02 := f|(B1#B2) in FN;
!! TimreP1 := A[A:P[dom(f)], A in P1[dom(f)] == im(f|A) in P1[im(f)]];         // used in GG1::hom::
!! TreIn2 := f|(A#B) <: f;
!! Tredomf := f|dom(f) = f;  
]; // FN :: [                                                 #3 FN


fgcomp :: [    // 2.Restriction
// !! L04 := z in dom(g) -> g(z) in dom(f);                            /// same as L03 above, line 2468, not 2469;
!! Lcompre1 := A <: dom(g) -> f o (g|A) = F[x:A, f(g(x))];              ///
!! Lcompre2 := A <: dom(g) -> (f o g)|A = F[x:A, f(g(x))];              ///
!! Tcompre := A <: dom(g) -> f o (g|A) = (f o g) | A;                   // is Lcompre1 ! Lcompre2;
// ! Tcompre1 := A <:dom(g) -> (f o g)|A = F[x:A, f(g(x))];            /// same as Lcompre1
]; // fgcomp :: [ 

fA := {f, A; f in FN, A in set, AxfA1 := A <: dom(f) };              //  restriction(see REL), add. theorems

fAB := {f,A,B; f in FN, A in set, B in set, AxfA1 := A <: dom(f), B <: A};
!! Trere := A[fAB, f|A|B = f|B];  
                                                           // |,re := {x,y | (x,y) in R & x in A};
fA :: [
// !        AxfA1;                                         // for f(x) in TreF; rework: goto FA ???
// ! Tx1 := FN <: REL;
// ! Tx2 := F[d,f] in REL;
// ! Tx3 := id(A) in REL;
// ! Tx4 := f in REL;
// ! Tx6 := f|A in REL;
!! Tx5 := B <: dom(f) -> f|B in fn(B,im(f)); 
!! TreF  := f|A = F[x:A, f(x)];                       ///
!! Treim_type := f|A in fn(A, im(f));                // by Tfnin; &(TreF, Tredom, Timre1);
// ! Tret  := f|A in FN;                             // is TFFN;
// !! Tredomf := f|dom(f) = f;                       // moved to FN   // is Trestr7(f);
!! Treim1 := im(f|A) <: im(f);                       // is Trestrim1;
!! Tredom := dom(f|A) = A;                           // is TFdom;
!! Timre := im(f|A) = R[x:A, f(x)];                  // byeq Def(f|A), TimF, Tredom;
// !! Timredom := im(f|dom(f)) = im(f);              //    is Trestrim2; moved to FN;
!! L0 := R[d,g] <: dom(f) == A[d,g in dom(f)];       // TRA  := R[d, f] <: B == A[d, f in B]; 
// !! TimreR := R[d,g] <: dom(f) -> im(f|R[d,g]) = R[d,f(g)]; // R[d,g] <: dom(f) == A[d,g in dom(f)]; So f(g) is a wft; ??? not checked 01.31.23
                
// !! Timre0 := im(f|A) <: im(f);                             // by Timre, Axim; is TRM; same as Treim1;
!! Treval := A[x:A, (f|A)(x) = f(x)];                      // is TFred;
!! Treim2 := A[x:A, f(x) in im(f|A)];                      // (f|A)(x) in im(f|A); is Timval; by Treval;
// ! Treim2 := A[x:dom(f), f(x) in im(f|A) == x in A];     // wrong! f = F[x:0..pi, sin(x)], A=0..pi/4,x=pi/2 + pi/4
// ! Treim3 := {x; x:dom(f), f(x) in im(f|A)} = A};        // wrong! see above!
// ! Trere := All(B, B<:A -> (f|A)|B = f|B);                 // byA Tredom; is Axrefleq;
!! TimreE := All(y,y in im(f|A) == E[x:A, f(x) = y]);      //  byeq Def(f|A), TimF, TRin;
!! TimreA := All(B, im(f|A) <: B == A[x:A, f(x) in B]);    // byeq Timre, TRI;
!! Trein := A[B:set, f|A in fn(A,B) == A[x:A, f(x) in B]]; // byA TreF; TFinfn(B); 
!! Timrenemp := im(f|A) ~= {} == A ~= {};                  // is Timemp ! Tredom;
!! TreUf := f = f|A \/ f|(dom(f)--A);                      // is TrestrD;
!! Tcompidre := f o id(A) = f|A;                           // is Trestr9;
!! Tinre := [a,b] in f|A == a in A & b = f(a);             // byeq TreF, TFin;
// !! L01 := A <: dom(f);                                     // Axfa1 is too far;                                            
!! TRre := R[x:A, f(x)] = R[x:A, (f|A)(x)];                // by Treval; Axrefl;
!! TreIn := f|A <: f;

]; // end fA :: [

f_FN_A_P_dom_f_x_A := {f,A,x; f in FN, A in P[dom(f)], x in A};
f_FN_A_P_dom_f_x_A :: [ !! L0 := x in dom(f|A); ];
!! TrevalA := A[f_FN_A_P_dom_f_x_A, (f|A)(x) = f(x)];

// ! TreFA  := A[f:FN, A:set, A <: dom(f) -> f|A = F[x:A, f(x)];                           
!! Tidre := All(B, B <: D & id(D)|B = id(B));              ///

// ! TfnREL := fn(A,B) <: REL;
!! TREL3 := f in REL -> f|C in REL;                        // line 2524, correct !!!
!! Timre2  := f in fn(A,B) & C <: A -> im(f|C) <: B;       ///

!! TFre := B <: A -> F[x:A, G(x)] | B = F[x:B, G(x)];                      ///
!! TFre2 := B1<:A1 & B2<:A2-> F[x:A1,y:A2, G(x,y)] | (B1#B2) = F[x:B1, y:B2, G(x,y)];

// ! TimreU := A[f,g: FN, A:< dom(f), B:< dom(g), f NI g -> (f\/g)|(A\/B) = (f|A)\/(f|B); not used

fg :: [
// !! L0_type := f\/g in REL;                               // same as TfgU_type above, line 2533, not 2534;
!! TreU1 := f\/g in FN -> (f\/g)|dom(f) = f;                ///
!! TreU2 := f\/g in FN -> (f\/g)|dom(g) = g;                ///   
!! Treeq := A <: dom(f) & B <: dom(g) & f|A = g|B -> A = B;   ///
!! Tfneqre := A <: dom(f) & A <: dom(g) -> (f|A = g|A == A[x:A, f(x) = g(x)]); ///
!! Treid:= D <: dom(g) & g|D = id(D) -> (f o g)|D = f|D;    /// was with no theorem name
!! TdomIreU := f|(K1 := dom(f)/\dom(g)) = g|K1 -> f\/g in FN; ///   was TFN4
]; // fg :: [

!! Tfneq := A[f,g: FN, f=g == dom(f)=dom(g) & A[x:dom(f), f(x)=g(x)]];             //   #4 FN

// begin("module_Df");   // 14 Difference (for functions) 2/10/09 12.29 3/26/10 4.30

// dcl[\,FN,set,FN];     // Difference (for functions) f\A

fA :: [                                     // fA := {f, A; f in FN, AxfA1 := A <: dom(f) };
!! AxDf := f\A = f|(dom(f)--A);
!! TDfdom := dom(f\A) = dom(f)--A;                              // is Tredom;
!! TDfim := im(f\A) <: im(f);                                   // is Timre1;
!! TDfin := [a,b] in f\A == [a,b] in f & a nin A;               ///
!! TDf_type := f\A in fn(dom(f)--A, im(f));                     // is Treim;
!! L02 := dom(f)--A <: dom(f);
!! TDfval := A[x: dom(f)--A, (f\A)(x) = f(x)];                  // is Treval;
!! TDfreemp := dom((f|A) \ A) = {};                             // byeq TDfdom, Tredom, TDemp1;                        
!! TDfre := All(A, A<:dom(f) -> f = f\A \/ f|A);                // byA AxDf; TreUf; 
]; // fA :: [

FN :: [                // FN1 :: [                 #5 FN      // FN := {f ; AxFN0 := f in REL, AxFN1 := func(f)}; 
!! Timredom := im(f|dom(f)) = im(f);                       //    is Trestrim2;
!! TFN1 := A[x:dom(f), Exist1(y, [x,y] in f)];                      // is AxFN1;
!! TFN6 := All(x,All(y,All(y1, [x,y] in f & [x,y1] in f -> y = y1))); // is Tfunc1 ! AxFN1;
!! TFNself := f in FN;                                              // by Axab; AxFN0 & AxFN1;
// exts := F[X:P[dom(f)], R[x:X, f(x)]];
// !! Texts := exts(f) in fn(P[dom(f)], P[im(f)]);

!! TDfdom1 := f\dom(f) = {};                                    // byeq AxDf, TDemp1, Treemp;
!! TDf1 := A[x:dom(f), f\{x} = f--{[x,f(x)]}];                  ///
!! TDf2 := A[x:dom(f), f = {[x,f(x)]} \/ f\{x}];                // by TDf1; TvalD; 
!! TDfemp := f\{} = f;                                          // by AxDf,TDemp,Tredomf;
!! TDfDf := (f\A)\B = f\(A\/B);                                 ///  
]; // FN1 :: [                                                  #5 FN

!! TDfid := All(A, All(B, id(A)\B = id(A--B) ));                // byeqA AxDf,Tdomid,Trestr11,TID; 
!! TDfid1 := id(A--B)\C = id(A--(B\/C));                        // byeqA AxDf,Tdomid,TDD;

fg :: [
// TfgdomNIU;                         // TfgdomNIU := dom(f) NI dom(f) -> f\/g in FN; for checking TDfU
!! TDfU := A<:dom(f) & B<:dom(g) & dom(f) NI dom(g) -> (f\/g)\(A\/B) = f\A \/ g\B; ///
!! TDfU1 := A<:dom(f) & dom(f) NI dom(g) -> (f\/g)\A = f\A \/ g; /// precedence of "\" is the same as of "|"
];  // fg :: [

!! Axinj := A[f:FN, injective(f) == A[x1,x2: dom(f), f(x1) = f(x2) -> x1 = x2]];  // added 8.
// ! Tinj0 := A[f:FN, injective(f) ->  A[x1,x2: dom(f), x1 = x2 == f(x1) = f(x2)]];   
!! Tinj0 := A[f:FN, injective(f) ==   A[x1,x2: dom(f), f(x1) = f(x2) == x1=x2]];

FN :: [ // FN1 :: [                                                 #6 FN
!! L06 := A <: dom(f) -> f|A in FN;                                          
// injective := A[x1,x2: dom(f), f(x1) = f(x2) -> x1 = x2];
!! Axinj := injective(f) == A[x1,x2: dom(f), f(x1) = f(x2) -> x1 = x2];    // by Taut((p==q)==(~p == ~q)); 
!! TinjN := ~injective(f) == E[x1,x2: dom(f), x1 ~= x2 & f(x1) ~= f(x2)];    
!! Tinj := injective == A[x1,x2: dom(f),  x1 ~= x2 -> f(x1) ~= f(x2)];     // is Axinj ! CP; // ContraPosition
!! TinjreA := A <: dom(f) -> (injective(f|A) == A[x1,x2:A, f(x1) = f(x2) -> x1 = x2]); // byeq Axinj(f|A), TFred;
!! Tinjre := A <: dom(f) & injective(f) -> injective(f|A);           // byA Axinj(f),TinjreA; TAIn1;
!! TinjAE1 := injective == A[y:im(f), E1[x:dom(f), y = f(x)]];       // by TE1; TimAE & Axinj;
// TFNemp; // ! TFNemp := {} in FN; // ! Tinjab := injective == {x:dom(f) | A[z:dom(f), z ~= x -> f(z) ~= f(x)} = dom(f);
! Tinjfunc := injective(f) == func(inv(f));                   ///
! Tinjemp := injective({});                                   // by TinjAE1,Timemp; TAemp;
]; // FN :: [                                                    #6 FN

// IFN := FN && (Axinj1 := injective);

// IFN := {f ; AxIFN0 := f in FN, Axinj1 := injective(f)};
IFN := FN && (Axinj1 := injective(f));

// !! AxIFN := IFN = FN && injective;                          //  by Axsc;
// ! TIFN := IFN = {f; f in FN , injective(f)};
!! TIFNin := f in IFN == f in FN & injective(f);               // is Axab;
!! TIFNinA := A[f: FN, f in IFN == injective(f)];              // is TAscin; by Axinj;
!! TIFNinAA := A[f: FN, f in IFN == A[x1, x2: dom(f), f(x1) = f(x2) -> x1 = x2]];
!! TIFNt := IFN <: FN;                                         // is TscIn;
!! TIFNt1 := IFN <: REL;
!! TIFNU := A[f,g: IFN, dom(f) NI dom(g) & im(f) NI im(g) -> f\/g in IFN]; ///

IFN :: [           
var A, P[dom(f)];
!! Tinj0 := f|A in IFN;
!! Tinj01 := f\A in IFN;
// !! Tinj0a := f|A in FN;        // A <: dom(f) -> f|A in FN; ??? f|A is a relation, and this rel is a function;
!! Tinj01a := f\A in FN;
!! TfA_type := f|A in fn(A, im(f|A));
!! Tinj := A[x1,x2: dom(f), f(x1)=f(x2) -> x1=x2];
!! Tinj1 := A[x1,x2: dom(f), x1 ~= x2 -> f(x1) ~= f(x2)];      // is Axinj ! Contraposition;
!! LinjIN := A[A1,A2 : P[dom(f)], A1 IN A2 == im(f|A1) IN im(f|A2)];  ///
!! LinjNI := A[A1,A2 : P[dom(f)], A1 NI A2 == im(f|A1) NI im(f|A2)]; // is LinjIN ! TINNI;     
!! Tinjre1 := injective(f|A);                                      // isA Tinjre(A) ! Axinj1; // A[A: P[dom(f)], 
!! Tifnre := A[A: P[dom(f)], f|A in ifn(A, im(f|A))];             // byA Tifnin; Treim & Tinjre1;
!! TinjNI1 := A[A: P[dom(f)], im(f\A) NI im(f|A)];                // is LinjNI(dom(f)--A, A) ! TNI9;

// ! Tinj2 := inv(f) in IFN;                                  // not used, see Tinvinj
// ! Tinj3 := A[a:dom(f), im(f\{inv(f)(a)}) = im(f)--{a}];    // not used;
]; // IFN :: [

!! Tinjcomp := A[f,g: IFN, im(g) <: dom(f) -> f o g in IFN];   ///
!! TIFNre := A[f: IFN, A: P[dom(f)], f|A in IFN];              // byA TIFNin; Tret & Tinjre;
!! TIFNeq  := A[f: IFN, x,y: dom(f), x = y == f(x) = f(y)];   ///

// ABset :: begin // ifn(A,B) := fn(A,B) && injective(f);

dcl[ifn, set,set, set]; 
// !! Axifn := ifn(A,B) = fn(A,B) && injective(f);                     by Axsc;
// ! TifnFN := ifn(A,B) <: FN;                                               
!! Tifn := ifn(A,B) = {f; f in fn(A,B) & injective(f)};
!! Tifnin := f in ifn(A,B) == f in fn(A,B) & injective(f);     // is Axab;
!! Tifnin1 := f in ifn(A,B) == f in fn(A,B) & f in IFN; /// by TIFNin, Absorb(f in fn(A,B) -> f in FN);
!! Tifnfn := ifn(A,B) <: fn(A,B);                             // is TscIn;
!! TifnInFN := ifn(A,B) <: IFN;                                // is TscInM;
!! Tifnemp1 := All(B, ifn({},B) = {{}});                      // byA Tifn,Tinjemp,Tabtrue;                        
!! Tifnemp := ifn({},{}) = {{}};                              // is Tifnemp1({});

// end; // ABset :: begin
!! ab11 in FN;  !! abba in FN;
!! Tinjid := All(A, injective(id(A)));                       ///
!! Tinjid1 := All(A, id(A) in ifn(A,A));                     // by Tifnin; Tidt & Tinjid;
!! Tinjab11 := injective(ab11) == (a=a1 == b=b1);
!! Tinjabba := injective(abba);

begin("module_sfn");   // 12 surjective functions 4/6/09 5.6   10/10/11
dcl[sfn,set,set, set];

// sfn := fn(A,B) && im(f) = B;                 // "surjective" is not used!
// !! Axsfn := sfn(A,B) = fn(A,B) && im(f) = B;                      // by Axsc;
!! Tsfn := sfn(A,B) = {f; f in fn(A,B); im(f) = B};    
!! Tsfnin := f in sfn(A,B) == f in fn(A,B) & im(f) = B;    // is Axab;
!! Tsfnin1 := f in sfn(A,B) == f in FN & dom(f) = A & im(f) = B;      /// 
!! TsfnIn:= sfn(A,B) <: fn(A,B);                                   // is TscIn;
!! Tsfnim := A[f: sfn(A, B), im(f) = B];                           /// use Tsfnin; 
!! Tsfndomim := A[f:FN, f in sfn(dom(f), im(f))];                  // byeq Tsfnin1, Axrefleq;
!! TsfnAE := A[f: sfn(A,B), A[y:B, E[x:A, y = f(x)]]];             ///
!! Tsfncomp := f in sfn(B,C) & g in sfn(A,B) -> f o g in sfn(A,C);           ///
!! Tsfnid := id(A) in sfn(A, A);                                                  ///
!! Tcompidsfn := A[f: fn(X,Y), g: fn(Y,X), f o g = id(Y) -> f in sfn(X,Y) & g in ifn(Y,X)]; ///

begin("module bfn");   // 13 bijective functions 4/6/09 5/10/10 9.14
dcl[bfn,set,set, set];
// bfn(A,B) := {f:ifn(A,B) | im(f) = B};
! Lbfn0 := ifn(A,B) <: REL;
! Lbfn01 := sfn(A,B) <: FN;
! Lbfn02 := fn(X,Y) <: REL;   // change TfnREL !!!
!! Axbfn := bfn(A, B) = {f; f in ifn(A,B), Axbfnim := im(f) = B};
!! Tbfnt := bfn(A,B) <: ifn(A,B);                                         // is TabIn;
!! Tbfnfn := bfn(A,B) <: fn(A,B);                                         // is Tbfnt ! Tifnfn;
!! Tbfnin := f in bfn(A,B) == f in ifn(A,B) & im(f) = B;                  // is Axab; by Tifnin;
!! Tbfnin1 := f in bfn(A,B) == f in fn(A,B) & injective(f) & im(f) = B;
!! Tbfnin2 := f in bfn(A,B) == f in sfn(A,B) & injective(f);              // by Tsfnin; Tbfnin1;
!! Tbfnim := f in bfn(A,B) -> im(f) = B;
!! Tbfndom := f in bfn(A,B) -> dom(f) = A;
!! Tbfninv := f in bfn(A,B) -> inv(f) in bfn(B,A);
// FN1 :: ! Tbfnin3 := f in bfn(A,B) == injective(f) & dom(f) = A & im(f) = B; 
//     byeq Tbfnin1, Tfnin, Absorb(im(f)=B -> im(f)<:B); 
! Tbfnin4 := f in bfn(A,B) == f in ifn(A,B) & f in sfn(A,B); 
//     byeq Tbfnin, Absorb(f in ifn(A,B) -> f in fn(A,B)), Tsfnin;
! Tbfnin5 := f in bfn(A,B) == f in IFN & f in sfn(A,B);
//     byeq Tbfnin4, Tifnin1, Absorb(f in sfn(A,B) -> f in fn(A,B));

! Tbfncomp := f in bfn(A,B) & g in bfn(C,A) -> f o g in bfn(C, B);       ///
! Tbfncomp1 := f in bfn(A, A) & g in bfn(A,A) -> f o g in bfn(A,A);      ///
! Tbfnre := f in bfn(A,B) & A1 <: A -> f|A1 in bfn(A1, im(f|A1));        ///
IFN :: ! Tbfnre1 := A <: dom(f) -> f|A in bfn(A, im(f|A));          // by Axbfn; Tifnre & Tbfnin3; 
FN :: ! Tbfn1:= injective(f) -> f in bfn(dom(f), im(f));                  /// was FN
! Tbfn2 := f in fn(A1,B1) & g in fn(B1,A1) & g o f = id(A1) & f o g = id(B1) ->
                                    f in bfn(A1,B1) & g in bfn(B1,A1);        ///
! Tbfn2a := A[A,B: set, f: fn(A,B), g: fn(B,A), 
       A[x:A, g(f(x)) = x] & A[y:B, f(g(y)) = y] -> f in bfn(A,B) & g in bfn(B,A)];    ///
// ! Tbfnt(A,B: set) := bfn(A, B) <: BFN; use AxextA, Tbfnin, TBFNin, TfnFN, Taut; not true!
!! TbfnA := f in bfn(A,B) -> A[x1,x2:A, f(x1)=f(x2) == x1=x2];
!! Tbfninv4 := f in bfn(A,B) & x in A -> inv(f)(f(x)) = x;
! Tbfnid := A[A:set, id(A) in bfn(A,A)];       // byA Tbfnin4; Tinjid1 & Tsfnid;
// ! Tbfnemp1 := A[B, bfn({},B) = {{}}];                                  wrong !!!                        
! Tbfnemp := bfn({},{}) = {{}};                                          // byeq Axbfn,Tifnemp,Timemp,Tabtrue;

begin("module qinv");   // 15 quasiinverse 4/7/09 5/12/10 15
// dcl[qinv,FN,FN];
FN :: [ 
!! LqinvF := A[y:im(f), {x; x in dom(f), f(x) = y} in P[dom(f)] ]; //  by TinP; TabIn;
qinv := F[y:im(f), {x: dom(f); f(x) = y} ];                        // quasiinverse
!! Tqinv_type := qinv in fn(im(f), P[dom(f)]);
!! Tqinvdom := dom(qinv) = im(f);                                  // is TFdom;
!! Tqinv := A[y:im(f), qinv(y) = {x: dom(f); f(x) = y} ];          // is TFred;
!! Tqinv1 := A[z:dom(f), qinv(f(z)) = {x; x in dom(f) & f(x) = f(z)} ];  // use Tqinv
!! Tqinvin := A[y: im(f), x in qinv(y) == x in dom(f) & f(x) = y];
!! Lqinvin0 := x in dom(f) -> f(x) in dom(qinv);                 
!! Tqinvin1 := A[y:im(f), x:dom(f), x in qinv(y) == f(x) = y ]; //  byeqA Tqinvin, x in dom;
!! Tqinvin2 := A[x:dom(f), x in qinv(f(x))];                    // is Tqinvin1;
!! Tqinvdom1 := A[y:im(f), qinv(y) <: dom(f)];                  // is TabIn;
!! TqinvE := A[y:im(f), nemp(qinv(y))];                         // by Tqinv(y), -TEab; TimAE;

// ! TqinvE := A[y:im, nemp(qinv(y)) == E[x:dom, f(x) = y]];    // byeqA Tqinv, TEab;
!! TqinvE1 := A[y:im(f), one(qinv(y)) == E1[x:dom(f), f(x) = y]];   // byeqA Tqinv, TE1ab;
!! Tqinvinj := injective(qinv);                                 // by TinjAE1;           ///
!! Tqinvinj1 := injective == A[y:im(f), one(qinv(y)) ];         // by TqinvE1,;TinjAE1;
// !! Tqinvbfn := qinv in bfn(im(f),part);

part := im(qinv);
!! Axpart := part = im(qinv);                                                                // #7 FN
!! TpartR := part = R[y:im(f), {x; x in dom(f) & f(x) = y} ];       // partition := {A, B ; Axprt1 := A=union(B); Axprt2 := {} nin B;
!! TpartR1 := part = R[z:dom(f), {x; x in dom(f) & f(x) = f(z)} ];  //               Axprt3 := A[Q1Q2_B, Q1 ~= Q2 -> Q1/\Q2 = {} ] };

!! Tqinvbfn := qinv in bfn(im(f), part);                           //  by Tbfnin2(qinv); Tsfndomim(qinv) & Tqinvinj;
!! TqinvU := union(part) = dom(f);                                 ///
!! Tqinvemp := {} nin part;                                        // by Axim, TRnin; TqinvE;
!! TqinvA := A[Q1,Q2: part, Q1/\Q2 ~= {} -> Q1 = Q2];              ///

Mpart := [dom(f), part];
!! Tqinvprt := Mpart in partition;                                 // by Tprtin; &(TqinvU,Tqinvemp,TqinvA);

puns := F[Q:P[part], union(Q)];                                    // partition :: unPB := F[Q:P[B], union(Q)];
! Tpuns_type := puns in fn(P[part], P[dom(f)]);  is TunPB.Mpart;   // partition :: !! TunPB := unPB in fn(P[B], P[A]);
! Tpunsinj := injective(puns);                   is TunPBinj.Mpart;
! Tpunsdom := dom(puns) = P[part];               is Tfndom(Tpuns_type);
! Tpunsim := im(puns) <: P[dom(f)];              is Tfnim(Tpuns_type);  // !! Tfnim := f in fn(A,B) -> im(f) <: B;

// ! Tsfninj := E[g:ifn(im(f),dom(f)), f o g = id(im(f)];      // not used, g = F[y:im(f), arb(qinv(y))];
// ! TsfninjA := E[g:ifn(B,A), A[z:B, f o g = id(B)]];          // not used

]; // FN :: [                                                   #7 FN

dcl[afn,set, set];
!! Axafn := afn(A) = bfn(A,A);

begin("module inv");   // 19 inverse function 10/27/08 2/9/09 3/24/10 5.19 9.11
IFN :: [
x_dom_f := {x; x in dom(f) };  var y, im(f); // var A, P[dom(f)];
!! L0 := dom(qinv) = im(f);   // better: use IFN <: FN: Tqinvdom from FN;
!! L01 := A[x_dom_f, f(x) in im(f)];
!! L01_type := the(qinv(y)) in dom(f);           // !! L01a := A[y:im(f), the(qinv(y)) in dom(f)];
!! Tinv1  := A[y:im(f), one(qinv(y))];           // is Tqinvinj1 ! injective;  by TqinvE1;
!! TinvE1 := A[y:im(f), E1[x:dom(f), y = f(x)]];
!! TIFN1 := A[x_dom_f, the(qinv(f(x))) = x];     // isA TT3(Tinv1 & Tqinvin2); // ! Tqinvin2 := A[x:dom(f), x in qinv(f(x))];
!! TIFN2 := f(the(qinv(y))) = y;                 // !! TIFN2 := A[y:im(f), f(the(qinv(y))) = y];          /// use ProofA, TimE, TIFN1;
!! LinvF  := A[y:im(f), the(qinv(y)) in dom(f)];              /// use TTin, Tqinvdom1;
!! Lf_type := inv(f) in fn(im(f),dom(f));
!! L03 := IFN <: REL;
!! L04 := inv(f|A) in FN;
!! L05 := im(f|A) <: im(f);
!! L06 := g in bfn(A,A) & h in bfn(A,A) -> inv(g) o h o g in bfn(A,A);
// ! L07 := dom(inv(f)) = im(f);
//  inv := F[y:im(f), the(qinv(y))];
!! Tinv := A[y:im(f), inv(f)(y) = the(qinv(y))];              // is TFred;
!! Tinvt := inv in fn(im(f), dom(f));                       // is TFt;
!! Tinv2 := A[y:im(f), inv(f)(y) in dom(f)];                // by TFred; LinvF;
!! Tinvdom := dom(inv(f)) = im(f);                    // is Tfndom;
!! Tinvim  := im(inv(f)) = dom(f);                    ///
!! Tinvl := A[x_dom_f, inv(f)(f(x)) = x];            // by TFred; TIFN1;
!! Tinvr := A[y:im(f), f(inv(f)(y)) = y];             // by TFred; TIFN2; 
!! Tinv3 := A[x:dom(f), y:im(f), inv(f)(y) = x == y = f(x)]; ///
// ! Tinv3a := A[x:dom, y:im, inv(f)(y) ~= x == y ~= f(x)];  // -- not used
!! Tinvinj := injective(inv(f));                      ///
!! Tinvinv := inv(inv(f)) = f;                        ///
!! TinvA_type := inv(f|A) in fn(im(f|A), A);            // moved up to first IFN:
!! Tinvre := All(A, A <: dom(f) -> inv(f|A) = inv(f)|im(f|A) );        ///
!! Tinvredom := A <: dom(f) -> dom(inv(f|A)) = im(f|A) ;               ///
!! Tinvreval := y1 in im(f|A) -> inv(f|A)(y1) = inv(f)(y1);            // !! Tinvreval := A <: dom(f) & y in im(f|A) -> inv(f|A)(y) = inv(f)(y); ///
!! Tinvcompl := inv(f) o f = id(dom(f));                               ///
!! Tinvcompr := f o inv(f) = id(im(f));                                ///
!! Tinveq := inv(f) = f -> f o f = id(dom(f));                         ///
!! Tinv4 := A[g:FN, dom(f) <: dom(g) -> dom(g o inv(f)) = im(f)]; // byeqA Tcompdom, Tinvdom;
!! Tinv5 := A[g:FN, B : P[dom(f)], B <: dom(g) -> 
                     (g o inv(f)) | im(f|B) = (g|B) o inv(f|B)];  ///
// !! L08 := A in P[B] == A <: B;                                    // AxP
// ! L09 := g in FN & B <: dom(f) & B <: dom(g) -> dom(g o inv(f|B)) = im(f|B);
// ! L09 := g in FN & B <: dom(f) & B <: dom(g) -> g o inv(f|B) in fn(im(f|B),im(g));
// ! L10 := b in B & B <: dom(f) -> f(b) in im(f|B);
// ! Tinv6   := A[g:FN, B: P[dom(g)], b:B, B <: dom(f) -> (g o inv(f|B))(f(b)) = g(b)];   ///
gBb := {g,B,b; g in FN; B <: dom(g); b in B; B <: dom(f); };
gBb :: [
!! L0 := b in dom(f);
!! LO1 := dom(g o inv(f|B)) = im(f|B);
!! L02 := g o inv(f|B) in fn(im(f|B),im(g));
!! L03 := f(b) in im(f|B);
!! L04 := b in dom(g);
!! Tinv6 := (g o inv(f|B))(f(b)) = g(b);
];

!! Linvbfn1 := f in bfn(A,B) -> inv(f) in bfn(B, A);              ///
// ! Linvbfn2 := A[A,B:set, f in bfn(A,B) -> im(f) = B];          // not used, see  Axbfnim;
!! Linvbfn := inv(f) in bfn(im(f), dom(f));                       ///
!! Tinvbfn := f in bfn(A, B) == inv(f) in bfn(B, A);              ///
!! Tinvret := A <: dom(f) -> inv(f|A) in bfn(im(f|A), A);         // is Tinvbfn ! Tbfnre1;
!! Tinvbfn1 := f in bfn(S, S) == inv(f) in bfn(S, S);             // is Tinvbfn(S,S);   
!! Tinv10 := A[y:im(f), inv(f)(y) in dom(f)];                     // is Tfnval;
!! Tinv11 := A <: dom(f) & y in im(f|A) -> inv(f)(y) in A;        ///
!! Tinvcomp := A[g: FN, dom(g) <: im(f) -> (g o f) o inv(f) = g];
                                                       // byeq Tcompass, Tinvcompr, Tidcompr;
!! Tinvcomp1 := A[g: FN, dom(f) <: im(g) -> inv(f) o (f o g) = g];   
                                                       // byeq Tcompass, Tinvcompl, Tidcompl;
!! Tinvreim := A <: dom(f) -> im(inv(f|A)) = A;        // is Tinvret ! Axbfnim; by Tinvre;
!! Tinvreim1 := A <: dom(f) -> im(inv(f)|im(f|A)) = A;
!! Tinvreim2 := A[y:im(f), im(f|{inv(f)(y)}) = {y}];               // byeq TreimS, Tinvr;
!! TinjNI := A[A1,A2:dom(f), A1 NI A2 == im(f|A1) NI im(f|A2)];    ///
!! TinjimDf := A <: dom(f) -> im(f\A) = im(f) -- im(f|A);          ///
!! TinvimDf := A[x: im(f), im(f\{inv(f)(x)}) = im(f)--{x}];        ///
!! TinvimDf2 := A[x,y: im(f), im(f\{inv(f)(x),inv(f)(y)}) = im(f)--{x,y}]; ///

]; // IFN :: [

!! Tinv12 := f in fn(A,B) & g in fn(A,B) & h in bfn(B,C) -> (f = g == h o f = h o g);           ///
!! Tinv13 := A[A,B: set, f: bfn(A,B), g: bfn(B,A), g o f = id(A) -> g = inv(f) & f = inv(g)]; ///
!! Tinv13a := A[A: set, f,g: bfn(A,A), g o f = id(A) -> g = inv(f) & f = inv(g)];               // isA Tinv13(A,A);
!! Tbfninv0 := A[A,B: set, f: fn(A,B), g: fn(B,A), g o f = id(A) & f o g = id(B) ->
               f in bfn(A,B) & g in bfn(B, A) & inv(f) = g & inv(g) = f ];                   ///

!! Tbfninv1 := A[A,B: set, f: fn(A,B), g: fn(B,A), A[x:A, g(f(x))=x] & A[y:B, f(g(y))=y] ->
                f in bfn(A,B) & g in bfn(B, A) & inv(f) = g & inv(g) = f ];                   ///
!! L11 := g in bfn(A,A) & h in bfn(A,A) -> inv(g) o h o g in bfn(A,A);
// ! L12 := g in bfn(A,A) & h in bfn(A,A) -> dom(inv(g) o h o g) = dom(g);
!! Tbfninv2 := A[A:set, g,h:bfn(A,A),x:A, (inv(g) o h o g)(x) = x == h(g(x)) = g(x)];             ///
// ! TinvF := injective(F[x:A, q(x)]) -> A[x:A, inv(F[x:A, q(x)])(q(x)) = x];        //  not used
!! Tbfnre1 := A[A,B: set, f: bfn(A,A), B <: A & im(f|B) <: B & im(inv(f)|B) <: B -> im(f|B) = B]; ///

dcl[exts,FN,FN];
!! Axexts := A[f:FN, exts(f) = F[X:P[dom(f)], R[x:X, f(x)]]];
!! Textsbfn := A[f:FN, f in bfn(A,B) == exts(f) in bfn(P[A],P[B])];
!! Lbfninv := f in bfn(A, B) -> inv(f) in bfn(B, A);

FN :: [                                                              // #8 FN
!! Tbfninv3 := A[t:set, g: bfn(im(f), t), A[x:dom(f), f(x) = inv(g)(g(f(x)))]];  // was g in bfn(im(f),t) -> ... 
// !! Tbfninv4 := g in bfn(im(f), t) -> A[x:dom(f), f(x) = inv(g)(g(f(x) ) )];  // WRONG : using free vars is dangerous: type(inv(g)) is kept !!!
// !! Axqinv := qinv = F[y:im(f), {x; x in dom(f), y = f(x)} ];
// part := im(qinv);                                                  
// !! TpartR := part = R[y:im(f), {x; x in dom(f), y = f(x)} ];      // partition := {A, B ; Axprt1 := A=union(B); Axprt2 := {} nin B;
// !! Tpart := [dom(f), part] in partition;                          // Axprt3 := A[Q1Q2_B, Q1 ~= Q2 -> Q1/\Q2 = {} ] };
// !! Tqinvbfn := qinv in bfn(im(f),part);
// !! Tqinvin := A[y: im(f), x in qinv(y) == x in dom(f) & y = f(x)];

iq := inv(qinv);
!! Tiq := iq in bfn(im(qinv), im(f));                   // part := im(qinv);

qinvs := exts(qinv); 

! Tqinvs := qinvs = F[Y:P[im(f)], R[y:Y, qinv(y)]];                  // {x; x in dom(f), f(x) in Y} ];
 EqProof Tqinvs;
F1 := exts(qinv);                                by Axexts;
F2 := F[X:P[dom(qinv)], R[x:X, qinv(x)]];        by Tqinvdom;     // !! Tqinvdom := dom(qinv) = im(f);
F3 := F[X:P[im(f)], R[x:X, qinv(x)]];
 end EqProof Tqinvs;
                                                 // !! Textsbfn := A[f:FN, f in bfn(A,B) == exts(f) in bfn(P[A],P[B])];
! Lqinvs1 := bfn(P[im(f)], P[part]) <: fn(P[im(f)], P[part]);  is Tbfnfn;               // !! Tbfnfn := bfn(A,B) <: fn(A,B);
! Tqinvsbfn := qinvs in bfn(P[im(f)], P[part]);                by -Textsbfn(qinv); Tqinvbfn;         
Tqinvsbfn; by Tbfnin1; Tqinvs_type & Tqinvsinj &  Lqinvsim; // !! Tbfnin1 := f in bfn(A,B) == f in fn(A,B) & injective(f) & im(f) = B;
! Tqinvs_type := qinvs in fn(P[im(f)], P[part]);   // is TinIn(Tqinvsbfn & Lqinvs1);    // ! TinIn := x in X2 & X2 <: Y2 -> x in Y2;
! Tqinvsinj := injective(qinvs);
! Lqinvsim := im(qinvs) = P[part];
! Lqinvsdom := dom(qinvs) = P[im(f)];       is Tfndom(Tqinvs_type);

! Tqinvsun := A[Y: P[im(f)], union(qinvs(Y)) = {x:dom(f); f(x) in Y } ];
 Proof Tqinvsun;
F0 := Y in P[im(f)];                        assume;
G0 := union(qinvs(Y)) = {x:dom(f); f(x) in Y}; by AxextA;
G1 := All(x, x in union(qinvs(Y)) == x in {x:dom(f); f(x) in Y});
  EqProof G1;
assume(x);
H0 := x in {x:dom(f); f(x) in Y} == x in dom(f) & f(x) in Y; is Axab;
H1 := x in union(qinvs(Y));                 by Tqinvs,Red;  // make RedF ???
H2 := x in union(R[y:Y, qinv(y)]);          by -TUunion;    // !! TUunion := U[d,w] = union(R[d,w]); 
H3 := x in U[y:Y, qinv(y)];                 by TUin;        // ! TUin := x in U[d, w] == E[d, x in w]; 
H4 := E[y:Y, x in qinv(y)];                 by Tqinvin;     // !! Tqinvin := A[y: im(f), x in qinv(y) == x in dom(f) & f(x) = y]
H5 := E[y:Y, x in dom(f) & f(x) = y];       by TEelim3;     // !! TEelim3 := E[x:A, P(x) & f=x] == P(f) & f in A; 
H6 := x in dom(f) & f(x) in Y;              by -H0;  // by -Axab;
H7 := x in {x:dom(f); f(x) in Y};
  end EqProof G1;
 end Proof Tqinvsun;

// unPB := F[Q:P[B], union(Q)];
// !! TunPB := unPB in fn(P[B], P[A]);
// !! TunPBinj := injective(unPB);

// gs := im(puns);
// ! Tpunsbfn := puns in bfn(P[part], gs);

// ! TgsR  := gs = R[Q:P[part], union(Q)];

preim := F[Y: P[im(f)], {x: dom(f); f(x) in Y} ];
! Lpreim := A[Y: P[im(f)], {x: dom(f); f(x) in Y} in P[dom(f)] ]; is TabinP; // !! TabinP := {x:t; Q(x)} in P[t];
! Tpreim := preim in fn(P[im(f)], P[dom(f)]);                by TFinfn1; Lpreim;            // FAGx := F[x:A, G(x)];
!! Lpreim1 := A[Y: P[im(f)], Y in P1[im(f)] == preim(Y) in P1[dom(f)]];
!! Lpreim2 := A[x:dom(f),Y:P[im(f)], x in preim(Y) == f(x) in Y];  
! Lpreimdom := dom(preim) = P[im(f)];                        is TFdom1;                     // !! TFdom1 := dom(FAGx) = A;
! Lpuns_qinvs := im(qinvs) <: dom(puns);                     by Lqinvsim,Tpunsdom; is Staut; // ! Tpunsdom := dom(puns) = P[part];
! Tpunsqinvs_type := puns o qinvs in fn(P[im(f)], im(puns)); by -Lqinvsdom; is Tcomptf_type(puns,qinvs);
                                                              // fgcomp:: Tcomptf:= f o g in fn(dom(g),im(f)); 
! Tpreimun := preim = puns o qinvs;                    
 Proof Tpreimun;   by Tfneq;    L1 & L2;      // !! Tfneq := A[f,g: FN, f=g == dom(f)=dom(g) & A[x:dom(f), f(x)=g(x)]];
L1 := dom(preim) = dom(puns o qinvs);         by Tcompdom@fgcomp(puns,qinvs); // fgcomp :: !! Tcompdom := dom(f o g) = dom(g); 
F1 := dom(preim) = dom(qinvs);                byeq Lpreimdom, -Lqinvsdom;
L2 := A[Y:dom(preim), preim(Y) = (puns o qinvs)(Y)];
  EqProof -L2;
K0 := Y in dom(preim);                        assume;
K01 := preim(Y) = {x: dom(f); f(x) in Y};     is Red;
K1 := (puns o qinvs)(Y);                      by Tcompval(puns,qinvs); // @fgcomp; // !! Tcompval := A[x:dom(g), (f o g)(x) = f(g(x))]; 
K2 := puns(qinvs(Y));                         by Red;              // puns := F[Q:P[part], union(Q)];
K3 := union(qinvs(Y));                        by Tqinvsun;
K4 := {x:dom(f); f(x) in Y};                  by -K01;
K5 := preim(Y);
  end EqProof -L2;                           // ! Tpunsinj := injective(puns);
 end Proof Tpreimun;                         // fgcomp := {f,g ; f in FN, g in FN, Axfg := im(g) <: dom(f)};
                                             // fgcomp :: !! Tcompinj := injective(f) & injective(g) -> injective(f o g)
! Tpreiminj := injective(preim);             by Tpreimun; is Tcompinj(puns, qinvs)(Tpunsinj & Tqinvsinj); 
!! Tpreim1 := qinv=id(im(f)) -> preim = F[Y:P[im(f)], union(Y)];    // puns := F[Q:P[part], union(Q)]; // part(f) = im(qinv);

// ! Tpreim1 := imps = im(f) = part & id(im(f)) -> A[Y:P[im(f)], preim(Y) = union(puns(Y))];
// begin("module_preim");        // 5  preimage 1/10/12  correct glex! write string together with ""!

// dcl[preim,FN,set,set];        // preim(f,B)
// FN :: [   // FN1 :: [                       // --- var f:FN, B:P(im(f));  #4 FN
// !! Axpreim := preim(f,B) = {x; x in dom(f); f(x) in B};

// ! Tpreimin := All(x, x in preim(f,B) == x in dom(f) & f(x) in B);  // is Axab;
// ! Tpreimin1 := A[x:dom(f), x in preim(f,B) == f(x) in B];          // is TAab2;
// ! Tpreim1 := preim(f,B) <: dom(f);                               // is TabIn;
// ! Tpreim2 := B <: im(f) ->im(f|preim(f,B)) = B; 
// ! Tpreim3 := B = {} == preim(f,B) = {};                          ///
// ! Tpreim4 := B ~= {} == preim(f,B) ~= {};                        // is Teqvneg ! Tpreim3;
// ! Tpreimm := A[B1:im(f), A[B2: im(f), B1 <: B2 -> preim(f,B1) <: preim(f,B2)]]; /// monotonic, not used
// ];  // FN1 :: [    
]; // FN :: [                                                    #8 FN

// begin("module eqp");   // 13a equipollence
dcl[eqp,set,set,bool];                                  // see dcl[~, := E[f, f in bfn(A,B)];
!! Axeqp := eqp(A,B) == Exist(f, f in bfn(A,B));
!! Teqprefl := eqp(A,A);                                    // reflexive
!! Teqpsym := eqp(A,B) -> eqp(B,A);                        // symmetric
!! Teqptrans := eqp(A1,B1) & eqp(B1,C1) -> eqp(A1,C1);       // transitive
!! Teqp3 := eqp(A,C) & eqp(B,C) -> eqp(A,B);
!! TeqpRS := eqp(R[x:A, {x} ], A);
!! Teqp4 := f in bfn(A,B) -> eqp(A,B);
!! Teqp4a := f in bfn(A,B) -> eqp(B,A);

// begin("module cfn");   // 17 Constant FuNctions 10/25/08, 4/5/09 5.21
CFN := {f; AxCFN1 := f in FN, AxCFN2 := one(im(f)) };   // CFN := FN && (Ax1 := E1[im(f)]); // dcl[CFN,set];
!! TCFNREL := CFN <: REL;
!! TCFNFN := CFN <: FN;
!! TCFN := f in CFN == f in FN & one(im(f)); 
!! TCFNin1 := f in FN -> ( f in CFN == one(im(f)) );             //  is TAscin;                

CFN :: [ 
// ! L0 := 
!! TCFNim  := im(f) ~= {};                                       // is TE1emp(Ax1); by -Timemp;
!! TCFNdom := dom(f) ~= {}; 
!! TCFN1 := A[y1,y2:im(f), y1 = y2];                             // by Axim, TAR2;
!! TCFN2 := A[x1,x2:dom(f), f(x1) = f(x2)];

 cval := the(im(f)); 
!! Lcval1 := A[y:im(f), y = cval];                               // is TT1(Ax1); by Axim, TAR;
!! Tcval := A[x:dom(f), f(x) = cval];
]; // CFN :: [ 

FN :: [      // FN1 :: [                                            #9 FN
! TCFNin1 := f in CFN == one(im(f));                                  // is TAscin; by TE1A2;
! TCFN2 := f in CFN == im(f) ~= {} & A[y1,y2: im(f), y1 = y2];        // by -Timemp, Axim, TAR2;
! TCFN3 := f in CFN == dom(f) ~= {} & A[x1,x2: dom(f), f(x1) = f(x2)];
]; // FN1 :: [                                                      #9 FN

! TCFN4 := F[d,f] in CFN == one(d) & A[x1,x2: d, Rep(d,f,x1) = Rep(d,f,x2)];  // is TCFN3(F[d,q,t]);
  // begin("module AFN");   // autojections, (= permutations)
AFN := {f; AxAFN1 := f in IFN; AxAFN2 := dom(f) = im(f)}; // AFN := IFN && (Axdomim := dom = im); 
!! TAFNREL := AFN <: REL;
!! TAFNFN := AFN <: FN;
!! TAFNIFN := AFN <: IFN;
AFN :: [
var vd, dom(f);
ds := {x: dom(f); f(x) ~= x};
!! L0 := inv(f) in FN;
!! L1 := dom(inv(f)) = dom(f);
!! L2 := A[x:dom(f), f(x) in dom(f)];
!! L3 := A[x:dom(f), f(x) in dom(inv(f))];
!! LfAFN := f in AFN;                 // ??? auto ???
!! LAFNinj := injective(f);
!! L4 := f in afn(dom(f));
!! Lf_type := f^i in afn(dom(f));     // var i,j, ... int;
!! L5 := (f^i)(vd) in dom(f); 
!! L13 := (f^i)(vd) = (f^j)(vd) -> (f^abs(i-j))(vd) = vd;  //  A[i,j:int, 
!! L14 := dom(f^i) = dom(f); 
!! L15 := A[m:nat1, a:dom(f), (f^m)(a) = a -> A[n,r:nat, (f^(n*m+r))(a) = (f^r)(a)]];
!! L16 := A[i,j:int, a:dom(f), (f^i)(a) = (f^j)(a) -> (f^abs(i-j))(a) = a];
!! TAFN0 := (f^0)(vd) = vd;  
!! TAFN1 := inv(f) o f = id(dom(f));                          //   is Tinvcompl;
!! TAFN2 := A[x:dom(f), inv(f)(f(x)) = x];                    ///
!! TAFN3 := A[x:dom(f),i,k:int, (f^i)((f^k)(x)) = (f^(i+k))(x)];
!! LAFN4 := A[x:dom(f),k:int, f((f^k)(x)) = (f^(k+1))(x)];
!! LAFNds := A[x:dom(f), x in ds == f(x) ~= x];
!! LAFNreds := f | ds.f in AFN;
!! LAFNdsdom := ds <: dom(f);
!! LAFNdsid := ds={} == f = id(dom(f)); 
!! LAFNdsIn := A[B:P[dom(f)], A[x:B, f(x) ~= x] == B <: ds];               // ???==
!! TAFNre := B <: dom(f) & f|B in AFN -> A[i:nat, b:B, ((f|B)^i)(b) = (f^i)(b)];
!! TAFNRS := A[x:dom(f), f(x) = x -> R[i_nat, (f^i)(x)] = {x} ];
]; // AFN :: [

// dcl[^,AFN,int,AFN];                                           // ??? implicitly contains as an axiom: f^i in AFN // recursive def is better ???
dcl[^, AFN, int, afn(dom(f@AFN))];

FN :: ! TAFNin := f in AFN == injective(f) & dom(f)=im(f);  /// was FN1
! TAFNU := A[f,g: AFN, dom(f) NI dom(g) -> f\/g in AFN];     ///
// ! TAFNidD := A[A:set, B :< A, 

begin("module afn");   // autojections, (= permutations)
// dcl[afn,set,set];                  // afn := {f | Axafn := f in bfn(A,A)};

!! L12 := ifn(A,A) <: REL; ! L13 := afn(A) <: REL; ! L14 := afn(A) <: bfn(A,A);
!! Tafn := afn(A) = {f; f in ifn(A,A), im(f) = A};                         //  byeq Axafn,Axbfn;  
!! Tafnifn := afn(A) <: ifn(A,A);                                     //  is TabIn; with Tifnfn;
!! Tafnfn := afn(A) <: fn(A,A);  
!! Tafnfn1 := f in afn(A) -> f in fn(A,A);                                   
!! Tafnin := A[f:FN, f in afn(A) == injective(f) & dom(f)=A & im(f)=A]; // is Tbfnin(A,A); 
// !! Tafnin1 := A[f:FN, f in afn(A) == f in AFN & dom(f)=A];             /// 
!! Tafnin1 := f in afn(A) == f in AFN & dom(f)=A;         // !! Tafnin1 := A[f:FN, f in afn(A) == f in AFN & dom(f)=A];  
!! Tafndom := A[f: afn(A), dom(f) = A];                                 // is Tbfndom;
!! Tafndom1 := f in afn(A)-> dom(f) = A;
!! Tafnim := A[f: afn(A), im(f) = A];                                   // is Tbfnim;
!! Tafnim1 := f in afn(A)-> im(f) = A;
!! Tafncomp := A[f,g: afn(A), f o g in afn(A)];                         // is Tbfncomp1;
!! Tafncomp1 := f in afn(A) & g in afn(A) -> f o g in afn(A);
!! Tafninv := A[f: afn(A), inv(f) in afn(A)];                           // is Linvbfn1;
!! Tafninv1 := A[f: afn(A), dom(inv(f)) = A];                           // is Tafndom(inv(f)); by Lafndom;
!! Tafninv2 := A[f: afn(A), dom(inv(f)) = dom(f)]; 
!! Tafnre := A[f: afn(A), S: P[dom(f)], f|S in afn(S) == im(f)=S];      ///
!! Tafnid := id(A) in afn(A);                                           // is Tidbfn;
!! Tafn2 := F[f,g: afn(A), f o g] in fn(afn(A)#afn(A), afn(A));         // by TFinfn; Tafncomp;
!! Tafn3 := F[f: afn(A), inv(f)] in fn(afn(A),afn(A));                  // by TFinfn; Tafninv;
!! Tafn4 := A[f: afn(A), f o id(A) = f];                                // is Tidcompr;
!! Tafn4a := A[f: afn(A), id(A) o f = f];
!! Tafn5 := A[f: afn(A), f o inv(f) = id(A)];                           // is Tinvcompr;
!! Tafn5a := A[f: afn(A), inv(f) o f = id(A)];                          // is Tinvcompl;
!! Tafn6 := A[f,g,h: afn(A), f o (g o h) = (f o g) o h];                // is Tcompass;
!! Tafn7 := A[f: afn(A), x: A, f(x) = x -> f(f(x)) = x];                // use ProofAC, Leib; by Contraposition;
!! L15 := A[f: afn(A), x:A, f(x) in A]; 
!! Tafn7a := A[f: afn(A), x: A, f(f(x)) ~= x -> f(x) ~= x];
!! L16 :=  f in afn(A) -> inv(f) in bfn(A,A);
!! Tafn7b := A[f: afn(A), x:A, f(x) = x == inv(f)(x) = x];                // isA Tinv3; // not used
!! Tafn8 := A[f: afn(A), x: A, f(x) in A];                              // is Tvalim ! Tafnim;
! Tafncompid := A[f:afn(A), B: P[A], f o id(B) = f|B];                    ///
!! LafnFif := B<:A & f in afn(B) -> F[x:A, if(x in B, f(x), x)] in afn(A);  "nosimr";
! L00 := afn(A) <: AFN;        is LafnAFN;         // !! LafnAFN := afn(A) <: AFN; // for wlot in Tafncomm;
!! Tafncomm := f in afn(A) & g in afn(A) & ds.f NI ds.g -> f o g = g o f;   // without ; : fTabbot; // 11.14.22; ERROR in glex !!!
Tabbat;  // ! Tabbat := abba in REL;
// ! Tafncompabba := f in afn(A) & a in A & b in A -> f o abba = {[a,f(b)], [b,f(a)]};                 ////
// ! TafnU := A[f,g: AFN, dom(f)/\dom(g)={} -> f\/g in afn(dom(f)\/dom(g))]; ///
!! Tafnabba := abba in afn({a,b});                                       //   by Tafnin; &(Tinjabba,Tdomabba,Timabba);
!! Tafnemp := afn({}) = {{}};                                            //   is Tbfnemp({},{});
!! AxpwafnA := A[f: afn(A),k:int, f^k in afn(A)]; 
!! Lafn9 := g in AFN & dom(g)=A -> g in afn(A);
!! Tpwr3b := A[a:afn(A), k: int, a^(-k) = ((a)^k)^(-1)];         // is Tpwr3 ! Tpwra;

// f_AFN_A_set := {f:AFN, A:set; dom(f) <: A};
// (||) := F[{f:AFN, A:set; dom(f) <: A}, F[x:A, if(x in dom(f), f(x), x)]];          // extension
// ! Tdvl := A[f_AFN_A_set, f||A = F[x:A, if(x in dom(f), f(x), x)]];                 byeq Red("F");  // dvl: double vertical line;
// ! Ldvldom := A[f_AFN_A_set, dom(f||A) = A];                                        by Tdvl; is TFdom1;
// !! Ldvlafn := A[f_AFN_A_set, Ldvlafn_type := f||A in afn(A)];

f_AFN_B_P := {f,B; Axf := f in AFN, AxB := B in P[dom(f)], Ax1 := f|B in AFN };        
(||) := F[f_AFN_B_P, F[x:dom(f), if(x in B, f(x), x)]];          "nosimr";            // if B is an orbit of f, then f||B is a cycle;
! Tdvl := A[f_AFN_B_P, f||B = F[x:dom(f), if(x in B, f(x), x)]]; "nosimr";            byeq Red("F");  // dvl: double vertical line;
! Ldvldom := A[f_AFN_B_P, dom(f||B) = dom(f)];                                        by Tdvl; is TFdom1;
!! Ldvlafn := A[f_AFN_B_P, Ldvlafn_type := f||B in afn(dom(f))];

// f_AFN_B_P := {f,B; Axf := f in AFN, AxB := B in P[dom(f)], Ax1 := f|B in AFN };
// f_AFN_AB_set := {f,A,B; Axf := f in AFN, AxA := A in set, AxB := B in set, Ax1 := dom(f) <: A, Ax2 := B <: dom(f), Ax3 := f|B in AFN};
// f_AFN_AB_set :: !! L0 := dom(f|B) <: A;
f_AFN_B_P :: !! dom(f|B) <: dom(f);
!! Ldvlre := A[f_AFN_B_P, (f||B)|B = f|B ];
!! Ldvlreds := A[f_AFN_B_P, (f|ds.f) in AFN ];
!! Ldvlds := A[f_AFN_B_P, (f||ds.f) = f ];
!! LdvlB := A[f_AFN_B_P, A[x:B, (f||B)(x) = f(x) ]];
!! Ldvlid := A[f_AFN_B_P, A[x:dom(f)--B, (f||B)(x) = x ]];



begin("module swap");                    // swapping
fx1x2 := {f,x1,x2; Axf := f in FN; Ax1 := x1 in dom(f), Ax2 := x2 in dom(f)};  // | x1 ~= x2

/*  commented on 2022.06.19
swap := F[fx1x2, F[x:dom(f), if(x=x1,f(x2),x=x2,f(x1),f(x))]];
 
!! Tswapdom := dom(swap) = fx1x2; 

fx1x2 :: [
// swap := F[x:dom(f), if(x=x1,f(x2),x=x2,f(x1),f(x))];             // is TFdom;
!! TswapA := A[x:dom(f), if(x=x1,f(x2),x=x2,f(x1),f(x)) in im(f)];  // isA TswapA;
!! Tswapt := swap in fn(fx1x2,fn(dom(f),im(f)));                    // by TfninA; Tswapdom & TswapA:
!! Tswap1a := swap(f,x1,x2)(x1) = f(x2);                            // by TFred; Tifin3_1;
!! Tswap1 := A[x:dom(f), x=x1 -> swap(f,x1,x2)(x) = f(x2)];            ///
!! Tswap2a := swap(f,x1,x2)(x2) = f(x1);                            // by TFred; Tifin3_2;
!! Tswap2 := A[x:dom(f), x=x2 -> swap(f,x1,x2)(x) = f(x1)];            ///
!! Tswap3 := A[x:dom(f), x~=x1 & x~=x2 -> swap(f,x1,x2)(x) = f(x)];    ///
!! L0 := x in dom(f)--{x1,x2} -> x in dom(f);
!! Tswap3a := A[x:dom(f)--{x1,x2}, swap(f,x1,x2)(x) = f(x)];           ///
!! Tswap4 := swap = f|(dom(f)--{x1,x2}) \/ {[x1,f(x2)], [x2,f(x1)]};   ///
]; // fx1x2 :: [
*/

ab_any := {a,b; a in any, b in any};
tr := F[ab_any, {[a,b], [b,a]}];          // tr(a,b)(a) = b; tr(a,b)(b) = a;
!! Ltr_type := tr(a,b) in afn({a,b});     // contradiction with the definition of tr: tr must have 2 params;

Aab := {A,a,b ; AxA := A in set, Axa := a in A, Axb := b in A};        
Afab := {A,f,a,b ; AxA := A in set, Axf := f in afn(A), Axa := a in A, Axb := b in A};        

Trp := F[Aab, tr(a,b) \/ id(A--{a,b})];                   // F[x:A, if(x=a, b, x=b, a, x)]];
!! AxTrp := A[Aab, Trp(A,a,b) = tr(a,b) \/ id(A--{a,b})]; // (x) = if(x=a, b, x=b, a, x) ]];
!! LTrp_type := Trp in fn(Aab, afn(A));
Aab :: [ !! LTrpAab_type := Trp(A,a,b) in AFN; ];             //  was !! LTrpAFN := A[Aab, Trp(A,a,b) in AFN]; // did not work without [...];
!! LTrpdom := A[Aab, dom(Trp(A,a,b)) = A];
!! LTrpcomp := A[Afab, Trp(A,a,b) o f in afn(A)];

/*  commented on 2022.04.24
begin("module trp");                                  // see 24 Trp in 9 AFN  Transposition
abA := {a,b,A ; Axa := a in A, Axb := b in A;};       // Axab0 := a~=b};
trp := F[abA, F[x:A, if(x=a, b, x=b, a, x)]];
!! Axtrp := A[abA, A[x:A, trp(a,b,A)(x) = if(x=a, b, x=b, a, x) ]];

abA :: [
!! L0 := A[x:A, {[x,a]} in afn(A) ]; !! L01 := {[y,z]} in REL;         // for {[x,a]} in Ttrp4b
Xg := {X,g; Ax1 := X in P[A]; Ax2 := g in afn(X)};
!! L1 := A[Xg, inv(g) in afn(X)];
!! L2 := trp(a,b,A) in FN;
!! Ttrpt := trp(a,b,A) in afn(A);                                      //  is TafnU;   
!! TtrpA := A[x:A, if(x=a, b, x=b, a, x) in A];                        ///
!! Ttrpval := A[x:A, trp(a,b,A)(x) = if(x=a, b, x=b, a, x)];           //  byeqA Axtrp,TFred;  
!! Ttrpdom := dom(trp(a,b,A)) = A;                                     //  is TFdom;
!! Ttrp0 := A[x:A, x nin {a,b} -> trp(a,b,A)(x) = x];                  //  is Tif3_3;  // Tcoll2nin !!
!! Ttrp1 := trp(a,b,A)(a) = b;                                         //  is Tif3_1;                                  
!! Ttrp2 := trp(a,b,A)(b) = a;                                         //  byeq Ttrpval, Tif3_2 !! b=b;
!! Ttrpre := trp(a,b,A) | {a,b} = {[a,b],[b,a]};                       ///
!! TtrpDf := trp(a,b,A) \ {a,b} = id(A--{a,b});                        ///
!! TtrpU := trp(a,b,A) = {[a,b],[b,a]} \/ id(A -- {a,b});              //  byeq TDfre({a,b}),Ttrpre,TtrpDf;
!! Ttrpinv := inv(trp(a,b,A)) = trp(a,b,A);                            ///
!! Ttrpcomp := trp(a,b,A) o trp(a,b,A) = id(A);                        //  is Tinveq ! Ttrpinv;
!! Ttrpcomm := trp(a,b,A) = trp(b,a,A);                                //  byeq TtrpU;  
!! Ttrp3 := A[f: afn(A), f o trp(a,b,A) = {[a,f(b)], [b,f(a)]} \/ f|(A--{a,b})];    ///
!! Ttrp3b := A[h:FN, im(h) <: A--{a,b} -> trp(a,b,A) o h = h];                      ///
!! Ttrp4b := A[x:A, trp(a,b,A) o {[x,a]} = {[x,b]} ];                                   // byeqA TcompS, Ttrp1;
// !! Ttrp4c := A[Xg, a in X & b nin X -> trp(a,b,X) o g = {[(inv(g):afn(X))(a),b]} \/ g\{(inv(g):afn(X))(a)}]; /// comm. 12.13.21
fg := {f,g; f in afn(A); g in afn(A); g =inv(f) };
!! Ttrp3a := A[fg, trp(a,b,A) o f|{g(a),g(b)} = {[g(a),b], [g(b),a]}];        ///
!! Ttrp3c := A[fg, im(f\{g(a),g(b)}) =  A--{a,b}];                           // isA TinvimDf2(f,a,b);
!! Ttrp3d := A[fg, trp(a,b,A) o f\{g(a),g(b)} = f|(A--{g(a),g(b)})];            ///
!! Ttrp4 := A[fg, trp(a,b,A) o f = {[g(a),b], [g(b),a]} \/ f|(A--{g(a),g(b)})]; ///
!! Ttrpid := All(X, X<:A & a in X & b nin X  -> trp(a,b,A) o id(X) = {[a,b]} \/ id(X--{a}) ); ///
!! Ttrpid1 := All(B, B<:A & {a,b} <: B -> trp(a,b,A) o id(A--B) = id(A--B) );                 ///

]; // abA :: [

// transp(a,b:A) := F[x:A, if(x=a, b, x=b, a, x)];
// ! Ttranspt := A[a,b:A, transp(a,b) in afn(A)];
*/

begin("module FNS");   // Set valued functions 2/24/13

FNS := {f; f in FN;im(f) <: set};  // set is same as any
! TFNS1 := A[d,q in set] -> F[d,q] in FNS;

FNS :: [     // FNS :: begin
! TUunionim := A[x:dom(f), f(x)\/union(im(f|(dom(f)--x))) = union(im(f))];   // not used
! Tunionim := union(im(f)) = U[i:dom(f), f(i)];                        ///
! TFNSre := A <: dom(f) -> f|A in FN;
! Tunionimre := A <: dom(f) -> union(im(f|A)) = U[i:A, f(i)];                         ///                                  // not used
! TFNdsjin := f in FNdsj == A[x1,x2: dom(f), x1 ~= x2 -> f(x1) NI f(x2) ]; // is TAScin; // used only in dfsp
! TFNdsjin1 := f in FNdsj == A[x1,x2: dom(f),f(x1) IN f(x2) -> x1 = x2 ]; // is  TFNdsjin !! CP; // ContraPosition

]; // FNS :: begin

// FNdsj := FNS && (AxFNdsj := A[x1,x2: dom(f), x1 ~= x2 -> f(x1) NI f(x2)]);
FNdsj := {f; Axf := f in FN; Ax1 := dsjs(im(f)); Ax2 := {} nin im(f) };

FNdsj :: [
// ! L0 := A in P[B] == A <: B;
! TFNdsjIN := A[x1,x2: dom(f), f(x1) IN f(x2) -> x1 = x2];                        // is Tprt2;
! TFNdsjinj := injective(f);                                                      ///
! TFNdsj0 := A[A,B: P[dom(f)], A IN B == union(im(f|A)) IN union(im(f|B))];       /// 
! TFNdsj1 := A[A,B: P[dom(f)], A NI B == union(im(f|A)) NI union(im(f|B))];       // by TINNI, Teqvneg; TFNdsj0; by Tunionimre;
! TFNdsj1a := A[A,B: P[dom(f)], A NI B == U[x:A, f(x)] NI U[x:B, f(x)] ];         //// used only in dfsp
! TFNdsj1a1 := A[a:dom(f), B: P[dom(f)], a nin B == f(a) NI U[x:B, f(x)] ];       /// not used 
! L01 := x in A--B -> x in A;
// ! L02 := dom(f)--H <: dom(f);                                                  // see wlot
! TFNdsj1b := A[H: P[dom(f)], U[x:H, f(x)] NI U[x:dom(f)--H, f(x)] ];             // isA TFNdsj1a !! H NI dom--H;

]; // FNdsj :: [                                 



begin("module mgm1");   // magma1, unary magma
mgm1 := {U,B,g ; AxB := B <: U, Axg := g in fn(U,U)};
mgm1 :: [

!! Tmgm1a := A[x:U, g(x) in U];                  // is TfninA !! Axg;
indset := {A ; AxA := A <: U, AxB := B <: A, Axg := A[x:A, g(x) in A]};
!! TB1 := A[indset, B <: U];                     // is AxB !! AxA;
!! Tg1 := A[indset, im(g|A) <: A];               // by TimreA; Axg;
!! Tindsetin := All(X, X in indset == X <: U & B <: X & A[x:X, g(x) in X]);
!! TindsetU := U in indset;                      // by Def; &(U <: U,TB1,Tmgm1a));
!! Tindset1 := indset ~= {};                     // is Tinnemp ! TindsetU;
X_indset := {X; X in indset};
!! Tindset2 := A[X_indset, X <: U];              // isA AxA(X);
!! Tindset3 := A[X_indset, B <: X];              // isA AxB(X);
!! Tindset4 := A[X_indset,A[x:X, g(x) in X]];       // isA Axg(X);

clos := II(indset);                             // gen 
!! Tclost := clos <: U;                          // is TII5(indset) ! (Tindset1 &  Tindset2);
!! Tclos1 := B <: clos;                          // is TII6(indset,B) ! (Tindset1 &  Tindset3);
!! Tclos2 := A[x:clos, g(x) in clos];            ///
!! Tclos2a := A[x:clos, A[z:indset, x in z]];
!! Tclos3 := clos in indset;                     // by Def; &(Tclost,Tclos1,Tclos2);
!! Tclos4 := A[X:indset, clos <: X];             // is TII4(indset);
!! Tclos5 := A[X:indset, A[Y:indset, X <: Y] -> X=clos]; // is TII7(indset) ! Tclos3;
]; // mgm1 :: [

magma1 := {U,g ; Axg := g in fn(U,U)};

magma1 :: closed := F[X:P[U], im(g|X) <: X];
! TIIin0 := All(x, x in II(A) == A[z:A, x in z]);
! TIIin1 := A[x:II(A), A[z:A, x in z]];
! TII4a := All(A, A[z:A, II(A) <: z]); 
! TII5a := All(A, A ~= {} & A[z:A, z <: B] -> II(A) <: B);
! TII6a := All(A,All(B, A ~= {} & A[z:A, B <: z] -> B <: II(A) ));
! TII7a := II(A) in A -> A[X:A, A[Y:A, X <: Y] -> X = II(A)]; 

begin("module gendefs");   // general definitions

Relf := {A,R; A in set, AxR := R in fn(A#A,bool)};  // relation as function
Relf :: [     // total reflexive irreflexive transitive symmetric asymmetric antisymmetric
total := A[x,y:A, R(x,y) or R(y,x)];   //  Totality
reflexive := A[x:A, R(x,x)];
irreflexive := A[x:A, ~R(x,x)];
transitive := A[x,y,z:A, R(x,y) & R(y,z) -> R(x,z)];
symmetric := A[x,y:A, R(x,y) -> R(y,x)];
asymmetric := A[x,y:A, R(x,y) -> ~R(y,x)];
antisymmetric :=  A[x,y:A, R(x,y) & R(y,x) -> x=y];
                                                      // trichotomous: exactly one of a < b, b < a and a = b is true.
connected :=  A[x,y:A, x ~= y -> R(x,y) or R(y,x)];
connected1 := A[x,y:A, x=y or R(x,y) or R(y,x)];
connected2 := A[x,y:A, ~R(x,y) -> x=y or R(y,x)];
! Tconnected1 := connected == connected1;               // byeq Taut (~p -> q or r == or(p,q,r));
! Tconnected2 := connected == connected2;               // byeq Taut (~p -> q or r == ~q -> p or r)); 

trichotomous := A[a,b:A, xor3(R(a,b),a=b,R(b,a))];                      // a<b,a=b,b<a); "<" was not defined !!!
!! Axtrichotomous := trichotomous == A[a,b:A, xor3(R(a,b),a=b,R(b,a))];

! Ttrichotomous1 := trichotomous == connected & 
                    A[x,y:A, ~(R(x,y) & x=y) & ~(R(x,y) & R(y,x)) & ~(R(y,x) & x = y)]; // use Dxo3b;
! Ttrichotomous2 := connected & 
   A[x,y:A, (x=y == ~R(x,y) & ~R(y,x)) & (R(x,y) == x ~= y & ~R(y,x)) &  (R(y,x) == x ~= y & ~R(x,y))]; // use Dxo3g;

! Ttrich1 := trichotomous ->  A[x,y:A, ~(R(x,y) & R(y,x))];           // from Ttrichotomous1;
! Ttrich2 := trichotomous ->  A[x,y:A, ~(x=y & R(x,y))];              // from Ttrichotomous1;
! Ttrich3 := trichotomous -> irreflexive;                            // R(x,x) & x=x is impossible
! Ttrich4 := trichotomous -> A[x,y:A, (x=y == ~R(x,y) & ~R(y,x)) & (R(x,y) == x ~= y & ~R(y,x)) &  (R(y,x) == x ~= y & ~R(x,y))];
! Ttrich4a := trichotomous -> A[x,y:A, (x=y == ~R(x,y) & ~R(y,x))];
! Ttrich4b := trichotomous -> A[x,y:A,  R(x,y) == x ~= y & ~R(y,x)];
! Ttrich4c := trichotomous -> A[x,y:A,  R(y,x) == x ~= y & ~R(x,y)];   // maybe not needed, the same as Ttrich4b

totalorder := transitive & antisymmetric & total; 
// toset := {R; R in Relf; transitive, antisymmetric, total};  // {A,R; (M:= [A,R]) in Relf; transitive.M; ...}
eqvr := reflexive & symmetric & transitive;                  // equivalence

! Tirtr_as := irreflexive & transitive -> asymmetric; 
! Ttrich5 := connected & reflexive == total; // (Proofwiki) http://www.proofwiki.org/wiki/Relation_Connected_and_Reflexive_iff_Total
! Ttrich_con := trichotomous -> connected;
! Ttrich6 := trichotomous -> (~ reflexive) & irreflexive; // (R(x,x) cannot hold because x=x).
! Ttrich7 := transitive & trichotomous -> irreflexive & asymmetric & antisymmetric;
! Tirtr_trichcon := irreflexive & transitive -> (trichotomous == connected); // follows from Tirtrcon_trich, Ttrich_con
! Tirtrcon_trich  := irreflexive & transitive & connected -> trichotomous;
]; // Relf :: begin

// Relf := {R:FN | Ax1 := Ex[A:set, dom(R) = A#A]; Ax2 := im(R) = bool]};
// relf(A:set) := fn(A#A, bool); // Relf(A:set) := {R | R in relf(A)}; // {R: fn(A#A,bool)};
//     http://www.proofwiki.org/wiki/Antireflexive_Transitive_Relation_is_Asymmetric
// asymmetric & transitive -> irreflexive     ProofWiki) Follows immediately from Asymmetric Relation is Antireflexive

begin("module preorder");   // Preorder
// dcl[<=, any, any, bool];

preorder := {Y,<=; Y in set; <= in fn(Y#Y, bool) ; Axrefl := A[x:Y, x <= x];
                  Axtrans := A[x,y,z:Y, x <= y & y <= z -> x <= z] };
preorder :: [
! L0 := S in P[Y] == S <: Y;
// <,lT := F[x:Y, S:P[Y], A[u:S, x < u]];
// !! AxlT := < = F[x:Y, S:P[Y], A[u:S, x < u]];
// ! TlTA := A[x:Y, S:P[Y], x < S == A[u:S, x < u]];

<== := F[x:Y, S:P[Y], A[u:S, x <= u]];
!! AxlE := (<==) = F[x:Y, S:P[Y], A[u:S, x <= u]];
! TlEA := A[x:Y, S:P[Y], x <== S == A[u:S, x <= u]];

mins := F[S:P[Y], {x; x in S ; x <== S}];
// < := F[x,y:Y, x<=y & x~=y];
dcl[<,Y,Y,bool];
!! Axltpr := A[x,y:Y, x < y == x<=y & x~=y];
! Tminsin := A[S:P[Y], x:S, x in mins(S) == x <== S];          // is Axab; with TlEA;   
! Tminsin1 := A[S:P[Y], x:S, x in mins(S) == A[u:S, x <= u]];  
! Tminsin2 := A[S:P[Y], x:S, x nin mins(S) == E[u:S, u < x]];   
]; // preorder :: [

begin("module poset");   // poset.v partially ordered sets 02/01/07 04/02/09

poset := {elp, <=  ;  Ax1 := elp in set;   Ax2 := (<=) in fn(elp#elp, bool);
         Axreflle    := A[x: elp, x <= x];                        // Reflexivity
         Axantisymle := A[x,y: elp, x <= y & y <= x -> x = y];    // Antisymmetry
         Axtransle   := A[x,y,z: elp, x <= y & y <= z -> x <= z]; // Transitivity         
         };

poset :: [
ab := {a,b; a in elp, b in elp};  var c, elp;

// <,lt := F[a,b:elp, a <= b & a ~= b];
// >,gt := F[a,b: elp, b < a];
// >=,gte := F[a,b: elp, b <= a];
// !! Axgt := (>) = F[a,b: elp, a > b == b < a];
// !! Axge := (>=) = F[a,b: elp, a >= b == b <= a];

dcl[<, elp,elp,bool];
dcl[>, elp,elp,bool];
dcl[>=, elp,elp,bool];
ab :: [

!! Axlt := a < b == a <= b & a ~= b;
!! Axgt := a > b == b < a;
!! Axgte := a >= b == b <= a;

// ! Tltt := (<) in fn(elp#elp, bool);
! Tlelt := a <= b == a < b or a = b;             // p & ~q or q == p
! Tltle := a < b -> a <= b;
! Tltneq := a < b -> a ~= b;
! Ttranslt := a < b & b < c -> a < c;            // use Proofc, Tltle, Axtransle; 
! TltNor := ~(a<b) == ~(a <= b) or a = b;        // from ~(a<=b) does not follow that b < a !!!!!!

! Tgtt := (>) in fn(elp#elp, bool);
! Tgtlt := a > b == b <= a & a ~= b;
! Tgtle := a > b -> b <= a;
! Tgtneq := a > b -> a ~= b;
! Ttransgt := a > b & b > c -> a > c;            // use Proofc, Axgt, Ttranslt, Axgt; 

! Tget := (>=) in fn(elp#elp, bool);
! Tgegt := a >= b == a > b or a = b;
! Tgtge := a > b == a >= b & a ~= b;
! Tgtge1 := a > b -> a >= b;    
! Ttransge := a >= b & b >= c -> a >= c;         // use Proofc, Axge, Ttransle, -Axge; 
]; // ab :: [
// <=,lteS := F[a: elp, B: P[elp], A[b: B, a <= b]];
// <=,ltSe := F[A: P[elp], b: elp, A[a: A, a <= b]];
// <=,ltSS := F[A: P[elp], B: P[elp], A[a: A, a <= B]];

dcl[<=, elp, P[elp], bool];
dcl[<=, P[elp], elp, bool];
dcl[<=, P[elp], P[elp], bool];

!! AxLE := A[A: P[elp], B: P[elp], A <= B == A[a: A, b: B, a <= b] ];
!! TLE1 := A[A: P[elp], B: P[elp], A <= B == A[b: B, A <= b] ];
!! TLE2 := A[A: P[elp], B: P[elp], A <= B == A[a:A, a <= B] ];
!! TeeS := A[a: elp, b: elp, C: P[elp], a <= b & b <= C -> a <= C];
!! TeSe := A[a: elp, B: P1[elp], c: elp, a <= B & B <= c -> a <= c];
!! TSee := A[A: P[elp], b: elp, c: elp, A <= b & b <= c -> A <= c];
!! TSeS := A[A: P[elp], b: elp, C: P[elp], A <= b & b <= C -> A <= C];
!! TeSS := A[a: elp, B: P1[elp], C: P[elp], a <= B & B <= C -> a <= C];
!! TSSe := A[A: P[elp], B: P1[elp], c: elp, A <= B & B <= c -> A <= c];
!! TSSS := A[A: P[elp], B: P1[elp], C: P[elp], A <= B & B <= C -> A <= C];

// < := F[a: elp, B: P[elp], A[b: B, a < b]];
// < := F[A: P[elp], b: elp, A[a: A, a < b]];
// < := F[A: P[elp], B: P[elp], A[a: A, a < B]];

dcl[<, elp, P[elp], bool];
dcl[<, P[elp], elp, bool];
dcl[<, P[elp], P[elp], bool];

!! TlT := A[x:elp, A:P[elp], x<A ==  A[u:A, x<u]];
!! TlTN := A[x:elp, A:P[elp], ~(x<A) ==  E[u:A, u <= x]];
!! TimP := f in fn(C,D) & A in P[C] -> im(f|A) in P[D];
!! TimSSle := A[f: fn(C,elp), A,B: P[C], im(f|A) <= im(f|B) == A[x:A, x1:B, f(x) <= f(x1)]];


]; // poset : [

begin("module poset_minmax");                // minmax.v 02/01/07 04/03/09 10/29/13
poset :: [             // chain := A[x,y: A, comparable(x, y)];

dcl[mins,P[elp],P[elp]];                                  // minimums: mins := F[A:P[elp], {m: A | m <= A}]; 
!! Axmins := A[A:P[elp], mins(A) = {m; m in A, m <= A}];  // Axmins := mins = F[A:P[elp], {m: A | m <= A}]; TminsA;
!! Tmins1 := A[A:P[elp], most1(mins(A))];                 // most1(S) == E[S] -> E1[S]  (exists at most one)

dcl[minimals,P[elp],P[elp]];                  // minimals(A:P[elp]) := {m: A | A[x: elp, x <= m -> x = m]};  
!! Axminimals := A[A:P[elp], minimals(A) = {m; m in A, A[x: elp, x <= m -> x = m]} ];
!! L3 := A[A:P[elp], mins(A) <: minimals(A)];                   
               
dcl[maxs,P[elp],P[elp]];                   // maximums
!! Axmaxs := A[A:P[elp], maxs(A) = {m; m in A, A <= m}];

dcl[maximals,P[elp],P[elp]];                  // minimals(A:P[elp]) := {m: A | A[x: elp, x <= m -> x = m]};  
!! Axmaximals := A[A:P[elp], maximals(A) = {m; m in A, A[x: elp, m <= x -> x = m]} ];
!! L4 := A[A:P[elp], maxs(A) <: maximals(A)];

dcl[lbs,P[elp],P[elp]];                                    // lower bounds
!! Axlbs := A[A:P[elp], lbs(A) = {x; x in elp, x <= A}]; 

dcl[ubs,P[elp],P[elp]];                                    // upper bounds
!! Axubs := A[A:P[elp], ubs(A) = {x; x in elp, A <= x}]; 

dcl[sup,P[elp],P[elp]];                                    // supremum
!! Axsup := A[A:P[elp], sup(A) = mins(ubs(A))]; 

dcl[inf,P[elp],P[elp]];                                    // infinum
!! Axinf := A[A:P[elp], inf(A) = maxs(lbs(A))]; 

!! Tsup1 := A[A:P[elp], most1(sup(A))];    // at most 1 supremum 
!! Tinf1 := A[A:P[elp], most1(inf(A))];    // at most 1 infimum 

// posetm := poset && (Emim := E[minimums];
// ! L5 := E1[mimimums];
// min := T[minimums];  min(A) := T[mins(S)];   var S: P[elp];
// ! Tmin1 := E[mins(S)] -> min(S) in S;
// ! Tmin2 := E[mins(S)] -> min(S) <= S;
// ! Tmin3 := E[mins{x:S | P(x)}] -> min{x:S | P(x)} in S;
// ! Tmin3a := E[mins{x:S | P(x)}] -> P(min{x:S | P(x)});

]; // poset :: [ 

begin("module storder");                                     // Strict Total Order
storder := {els,< ; els in set, (<) in fn(els#els, bool); 
            Axirr := A[x:els, ~(x < x)];                       // Irreflexive
            Axtr := A[x,y,z: els, x < y & y < z -> x < z];     // Transitive
            Axcon := A[x,y: els, x ~= y -> x < y or y < x];    // Connected
           };  // end def storder
// dcl[trichotomous,REL,bool];
                               // trichotomous(Relf(M)) is adt (abridged dot term): in C++ notation) Relf(M).trichotomous;
storder :: [                   // Relf := {A,R; A in set, AxR := R in fn(A#A,bool)}; Relation as function;
                               // Relf := trichotomous := A[a,b:A, xor3(R(a,b),a=b,R(b,a))];  
M := [els, < @ storder];                              // "irreflexive & transitive & connected" -> trichotomous";
!! TM1_type := M in Relf;
!! Tstoasym := A[x,y: els, x < y -> ~(y < x)];        // is Tirtras.M; // "irreflexive & transitive -> asymmetric";  // Asymmetric
!! Tstotrich := trichotomous.M;                       // is Tirtrcon_trich.M(Axirr,Axtr,Axcon); with Ttrich1.M;
!! Tstotrich1 := A[x,y:els, ~(x<y & y<x)];            // by Taut(~(p & q) == p -> ~q);
!! Tstotrich1a := A[x,y:els, x<y -> ~(y<x)];
!! Tstotrich2 := A[x,y:els, ~(x=y & x<y)];            // is Tstotrich ! Ttrich2.M; by Taut(~(p & q) == (p -> ~q));
!! Tstotrich2a := A[x,y:els, x=y -> ~(x<y)];          // by CP, NN;
!! Tstotrich2b := A[x,y:els, x<y -> ~(x=y)];
!! Tstotrich2c := A[x,y:els, x<y -> ~(x=y) & ~(y<x)]; // is Tstotrich1a ! Tstotrich2b;
!! Tltor := A[x,y: els, x < y or x=y or y < x];        // is Axcon ! Taut((~p -> q or r) == or(p,q,r));
!! Tltxor := A[x,y: els, xor3(x < y, x=y, y < x)];     // byA Dxor3a; &(Tltor,Tstotrich2(x,y),Tstotrich1,Tstotrich2(y,x)); 

dcl[~<,els,els,bool];
// by Axtrichotomous.M; Axcon & Tstotrich2;            //  x ~< y) & y ~< x == ~(x<y or y<x)
!! Tstotrich3a := A[x,y:els, x=y == x ~< y & y ~< x];        // by Teqvneg;  ///
!! Tstotrich3aN := A[x,y:els, x ~= y == x < y or y < x];
!! Tstotrich3b := A[x,y:els,x < y == x ~= y & ~(y < x)];     ///
!! Tstotrich3b1 := A[x,y:els, x < y -> x ~= y];              // from  Tstotrich3b; // is Taut((p->q&r) -> (p->q));
!! Tstotrich3b2 := A[x,y:els, x < y -> ~(y < x)];            // from  Tstotrich3b; // is Taut((p->q&r) -> (p->q));
!! Tstotrich3c := A[x,y:els,(y < x == x ~= y & ~(x < y))]; 

dcl[<=, els,els,bool];
// <=,le := F[x,y:els, x < y or x = y];                  // less or equal  // <=$le <=%le
// ! Tlet := le in fn(els#els,bool);                    // is TFt;
!! TleA := A[x,y:els, x <= y ==  x < y or x = y];     // by TFred; Axrefl;
!! Tlelt :=  A[x,y:els, x < y -> x <= y];             // by TleA; Taut(p -> p or q);
!! Tlelt1 :=  A[x,y:els, x = y -> x <= y];            // by TleA; Taut(q -> p or q);
!! TltN := A[x,y:els, ~(x<y) == y<=x];                 // by Tstotrich3b,Nand,NN; TleA;
!! Tlerefl := A[x:els, x<=x];                         // by TFred, Axirr; Axrefl;  // reflexivity see T4.3a
!! Tletr1 := A[x,y,z: els, x < y & y <= z -> x < z];   ///
!! Tletr := A[x,y,z:els, x<=y & y<=z -> x<=z];         /// transitivity  
!! Tltle := A[x,y:els, x < y == x <= y & x ~= y];      // is Tstotrich3b ! TltN;
!! Tantisymle := A[x,y: els, x <= y & y <= x -> x = y];  /// Antisymmetry 
                                     // by Def; &(Tlet,Tlerefl,Tantisymle,Tletr,Ttotle);

dcl[<,els,P[els],bool];
// <,lT := F[x:els, A:P[els], A[a:A, x < a]];
// !! AxlT := < = F[x:els, A:P[els], A[a:A, x < a]];         
!! TlTA := A[x:els, A:P[els], x < A == A[a:A, x < a]];        
!! TlTN := A[x:els, A:P[els], ~(x < A) == E[a:A, a <= x]];
!! TlT1 := A[x:els, A:P[els], x < A -> x nin A];
!! TlT2 := A[x:els, A:P[els], a: A,  x < A -> x < a];
!! TlT3 := A[A:P[els], {x; x in els, x < A} NI A];                           

dcl[<=,els,P[els],bool];
// <=,lE := F[x:els, A:P[els], A[a:A, x <= a]];
// !! AxlE := < = F[x:els, A:P[els], A[a:A, x <= a]];         
! TlEA := A[x:els, A:P[els], x <= A == A[a:A, x <= a]];
// ! TlTN := A[x:els, A:P[els], ~(x < A) == E[a:A, a <= x]];
// ! TlT1 := A[x:els, A:P[els], x < A -> x nin A];
// ! TlT2 := A[x:els, A:P[els], a: A,  x < A -> x < a];
// ! TlT3 := A[A:P[els], {x:els | x < A} NI A];                           

]; // storder :: [

begin("toset.v");   // totally ordered sets 02/01/07 04/02/09  

// toset := poset(elt) && (Axtotle := A[x,y: elt, x <= y or y <= x]); // 
// Axtoset :=   // this will be automatically generated from the above line
toset := {elt, <=  ;  Ax0 := elt in set;                          // total(linear) order
         Ax1 := ( <= ) in fn(elt#elt, bool);
         Axreflle    := A[x: elt, x <= x];                        // Reflexivity

         Axantisymle := A[x,y: elt, x <= y & y <= x -> x = y];    // Antisymmetry
         Axtransle   := A[x,y,z: elt, x <= y & y <= z -> x <= z]; // Transitivity        
         Axtotle := A[x,y: elt, x <= y or y <= x];                // Totality
         };
!! Ttoset1 := toset <: poset;
toset :: [                                       // also linear ordered set
var a,b,c, elt;                                  // ab := {a,b: elt}; 
!! Tleeq := A[a,b: elt, a = b -> a <= b];

//'<',lt := F[a,b: elt, a <= b & a ~= b];
// !! Axlt := (<) = F[a,b: elt, a < b == a <= b & a ~= b];
dcl[<,elt,elt,bool];
lt := F[a,b:elt, a<b];
!! TltA :=  A[a,b: elt, a < b == a <= b & a ~= b];
!! Tltt := lt in fn(elt#elt, bool);
!! Tltlt := A[a,b:elt, a <= b == a < b or a = b];
!! Tltle := A[a,b:elt, a < b -> a <= b];
!! Tltneq := A[a,b:elt, a < b -> a ~= b];
!! TNltle := A[a,b:elt, ~(a < b) == b <= a];
!! TNlelt := A[a,b:elt, ~(a <= b) == b < a];
!! Ttranslt := a < b & b < c -> a < c;             //  use Proofc, Tltle, Axtransle; 

//  '>' := F[a,b: elt, b < a];
//!! Axgt := (>) = F[a,b: elt, a > b == b < a];
dcl[>,elt,elt,bool];
gt := F[a,b:elt, a>b];
!! Tgtt := gt in fn(elt#elt, bool);
!! Tgtlt := A[a,b:elt, a > b == b <= a & a ~= b];
!! Tgtle := A[a,b:elt, a > b -> b <= a];
!! Tgtneq := A[a,b:elt, a > b -> a ~= b];
!! Ttransgt := a > b & b > c -> a > c;             // use Proofc, Axgt, Ttranslt, Axgt; 


// '>=' := F[a,b: elt, b <= a];
// !! Axge := (>=) = F[a,b: elt, a >= b == b <= a];
dcl[>=,elt,elt,bool];
ge := F[a,b:elt, a>=b];
!! Tget := ge in fn(elt#elt, bool);
!! Tgegt := A[a,b:elt, a >= b == a > b or a = b];
!! Tgtge := A[a,b:elt, a > b == a >= b & a ~= b];
!! Tgtge1 := A[a,b:elt, a > b -> a >= b];    
// ! Tgtneq := A[a,b:elt, a > b -> a ~= b];
!! Ttransge := a >= b & b >= c -> a >= c;   // use Proofc, Axge, Ttransle, -Axge; 

// mins := F[S:P(Y), {x:S | x <= S}];       // see preorder, or maybe better, poset
dcl[mins,P[elt],P[elt]];                                  // minimums: mins := F[A:P[elp], {m: A | m <= A}];
dcl[<=,elt,P[elt],bool]; 
!! Axmins := A[A:P[elt], mins(A) = {m; m in A, m <= A}];  // Axmins := mins = F[A:P[elp], {m: A | m <= A}]; TminsA;
!! Tminsin := A[S:P[elt], x:S, x in mins(S) == x <= S];              // see preorder   
!! Tminsin1 := A[S:P[elt], x:S, x in mins(S) == A[u:S, x <= u]];     // // see preorder
!! Tminsin2 := A[S:P[elt], x:S, x nin mins(S) == E[u:S, u < x]];      //byeqA Tminsin1,TNA, 


]; //  toset :: [

// A problem: where to define mins (preorder, poset, toset) ?

begin("module woset");    //  well ordered sets 02/01/07 04/02/09 

// woset := toset(elw) && (Axwellordle := A[X:P1[elw], E[a:X, A[x:X, a <=x]]]); // 
// woset := toset(elw) && (Axwellordle := A[X:P1[elw], E[mins(X)]]); // 
// Axwellorder :=   // this will be automatically generated from the above line
woset := {elw, <=  ;  Ax0 := elw in set;                          // total(linear) order
         Ax1 := (<=) in fn(elw#elw, bool);
         Axreflle    := A[x: elw, x <= x];                        // Reflexivity
         Axantisymle := A[x,y: elw, x <= y & y <= x -> x = y];    // Antisymmetry
         Axtransle   := A[x,y,z: elw, x <= y & y <= z -> x <= z]; // Transitivity          
         Axtotle := A[x,y: elw, x <= y or y <= x];                // Totality
         Axwellordle := A[X:P1[elw], E[a:X, A[x:X, a <= x]]];     // well-ordering 
         };                                                       // every non-empty set has a least element         
! Twoset1 := woset <: toset; 
! Twoset2 := woset <: poset;
woset :: [
var a,b,c, elw;
!! Twoset3 := A[S: P[elw], nemp(mins(S)) == nemp(S) ];
!! Tleeq := A[a,b: elw, a = b -> a <= b];

// '<' := F[a,b: elw, a <= b & a ~= b];
// !! Axlt := (<) = F[a,b: elw, a < b == a <= b & a ~= b];
dcl[<,elw,elw,bool];
lt := F[a,b:elw, a<b];
!! Tltt := lt in fn(elw#elw, bool);
!! Tlelw := A[a,b:elw, a <= b == a < b or a = b];
!! Tltle := A[a,b:elw, a < b -> a <= b];
!! Tltneq := A[a,b:elw, a < b -> a ~= b];
!! Ttranslt := a < b & b < c -> a < c;  // use Proofc, Tltle, Axtransle; 

// '>' := F[a,b: elw, b < a];
// !! Axgt := (>) = F[a,b: elw, a > b == b < a];
dcl[>,elw,elw,bool];
gt := F[a,b:elw, a>b];
!! Tgtt := gt in fn(elw#elw, bool);
!! Tgtlt := A[a,b:elw, a > b == b <= a & a ~= b];
!! Tgtle := A[a,b:elw, a > b -> b <= a];
!! Tgtneq := A[a,b:elw, a > b -> a ~= b];
!! Ttransgt := a > b & b > c -> a > c;  // use Proofc, Axgt, Ttranslt, Axgt; 

// '>=' := F[a,b: elw, b <= a];
// !!!! Axge := (>=) = F[a,b: elw, a >= b == b <= a];
! Tget := (>=) in fn(elw#elw, bool);
dcl[>=,elw,elw,bool];
ge := F[a,b:elw, a>=b];
!! Tgegt := A[a,b:elw, a >= b == a > b or a = b];
!! Tgtge := A[a,b:elw, a > b == a >= b & a ~= b];
!! Tgtge1 := A[a,b:elw, a > b -> a >= b];    
// ! Tgtneq := A[a,b:elw, a > b -> a ~= b];
!! Ttransge := a >= b & b >= c -> a >= c;  // use Proofc, Axge, Ttransle, -Axge; 

dcl[comparable,elw,elw,bool];
Axcomparable := A[a,b:elw, comparable(a,b) == a <= b or b <= a];

dcl[compatible,elw,elw,bool];
Axcompatible := A[a,b:elw, compatible(a,b) == E[x: elw, x <= a & x <= b]];

!! L1 := A[a,b:elw, comparable(a,b) -> compatible(a,b)];

dcl[mins,P[elw],P[elw]];                                  // minimums: mins := F[A:P[elp], {m: A | m <= A}];
dcl[<=,elw,P[elw],bool]; 
!! Axmins := A[A:P[elw], mins(A) = {m; m in A, m <= A}];  // Axmins := mins = F[A:P[elp], {m: A | m <= A}]; TminsA;
!! Tminsin := A[S:P[elw], x:S, x in mins(S) == x <= S];              // see preorder 

!! Twoset4 := A[S: P1[elw],  one(mins(S))];

dcl[min,P1[elw],elw];
!! Axmin := A[S:P1[elw], min(S) = the(mins(S))];
!! Tmin1 :=  A[S:P1[elw], min(S) in S];
// ! Tmin2 :=  A[S:P1[elw], min(S) <= S];
!! Tmin3 :=  A[S:P1[elw],x:elw, x < min(S) -> x nin S];
]; // woset :: [ 

begin("module wfrel");   // well-founded relation 11/26/08

wfrel := {W,< ; W in set, < in fn(W#W, bool); // there exists a minimal element in every nonempty set:

            Axwf := A[S:P[W], S ~= {} -> E[x:W, x in S & A[y:W, y < x -> y nin S]]]; }; 

wfrel :: [    // Infinite Descent

!! InfDescent := A[S:P[W], S = {} == A[x:W, x in S -> E[y:W, y < x & y in S]]];

!! Wfinds := A[S:P[W], S = W == A[x:W, A[y:W, y < x -> y in S] -> x in S]]; // well-founded induction

!! Wfindf := A[f: fn(W, bool), A[x:W, f(x)] == A[x:W, A[y:W, y < x -> f(y)] -> f(x)]];

!! Wfind := A[x:W, P(x)] == A[x:W, A[y:W, y < x -> P(y)] -> P(x)];
!! TwfindE := E[x:W, P(x)] -> E[x:W, P(x) & A[y:W, y<x -> ~(P(y))]];        // is Axwf({x:W|P});

]; // wfrel :: [

begin("module equiv");   // equivalence relation 1/22/11
//  Relf := {A,R; A in set, AxR := R in fn(A#A,bool)};
eqvrel := {S,~; (~) in fn(S#S, bool),   
            AxRefl := A[x: S, x ~ x],
            AxSym := A[x,y: S, x ~ y -> y ~ x],
            AxTrans := A[x,y,z: S, x ~ y & y ~ z -> x ~ z] }; 
eqvrel :: [                 // 1 eqcl, qset

// !! Tprteqvr1 := g in fn(A,t) -> [A, F[x,y:A, g(x) = g(y)] ] in eqvrel;  moved to partition;

dcl[eqcl, fn(S, P[S]) ]; 
// eqcl :=  F[x:S, {z; z in S, z ~ x }]; 
!! Axeqcl := A[x:S, eqcl(x) = {z; z in S, z ~ x }];     // equivalence class
// eqclf := F[x:S, eqcl(x)];                            // same as eqcl

! Teqcl1 := A[x:S, x in eqcl(x)];                      // EqbyA Axab, 
! Teqcl2 := A[x:S, eqcl(x) ~= {}];
! Teqcl3 := A[x,y:S, x in eqcl(y) == x ~ y];
! Teqcl4 := A[x,y:S, x in eqcl(y) == y in eqcl(x)];
! Teqcl5 := A[x,y:S, x ~ y == eqcl(x) = eqcl(y)];
! Teqcl6 := A[x,y:S, x ~ y == eqcl(x) /\ eqcl(y) ~= {}];
! Teqcl7 := A[x:S, eqcl(x) <: S];

dcl[qset,P[P[S]] ];
// qset := R[x:S, eqcl(x)];            // quotient set is the set of all eqv.classes
!! Axqset :=  qset = R[x:S, eqcl(x)];
! Tqset := A[x:S, eqcl(x) = {y; y in S, x ~ y}];
! Tqsett := qset <: P[S];         // P[x] is the PowerSet of x;
! Tqsett1 := A[Q:qset, Q <: S];
! Lqset1 := union(qset) = S;
! Lqset2 := A[q1,q2: qset, q1 /\ q2 ~= {} -> q1 = q2];
! Tqsetprt :=  [S, qset] in partition;  // see 23 partition.v in snam
! Teqclt := eqcl in fn(S, qset);
! TeqcltA := A[x:S, eqcl(x) in qset];
! Tqset1 := A[Q:qset, x,y:Q, x ~ y];
! TeqclE := A[Q:qset, E[x:S, Q = eqcl(x)]];
! Tqset2 := A[Q:qset, Q ~= {}];
! Tqset3 := A[Q:qset, x:Q, eqcl(x) = Q];

]; // eqvrel :: [              // 1  eqcl, qset;
                     // partition := {A, B ; Axprt1 := A=union(B); Axprt2 := {} nin B; Axprt3 := A[Q1Q2_B, Q1 ~= Q2->Q1/\Q2 = {} ] };
partition :: [                 // 3 eqr
!! Tprteqvr1 := g in fn(A,t) -> [A, F[x,y:A, g(x) = g(y)] ] in eqvrel;
eqr := [A, eqf := F[x,y: A, cl(x)=cl(y)] ]; 
! Teqr := eqr in eqvrel;  is Tprteqvr1(Axcl1);      // Axcl1 := cl in fn(A,B); 
!! Teqr_eqcl := eqcl.eqr = cl;
!! Teqr_qset := qset.eqr = B;                      // !! Axqset :=  qset = R[x:S, eqcl(x)];
]; // partition :: [           // 3 eqr

FN :: [      // erf: f(x) = f(x1)
erf := [dom(f), erff := F[x,x1:dom(f), f(x) = f(x1)]];
!! Terf := erf in eqvrel;
!! Terf1 := qset.erf = im(qinv);
!! Tiq1 := iq in bfn(qset.erf, im(f)); 

];           // end FN :: [ // eqvr: f(x) = f(x1

begin("module int");   // in the directory Int 12/11/07  2/13/12 4/26/12
// OrderInt  := (int, <=);    TheIntegers := {int, 0, 1, +, '-unary', *, <= |
// AxAddGrInt := (int, 0, +, '-unary') in AbelGroup;

// dcl[int,set];
plint := dcl[+,int,int,int];
mnint := dcl[-,int,int,int];
mnint1 := dcl[-,int,int];

remint := dcl[%,int,nat1,nat];                                  // remainder
!! Tnatres := A[i:nat, m:nat1, E[n:nat, i = n*m + i%m]]; // actually, E1[

!! Tintmn0 := -0 = 0;
!! Tintmnmn := -(-k) = k;
mltint := dcl[*,int,int,int];
!! Tintmlt0 := k*0 = 0;
!! Tintmlt1 := k*1 = 1;
!! Tintmlt2 := (-k)*m = -(k*m);
!! Tintmlt3 := k<0 & m in nat -> -(k*m) in nat;
!! Tintmlt3a := k in nat & m < 0 -> -(k*m) in nat;
!! Tintmlt3a1 := k in nat & m < 0 -> k*(-m) in nat;
!! Tintmlt3b := k<0 & m in nat -> (-k)*m in nat;
!! Tintmlt4 := k < 0 & m < 0 -> k*m in nat;
!! Tintmlt5 := (-k)*(-m) = k*m;
!! Tintmlt5a := k*(-m) = -(k*m);
!! Tintdistr := A[x,y,z: int, (x+y)*z = x*z + y*z];
!! Tintdistr1 := A[x,z: int, (x+1)*z = x*z + z];
!! Tintdistr1a := A[z,x: int, z*(x+1) = z*x + z];
// dcl[||,int,int,bool];   // Axdivides := x||y == E[a:int, x*a = y];
!! Ax0t := 0 in int;
!! Ax1t := 1 in int;
leint := dcl[<=,fn(int,int,bool)];
!! Axle := k <= m == k<m or k=m;
!! Axreflle := A[x: int, x <= x];                           // Reflexavaty
!! Axintasymle := A[x,y: int, x <= y & y <= x -> x = y];    // intasymmetry
!! Axtrinsle   := A[x,y,z: int, x <= y & y <= z -> x <= z]; // Trinsatavaty 
!! Llege := k <= 0 -> -k >= 0;                              //  !! Tlege := k <= 0 == -k >= 0; 
dcl[<,int,int,bool];
!! Axlt := (<) = F[a,b: int, a < b == a <= b & a ~= b];
!! Tltt := (<) in fn(int#int, bool);
!! Tlint := A[a,b:int, a <= b == a < b or a = b];
!! Tltle := A[a,b:int, a < b -> a <= b];
!! Tltneq := A[a,b:int, a < b -> a ~= b];
!! Tlt1 := k < m == ~(k >= m);
!! Ttrinslt := A[a,b,k:int, a < b & b < k -> a < k];    // use Proofc, Tltle, Axtrinsle; 
!! Tintltle := k < m == k <= m-1;                       // A[k,m: int, k < m == k <= m-1];
!! Tintltle1 := k-1 < m == k <= m;

dcl[>,int,int,bool];
// !! Axgt := (>) = F[a,b: int, a > b == b < a];
!! Tgtt := (>) in fn(int#int, bool);
!! Tgtlt := A[a,b:int, a > b == b <= a & a ~= b];
!! Tgtle := A[a,b:int, a > b -> b <= a];
!! Tgtneq := A[a,b:int, a > b -> a ~= b];
!! Ttrinsgt := A[a,b,c:int, a > b & b > c -> a > c];    // use Proofc, Axgt, Ttrinslt, Axgt; 

dcl[>=,int,int,bool];
// !! Axge := (>=) = F[a,b: int, a >= b == b <= a];
!! Tget := (>=) in fn(int#int, bool);
!! Tgegt := A[a,b:int, a >= b == a > b or a = b];
!! Tgtge := A[a,b:int, a > b == a >= b & a ~= b];
!! Tgtge1 := A[a,b:int, a > b -> a >= b];    
!! Ttrinsge := A[a,b,c:int, a >= b & b >= c -> a >= c]; // use Proofc, Axge, Ttrinsle, -Axge; 
!! Tintgtge := A[k,m: int, k > m == k >= m+1];
!! Tgerefl :=  k >= k;                                  // >= is reflexive;
!! Lgeneg0 := ~(k >= 0) -> -k >= 0;                     // == -k in nat;

!! Tleeq := A[a,b: int, a = b -> a <= b];
!! comparable := A[a,b: int, a <= b or b <= a];
!! compatible := A[a,b: int, E[x: int, x <= a & x <= b]];
!! L1cc := comparable -> compatible;

// !! Ax2t := 2 in int;
!! Axiadd    := + @ plint in fn(int#int, int);        // see rnam: if M: dcl[w,...], w(M) denotes w;
!! Axiaddass := A[x,y,z: int, x+(y+z) = (x+y)+z ];
!! Axiaddcomm := A[x,y: int, x+y = y+x ];
!! Axii := - @ mnint1 in fn(int, int);
!! Axir0   := A[x:int, x + 0 = x];
!! Axirinv := A[x:int, x + (-x) = 0]; 
// AxMonoidInt := (int, 1, *) in CommMonoid;
!! Aximlt := * @ mltint in fn(int#int, int);
!! Aximltass := A[x,y,z: int, x*(y*z) = (x*y)*z];
!! Aximltcomm := A[x,y:int, x*y = y*x];
!! Aximlt1L := A[x:int, 1*x = x];                        // ??? twice ???
!! Aximlt1R := A[x:int, x*1 = x];                        
!! Axidistr := A[x,y,z: int, (x+y)*z = x*z + y*z];
!! Axordint     := [int, <= @ leint] in toset;                           // by Def; 
!! Axile        :=  <= @ leint  in fn(int#int, bool);
!! Axireflle    := A[x:int, x <= x];                            // Reflexivity
!! Axiantisymle := A[x,y:int, x <= y & y <= x -> x = y];        // Antisymmetry
!! Axitransle   := A[x,y,z:int, x <= y & y <= z -> x <= z];     // Transitivity
!! Axitotle     := A[x,y:int, x <= y or y <= x];                // Totality
!! Axordint1 := A[x,y,z:int, y <= z -> x + y <= x + z];         // isotonic for sums
!! Axordint2 := A[a,b,c:int, 0 <= a & b <= c -> a*b <= a*c];    // isotonic for pos. factors
!! Tint1 := A[k:int, k >= 0 or k < 0];
// ! Tint1a := A[k:int, k in nat or k < 0];
!! Tint1b := A[k:int, k in nat1 or k <= 0];
!! Tint2 := A[k:int, k in nat or k <= 0];
!! Tint3 := -(k-k1) = -k + k1;
!! Tint4 := (k-m) + m = k;
!! Tint5 := -k + m -k1 = -(k+k1) + m;
!! Tint6 := -(k + m) = -k - m;
!! Tint7 := -k + -m = -(k + m);

dcl[even, fn(int,bool)];
!! Axeven := A[k:int, even(k) == k%2 = 0];

abs := F[k:int, if(k>=0, k, -k)];           // was  dcl[abs,int,nat];
!! Labs1 := A[k:int, abs(k) in nat];
!! Labs2 := A[i,j:int, i ~= j -> abs(i-j) ~= 0];
!! Labs3 := A[i,j:int, i ~= j -> abs(i-j) in nat1];
!! Labs4 := A[m:nat1, i,j: 0..m-1, i~=j -> abs(i-j) < m];

Axnat := nat = {n; n in int, n >= 0};                            // natural numbers
i_nat := {i; i in nat};
!! Tnat0 := k in nat == k >= 0;                                  // var k,...,int;
!! Tnat0a := k in nat == -k <= 0; 
!! Tnat1 := -k in nat == k <= 0;
!! Tnat2 := -k in nat <- ~(k >= 0);
!! Tnat3 := -k in nat <- k <= 0;
!! Tnat4 := nat ~= {};
!! Tnat5 := k < 0 -> -k in nat;
!! Tnat6 := k in nat1 -> k-1 in nat;
!! Tnat7 := n <= 1 -> n=1 == ~(n=0);           // var n, nat;  // see root.v
!! Tnatorlt0 := k in nat or k < 0;
!! Tnatadd := A[k,m:nat, k+m in nat];
!! Tnatmlt := A[k,m:nat, k*m in nat];

!! Lle0 := (<=(leint)) in REL;                                           // ??? in fn(int,int,bool);
!! Tnatint := nat <: int;
nat1 := {n; n in int, 1 <= n};
!! Tnat1in := x in nat1 == x in int & x >= 1;
!! Tnat1int := nat1 <: int;
!! Tnat1nat := nat1 <: nat;
!! Tnat1z := x1 in nat1 -> x1 > 0;
!! Lnat1nz := x in nat1 -> x ~= 0;
!! Tnat1in1 := x in nat1 == x in nat & x ~= 0;

ordernat := [nat, (<=(leint))|(nat#nat)];
!! Axordnat := ordernat in woset;                                // well ordered set     
!! Tnatdecr := A[f: fn(nat,nat), ~A[k:nat, f(k+1) < f(k)]];
!! Tnatneqlt := A[n:nat, n ~= 0 == n > 0];
!! Tnatle2 := A[n:nat, n <= 2 == n=0 or n=1 or n=2];
neg := {n; n in int, n < 0};
!! Axnegt := nat1 <: int;
!! Tneg1 := A[n:int, Q(n)] == A[n:neg, Q(n)] & A[n:nat, Q(n)]; 
nat1 :: !! Tnat1_or :=  n=1 or n>1;                                // ???
dcl[divisors,int,P[nat1] ];
!! Axdivisors := A[n:nat, divisors(n)= {k; k in nat1, E[m:int, k*m = n] }];    // ?? k:nat  

// dcl[prime, nat, bool];
prime := F[n:nat, n > 1 & divisors(n) = {1,n}];
!! Tprime := A[n:nat, prime(n) == n > 1 & divisors(n) = {1,n} ];

primes := {k; k in nat2, prime(k) };
!! Tprimes := primes <: nat2;
primedivs := F[n:nat2, {p; p in nat, p in divisors(n); prime(p)} ];
!! Tprimedivs := primedivs in fn(nat2, P[primes]); 
dcl[comp,nat,bool];     // composite number
!! Axcomp := A[n:nat, comp(n) == ~prime(n)];
// var n1, nat1; 
!! Lmin1 := A[n:nat1, n-1 in nat];
n_nat := {n; n in nat};
dcl[!, fn(n_nat,nat)];          postfix;  recdef;   // factorial n!                 
!! Axfact0 := 0! = 1;   
!! Axfact1 := A[n_nat, (n+1)! = n! * (n+1)];
! Lfact0 := 1 in nat;                        is typeaxiom;                      
!! Tfact2 := A[n:nat, n! + 1 in nat2];
// !  arb(primedivs(n! + 1)) in int;         // for >
! primes <: int;                             // for

// begin("module Mathind");   // Mathematical Induction 12/01/08 12.10 12.21 
var ff, fn(nat, bool); var ff1, fn(nat1, bool); 
!! Axnat1nat := nat1 <: nat; // ! Lnatplus1; // n0+1 in nat;         // ! Lnatplus1 := A[m:nat, m+1 in nat]; ??? ploop !
!! Mathinds := A[S: P[nat],  S = nat == 0 in S & A[k:nat, k in S -> k+1 in S]];
!! Mathindf := A[n:nat, ff(n) ] == ff(0)  & A[k:nat, ff(k) -> ff(k+1)];
!! Mathind := A[n:nat, P(n)] == P(0) & A[k:nat, P(k) -> P(k+1)];
!! Mathindwf := A[n:nat, ff(n) ] == A[n:nat, A[k:nat, k<n -> ff(k)] -> ff(n)]; // is Wfindf(nat, <);
!! Mathindwf0 := A[n:nat, ff(n) ] == ff(0) & A[n:nat1, A[k:nat, k<n -> ff(k)] -> ff(n)];

!! Mathindrf := A[S:set, g:fn(S,nat), f:fn(S,bool), A[x:S, f(x)] == (Basis := A[x:S, g(x)=0 -> f(x) ]) 
                & (Step := A[k:nat1, A[x:S, g(x) < k -> f(x)] -> A[x:S, g(x)=k -> f(x) ]]) ];


// !! Mathindfr := A[{f:prop, g:fn(dom(f), nat))},  All(f) == (Basis := A[x:S, g(x)=0 -> f(x))] 
//                & (Step := A[k:nat1, A[x:S, A[x:S, g(x) < k -> f(x)] -> g(x)=k -> f(x)]];

//  !! Mathindr := A[G:nat, A[d,P] == (Basis1 := A[d, G=0 -> P]) &
//                                             (Step1 := A[k:nat1, A[d, G<k -> P] & G=k -> P])]; 
// var mnd, nat;   // mnd: method nat for d;      // move up, where d is defined;
 !! Mathindr := A[mnd:nat, A[d,P] == A[d, mnd=0 -> P] & A[k:nat1, A[d, mnd < k -> P] -> A[d, mnd = k -> P]]]; 

// !! Mathindr(d::G:nat)(d,P) := A[d,P] == (Basis := A[d, G=0 -> P]) &   // Non-symmetric formula, G - the 
//                                        (Step := A[k:nat1, A[d, G<k -> P] -> A[d, G=k -> P)]]); 

// RedFamSet := {B: P(set) | A[Z:B, fin(Z) & Z--{arb(Z)} in B]};
// RedFamSet :: !! FSind(B) := A[Z:B, Q(Z)] == Q({}) & A[Z:B, x:any, Z\/{x} in B & Q(Z) -> Q(Z\/{x})];

dcl[..,int,int,P[int]];
!! Axseg := A[k,m:int, k..m = {n; n in int, k<:n, n<:m}];
!! Tsegin1 := A[k,m,n:int, n in k..m == k<:n & n<:m];
!! Tseg1 := A[k:int, k+1..k = {}];	 
!! Tseg2 := A[k,m,n:int, k in m..n == k+1 in m+1..n+1];
!! Tseg3 := A[k,m,k1,m1:int, k..m = k1..m1 == k=k1 & m=m1];
!! Tseg4 := k <= m -> A[n: k..m, Q(n)] == Q(k) & A[n: k+1..m, Q(n)];    // ??? Q: replace with ff ???
// ! Tseg5(k,m,a:int) := A[i:k+a..m, Q(i)] == A[i:k..m-a, Q(i-a)];
!! Tseg5 := k..m <: int;
!! Tseg6 := 0..m <: nat;
!! Tseg7 := 1..m <: nat1;
!! Tseg8 := A[i:1..m, Q(i)] == A[i:0..m-1, Q(i+1)];                     // ??? Q: replace with ff ??
!! Tseg9 := 0 in 0..n1-1;

dcl[ige,int,P[int] ];
!! Axige := A[n:int, ige(n) = {k; k in int, n <= k}];      // integers, greater than or equal to n
!! Tigenat := nat = ige(0);
!! Tigenat1 := nat1 = ige(1);

natm := ige(-1);
!! Tnatmt := natm <: int;
segm0 := R[n:natm, 0..n];                                // segm0 := R[n:natm, 0..n_natm???];
!! Tsegm0in := All(s, s in segm0 == E[k:natm, s = 0..k]);       // is TRin;
!! Tsegm0E1 := A[S:segm0, E1[k:natm, S = 0..k]];

dcl[upbound,segm0,natm];
!! Axupbound := A[S:segm0, upbound(S) = the({k; k in natm, S = 0..k})];

segmint := R[a,b:int, a..b];

!! Tsegmintin := All(x, x in segmint == E[a,b:int, x = a..b]);
!! TRsegm01 := R[k:0..1, G(k)] = {G(0), G(1)};

dcl[<=,int,P[int], bool ];
dcl[lboundedint,P[int],bool];
!! Axlboundedint := A[S:P[int], lboundedint(S) == S ~= {} & E[a:int, a <= S] ];
// ! L0 := x <: A == x in P[A];

lbint := {S; S in P[int], lboundedint(S)};
!! Tlbint0 := lbint <: P[int];
!! Tlbint1 := P[nat1] <: lbint; 
!! Tlbint2 := S <: nat1 & S ~= {} -> S in lbint;

dcl[min,lbint,int];
// !! Axmin := A[S:P1[int], min(S) = the(mins(S))];
!! Tmin1 :=  A[S:lbint, min(S) in S];
// ! Tmin2 :=  A[S:lbint, mins(S) <= S];
!! Tmin3 :=  A[S:lbint,x:int, x < min(S) -> x nin S];
!! Lmin4 := (S3 := {k:nat1; P(k) }) in lbint -> A[k:1..min(S3)-1, ~(P(k))];
// ! L00 := {x; x in t; Q} <: t;

tdomff := {i; i in nat, ff(i)};
exff := E[i:nat, ff(i)];
// igekQ := {i; i in ige(k), Q(i)};
!! L01 := {i; i in ige(k), Q(i)} in lbint;
!! L02 := exff -> tdomff in lbint;
!! L02a := exff -> min(tdomff) in nat;
!! L03 := {i; i in nat1, Q(i)} in lbint;
tdomff1 := {i; i in nat1, ff1(i)};            // var ff, fn(nat, bool); var ff1, fn(nat1, bool); 
exff1 := E[i:nat1, ff1(i)];
!! L17 := exff1 -> tdomff1 in lbint;
!! L18 := exff1 -> min(tdomff1) in nat1;
SQ := {i; i in ige(k), Q(i)};
! Tminige0 := ige(k) in lbint;
!! LSQ1 := SQ ~= {} -> SQ in lbint;
!! Tminige := SQ ~= {} -> (m = min(SQ) == Q(m) & A[j:k..m-1, ~(Q(j))]); // was E[i:ige(k), Q(i)] -> (m = min
!! Lmm := exff -> (mm := min(tdomff))  in nat;
!! Tminnat := exff -> ff(mm) & A[i:0..mm-1, ~(ff(i))];
!! Tminnat1 := exff1 -> ff1(mm1 := min(tdomff1)) & A[i:1..mm1-1, ~(ff1(i))];

/*
  M := min({k; k in nat1, P});        // ??? k; k in nat1, P} in lbint ???   2022.04.24
!! Tminnat1a :=  E[k:nat1, P] -> M in nat1 & P(M) & A[k:1..M-1, ~(P(k))];
!! Lff1a := ff1(2) -> exff1; 
!! Tminnat1_1 := ~(ff1(1)) & ff1(2) -> min(tdomff1) = 2;  
*/

// dcl[equip,set,set,bool];     // equipollent
dcl[fin,set,bool];
dcl[fin1,set,bool];
dcl[infinite,set,bool];

dcl[FS,set,set];         // finite subsets of A
// !! AxFS := X in FS(A) == X <: A & fin(X);        // finite subsets of A
!! AxFS := X in FS(A) == X <: A & X in finset;        // finite subsets of A

dcl[FS1,set,set];        // nonempty finite subsets of A
!! AxFS1 := X in FS1(A) == X <: A & fin(X) & X ~= {};

finset := {A; Ax1 := fin(A)};      // dcl[finset,set];     // the set(class) of all finite sets // ob'em(fin) = finset;
!! Tfinsetemp := {} in finset;
!! TfinsetS := {X} in finset;      // was Tfinset1;
!! Tfinset1 := X in finset1 == X in finset & X ~= {};  // rename existing Tfinset1 to Lfinset1;
!! Tfinset2 := X in finset & a in X & b in X & a ~= b -> #X > 1;
!! Tfinset := {a,b} in finset;                   // var ee, enumterm; ...  ee in finset;
!! TfinsetIn := A in finset & B <: A -> B in finset;
!! Lfinset1In := finset1 <: finset;
!! TfinsetR := X in finset -> R[x:X, g] in finset;
!! TfinsetRseg := R[k:i..j, g] in finset;

dcl[#,finset,nat];                               // the number of elements of a finite set
!! Axfin := All(A, fin(A) == E[S:segm0, A ~ S]);
!! Axfin1  := fin1(A) == fin(A) & A ~= {};
!! Axfinset := X in finset == fin(X);
!! TfinsetIn1 := A in finset & B <: A -> B in finset & #B <= #A;
!! Axinfinite := infinite(A) == ~fin(A);

!! TFS1 := FS1(A) = {x; fin(x) & x <: A};      // finite subsets of A
!! Axcard := fin(X) -> X ~ 1 .. #X;
!! Tfin1 := A[s:segm0, fin(s)];   // use s~s;
!! TfinN := ~fin(A) -> A ~= {}; 
!! TfinS := fin({A});
!! TfinI := fin(A) ->  fin(A/\B);
!! TfinD := fin(A) -> fin(A--B);

!! TfinD1 :=  ~fin(A) & fin(B) -> ~fin(A--B);
!! TfinD2 := ~fin(A) & fin(B) -> A--B ~= {};
!! TfinUS := fin(A) -> fin(A\/{x});
!! TinfinE := infinite(A) & fin(B) -> E[c:A, c nin B];
!! TfinR  := fin(d) -> fin(R[d, f]);
!! TfinDP := fin(A) & fin(B) == fin(A # B);
!! TfinIn := fin(B) & A <: B -> fin(A);
!! TFSm := A <: B -> FS(A) <: FS(B);        // FS is monotone
!! TFS0 := FS(A) <: finset;
!! TFS2 := B in FS(A) & B1 <: B -> B1 in FS(A);
!! TFS3 := B in FS(A) -> B -- C in FS(A);
!! TFS4 := B in FS(A) & x in B -> x in A;
!! TfinE1 := A[A:finset, E1[S:segm0, A ~ S] ];
!! Tcardnz   := A[A:finset, #A ~= 0 == A ~= {}];
// ! Tcardt := #A in nat;
!! Tsegm0fin := A[S:segm0, fin(S)];

!! TfinIn1    := fin(B) & A <: B -> fin(A) & #A <= #B;
!! TfinFS     := fin(A) == E[k:nat, A[B: FS(A), #B <= k]];
!! Tcardemp   := #{} = 0;
!! Tcard1     := #{X} = 1;
!! Tcard2a    := a ~= b == #{a,b} = 2;
!! Lsegm01 := segm0 <: finset;
!! Tsegm01 := A[S:segm0, S = 0 .. #S-1];  

finset :: [
x_A := {x; x in A}; B_PA := {B; B in P[A]};                   // x_any := {x; x in any};
!! L0       := A in finset;
!! Tcard2b  := #A = 2 & a1 in A & b1 in A & b1 ~= a1 -> A = {a1,b1};
!! Tcardgt  := #A > 0 == A ~= {}; 
!! Tcardz   := #A = 0 == A = {};
!! L00      := A[x_A, A--{x} in finset]; 
!! TcardD1  := A[x_A, #(A--{x}) = #A - 1];                     // with Obv(k-1<k); // Tcard1
!! TcardD1a := A[x_A, #(A--{x}) < #A];
!! L01      := A \/ {x} in finset;                  // was A[x: any, A \/ {x} in finset];
!! TcardU1  := x nin A -> #(A \/ {x}) = #A + 1;     // was A[x: any, x nin A -> #(A \/ {x}) = #A + 1]; 
!! L02      := A -- B in finset;                    // was A[B: P1[A], A -- B in finset];    
!! TcardD   := #(A -- B) < #A;                      // was A[B: P1[A], #(A -- B) < #A];
!! L03      := R[x_A, {x}] in finset;
!! TcardRS  := #R[x_A, {x}] = #A;                                  // is TeqpR ! Tfineqp;
!! L04      := fin(A#B) -> A#B in finset & B in finset;
!! TfinDp   := fin(A#B) -> #(A#B) = (#A) * (#B); // Dp: Direct Product
!! Tcard2   := A[x,y:A, x~=y -> #A > 1];
!! TcardE1  := one(A) == #A = 1;
!! Tcard2E  := #A = 2 == E[a,b:A, a ~= b & A = {a,b}];
!! TcardE   := #A > 0 == Exist(x, x in A);
!! TcardE2  := #A = 2 & a in A -> Exist(b, b in A & a ~= b & A = {a,b});   // ???
B_PA :: [ !! L05 := B in finset; ];                 // was B in P[A] -> B in finset;          
!! Tcardsub := A[k: 0 .. #A, E[B_PA, #B = k]];      // was A[k: 0 .. #A, E[B: P[A], #B = k]];  B's were different;
!! Tcard1E  := #A = 1 == E[x_A, A = {x}];
]; // finset :: [

finset1 := finset && (Ax2 := A ~= {});    // finset := {A; Ax1 := fin(A)};
finset1 :: [   // ??? Aset :: [ ???  // finset := {A; Ax1 := fin(A)}; finset1 := finset && (Ax2 := A ~= {});
compA := F[f,g:afn(A), f o g];       // comp: composition;        // !! Tafn6 := A[f,g,h: afn(A), f o (g o h) = (f o g) o h];
! LcompA_type := compA in fn(afn(A)#afn(A),afn(A));    is Tafn2;  // !! Tafn2 := F[f,g: afn(A), f o g] in fn(afn(A)#afn(A), afn(A));         
! LcompAass := A[f,g,h:afn(A), compA(f, compA(g,h)) = compA(compA(f,g),h)]; by Red("F"),Red("F"),Red("F"),Red("F"); is Tafn6; 
! L1 := id(A) in afn(A);                               is Tafnid;   // e1
// !! L2 := inv(compA) in fn(afn(A),afn(A));           // WRONG !!! was not caught !!!
xafnA := {x; x in afn(A)};
inv0 := F[xafnA, inv(x)];                           // next line: ! L2_type := inv0 in fn(afn(A),afn(A)) did not work !!! see typeth(...) !!!
! Linv0_type := inv0 in fn(afn(A),afn(A));          is Tafn3;                        // !! Tafn3 := F[f: afn(A), inv(f)] in afn(A);
! L3 := A[xafnA, compA(x,id(A)) = x];               by Red("F"); is Tafn4;           // !! Tafn4 := A[f: afn(A), f o id(A) = f];   
! L4 := A[xafnA, compA(x,inv0(x)) = id(A)];         by Red("F"), Red("F"); is Tafn5; // !! Tafn5 := A[f: afn(A), f o inv(f) = id(A)]; 
! Leinv := E[e1:afn(A), inv1:fn(afn(A),afn(A)),                                      // inv0 := F[xafnA, inv(x)];    
                A[xafnA, compA(x,e1) = x] & A[xafnA, compA(x,inv1(x)) = e1]]; is Witness(id(A), inv0);
// Sym := [afn(A), compA];            // symmetric group Sym(A); see altg.v
// ! TSym := Sym in group;      by Tingroup;  LcompA_type & LcompAass & Leinv; 
]; // finset1 :: [

finset2 := {A,B; AxA := A in finset, AxB := B in finset};
finset2 :: [
!! TcardIn    := A <: B -> #A <= #B;
!! Tfineqp    := A ~ B == #A = #B;   // ~ : equipollent
!! LcardU := A \/ B in finset;
!! LcardI := A /\ B in finset;
!! TcardUD :=  #(A \/ B) = #A + #B - (#(A /\ B));    // see TfinU ??? - was parsed as postfix ???
!! TcardU  := A/\B = {} -> #(A \/ B) = #A + #B;   // see TfinU
!! TfinInN := A <: B & #B <= #A -> A = B;
!! TfinInN1 := A <: B & #B = #A -> A = B; 
!! TcardI1 := #(A/\B) <= #A;
!! TcardI2 := #(A/\B) <= #B;
!! TcardIeq1 := #(A/\B) = #A == A <: B; 
!! TcardIeq2 := #(A/\B) = #B == B <: A; 
!! TcardIeq3 := #(A/\B) = #A  &  #(A/\B) = #B  ==  A = B; 
]; // finset2 :: [       

dcl[dif3,any,any,any,bool];           // all a,b,c are pairwise differeny;
!! Axdif3 := A[a,b,c:any, a ~= b & a ~= c & b ~= c];
dcl[BFN,set];
!! AxBFN := f in BFN == E[A,B:set, f in bfn(A,B) ];
  
coll22 := {X,Y; AxX := X in finset, AxY := Y in finset, AxX2 := #X = 2, AxY2 := #Y = 2};
coll22 :: [
Z := X/\Y;
!! TZfin := fin(Z);                                                  // is TfinI;
!! TZfin1 := Z in finset;
!! TZle2 := #Z <= 2;                                                 // is TcardI1;
!! TZeq := #Z = 2 == X=Y;                                            // is  TcardIeq3;
!! TZor := xor3(#Z = 0, #Z = 1, #Z = 2);                             // is Tnatle2; by Tcardz,TcardE1, 
!! TS2a0 := xor3(X NI Y, one(X/\Y), X=Y);                            // is TZor ! Tcardz ! TcardE1 ! TZeq;
!! TS2a := X NI Y or one(X/\Y) or X=Y;                               // is TS2a0 ! Taut(TS2a0 -> TS2a);
!! TZE1 := one(X/\Y) -> X~=Y;                                        // is TS2a0 ! Taut(TS2a0 -> TZE1);
!! TS2b := one(X/\Y) == E[a,b,c:any, dif3(a,b,c) & X = {a,b} & Y = {a,c}]; ///
]; // coll22 :: [
FN :: [
!! TFN4 := infinite(dom(f)) & fin(im(f)) -> E[a,b:dom(f), a ~= b & f(a)=f(b)];
!! TFN5 := dom(f)=nat & fin(im(f)) -> E[a,b:nat, a ~= b & f(a)=f(b)];
]; // FN :: [

!! LafnAFN := afn(A) <: AFN;
!! Lafn2 := A in finset & f in fn(A,A) & injective(f) -> f in afn(A);

// Finite domain functions 6/19/08 2/13/08 9/02/10

// FFN := {f; Axf := f in FN, Axf1 := fin(dom(f)) };
FFN := FN && fin(dom(f));                                           // line 4001, not 4002;
! TFFNREL := FFN <: REL; ! TFFNFN := FFN <: FN;
dcl[ffn1,set,set];
!! Axffn1 := f in ffn1(B) == f in FN & im(f)<:B & fin(dom(f));
!! Tffn0 := ffn1(B) = {f; f in FN, fin(dom(f)), im(f) <: B};
!! Tffnnemp := ffn1(B) ~= {};         // {} in ffn1(B);
dcl[---, FFN, set, FFN];
FFN :: [
!! L0 := f in FFN;
!! Tfunre1 :=  f---A in REL;                    // was: ! Tfunre1 := A[f:FFN, f---A in REL];
!! Axfunre := f---A = f|(dom(f)--A);           // was !! Axfunre := A[f:FFN, f---A = f|(dom(f)--A)];
!! Lfunre0 := dom(f) in finset;                 // was: ! Lfunre0 := h in FFN -> dom(h) in finset;
!! Lfunre1 := dom(f---A) in finset;             // was: ! Lfunre1 := h in FFN -> dom(h---A) in finset;
!! Lfunre2 := im(f) in finset;                  // was: ! Lfunre2 := h in FFN -> im(h) in finset;
!! Tffn2 := A[a: dom(f), #dom(f---{a}) = #dom(f) - 1];                          // look for old Tffn2 below;
!! Tffn2a := A[a: dom(f), #dom(f---{a}) < #dom(f)];                             // look for old Tffn2a below;
!! Tffn3 := A[a: dom(f), dom(f---{a}) << dom(f)];                               // look for old Tffn3 below;
!! Tffn8 := fin(im(f));                         // was: ! Tffn8 := A[f: FFN, fin(im(f))];
!! Tffn9 := #im(f) <= #dom(f);                   // was: ! Tffn9 := A[f: FFN, #im(f) <= #dom(f)]; see below;
!! Tffn11 := #im(f) < #dom(f) -> E[x1,x2: dom(f), x1 ~= x2 & f(x1) = f(x2)];    // look for old Tffn11 below;
!! Tffn12 := #im(f) = #dom(f) == f in BFN;                                      // look for old Tffn12 below;
]; // FFN :: [

!! Lfinset0 := fin(A) == A in finset;           // ??? move to near finset definition ???
dcl[ffn,set,set,set];                          // ??? type of ffn will be incorrect: set, not fn(set#set,set);
!! Axffn2 := ffn(A,B) = {g; g in FN, dom(g) <: A, fin(A), im(g) <: B};
!! Tffn00 := f in ffn(A, B) == f in FN & dom(f)<:A & fin(A) & im(f)<:B;
!! Tffn1 := ffn(A, B) <: FFN;       // A[A, B: set, ffn(A, B) <: FFN];
// ! Tffn2 := A[h: FFN, a: dom(h), #dom(h---{a}) = #dom(h) - 1];      // was #dom(f--{a})
// ! Tffn2a := A[f: FFN, a: dom(f), #dom(f---{a}) < #dom(f)];         // was #dom(f--{a})
// ! Tffn3 := A[f: FFN, a: dom(f), dom(f---{a}) << dom(f)];
!! Tffn4 := A[A,B,C:set, f in fn(A,B) & A in FS(C)-> f in ffn(C, B)];
!! TffnM := A[A,B: finset, C: set, A <: B -> ffn(A, C) <: ffn(B, C)]; 
!! Tffn5 := A[A,B,C: set,f1: ffn(A, C), f2: ffn(B, C), A NI B -> dom(f1) NI dom(f2)={}]; 
!! Tffn6 := f in fn(A, B) & fin(A) & A <: C -> f in ffn(C, B);
!! Tffn7 := f in ffn(Y\/{x}, B) -> f---{x} in ffn(Y, B);
!! Tffn7a := f in ffn(Y, B) & a in dom(f) -> f---{a} in ffn(Y, B);
// ! Tffn8 := A[f: FFN, fin(im(f))];
// ! Tffn9 := A[f: FFN, #im(f) <= #dom(f)];
!! Tffn10 := A[f: FN, A: P[dom(f)], fin(A) -> f|A in FFN];
// ! Tffn11 := A[f: FFN, #im(f) < #dom(f) -> E[x1,x2: dom(f), x1 ~= x2 & f(x1) = f(x2)]];
// ! Tffn12 := A[f: FFN, #im(f) = #dom(f) == f in BFN];
FN :: !! L07 :=  fin(dom(f)) -> dom(f) in finset & im(f) in finset;
FN :: !! Tffn12a := fin(dom(f)) -> fin(im(f)) & #im(f) <= #dom(f);   // was fin(dom(f))
!! Tffn13 := A<:A1 & B<:B1 & f in ffn(A,B) -> f in ffn(A1,B1);
/*   commented on 2022.10.26
FFNS := {f; Axf := f in FFN, Axf1 := A[x:dom(f), f(x) in finset] };

FFNS :: [
dxdomf := {x; Ax1 := x in dom(f) } ;
!! Tdxdomf := dxdomf in finabterm;
dxdomf :: !! L0 := f(x) in finset;
ddp := {x,y; x in dom(f), y in f(x)};
!! Tddpfin := fin(ddp);  // by induction on #dom(f)
!! Tddpfinset := ddp in finset;
!! TddpN := #ddp = S[dxdomf, #(f(x))];
!! TddpN1 := #ddp = S[dxdomf, #(f(x))];
]; // FFNS :: [
*/
finpartition := partition && ( Axfinprt := fin(A) );   // 4.18.20: PROBLEM: not checked: && [Axfinprt := fin(A)
finpartition :: [
!! L0 := A in finset;
!! L01 := B in finset;
!! Tfinprt1 := fin(B);                       // fin(union(B)) -> fin(B);
!! Tfinprt2 := A[Q:B, Q in finset];
!! TfinprtS := #A = S[Q:B, #Q];               // from A = U[Q:B, Q];
!! Tfinprt4 := A[Q:B, #Q > 0];
!! Tfinprt5 := A[n:nat, #A = n & A[Q:B, #Q >= n] -> #B = 1];
!! Tfinprt6 := A[n:nat, A[Q:B, #Q >= n] -> #A >= #B * n];
!! Tfinprt7 := A[Q:B, Q=A] == #B = 1;                       // use Tcl5;
Fnum := F[Q:B, #Q];                          // number of a member of B; 
];    

eqfinpartition := finpartition && (AxC := Fnum in CFN);

SEQ := FN && (Axdom := dom in segm0);   // segm0 := R[n:natm, 0..n]; natm = {k:int | k >= -1};
!! TSEQ0 := {} in SEQ; 
!! LSEQ0 := All(x, [x] in SEQ);
!! LSEQ1c1 := All(x, [x] in SEQ1);            // move out SEQ1 !!!
!! LSEQ1S0 := [x](0) = x;
!! LSEQ1im := im([x]) = {x};

var u0,v0, SEQ;
dcl[l,SEQ,nat];
dcl[last,SEQ,natm];
!! Axlast := last(u0) = l(u0)-1;
!! LlastF0 := F[i:0..n_natm, Q] in SEQ;
!! TlastF := A[n:natm, last(F[i:0..n, Q]) = n];
!! Llast0 := l(u0) >0 -> last(u0) in dom(u0);
!! LSEQim1 :=  x in im([x]);

SEQ :: [
!! TSEQE := E[n:natm, dom(f) = 0..n];                       // is Tsegm0in ! Axdom;
!! TSEQE1 := E1[n:natm, dom(f) = 0..n];                     // is Tsegm0E1(dom);
!! TSEQfin := fin(dom(f));                                  // is Tsegm0fin(dom); line 4089, not 4090;
!! L0 := SEQ <: REL;
!! L00 := f in SEQ;                                         // ??? this ???
!! L0a := dom(f) in finset;
!! Axl := l(f) = #dom(f);
!! Tlt := l(f) in nat;                                      //   is Tcardt;
!! Tldom  := dom(f) = 0 .. l(f)-1;                             // is Tsegm01;
!! Tldom1 := dom(f) = {} == l(f) = 0;                          // by Axl; Tcardz; by Teqvneg;    
!! Tldom2 := dom(f) ~= {} == l(f) ~= 0;                        // by Tnatneqlt;        
!! Tldom3 := dom(f) ~= {} == l(f) > 0;
!! LSEQim := x in im(f) -> f in SEQ1; 
!! TSEQafn := afn(dom(f))  <: SEQ; 
!! L01 := f in FN;  
!! L02 := dom(f) <: int; 
// ! L07 := last(f) in int;
!! Tlast1 := dom(f) = 0 .. last(f);         // is Tl2 ! Axlast;
!! Tlast2 := last(f) < l(f);
!! Tlastt := last(f) in nat;
!! Llast0 := last(f) = 0 -> 0 in dom(f);
!! Tlast0 := last(f) = 0 -> f = [f(0)];    // ??? checking f(0) ??? uses meth, abtyp, prevt;
!! Tlastl := l(f) = last(f)+1;
!! Tlast3 := A[i:dom(f),  last(f)-i in dom(f)]; 
!! Llastim3 := last(f)>=3 -> 0 in dom(f) & 1 in dom(f) & 2 in dom(f) & last(f) in dom(f);    // line 4110, correct !!! 1 in dom(f)
!! Llastim3a := last(f)>=3 -> 3..last(f)-1 <: dom(f);
!! Tlastim3 := last(f)>=3 -> im(f) = {f(0),f(1),f(2),f(last(f))} \/ R[i:3..last(f)-1,f(i)];
!! Tlastim3A := last(f)>=3 -> All(z, z in im(f) == z=f(0) or z=f(1) or z=f(2) or z=f(last(f)) or z in R[i:3..last(f)-1,f(i)]);
]; // SEQ :: [

!! TSEQFN := SEQ <: FN;                                     // is TscIn;
!! TSEQt := SEQ <: FFN;                                     // is TscIn3???;
!! TFSEQ := F[i:0..k, g] in SEQ;
!! TFl := l(F[i:0..n1-1, G(i)]) = n1;
!! LFmnat := F[i:0..k, G(i)] <: F[i_nat, G(i)];
!! LFimnatIn := im(F[i:0..k, G(i)]) <: im(F[i_nat, G(i)]);
!! LFimseg := im(F[i:0..k, G(i)]) in finset;
dyz := {y,z; y in SEQ; z in SEQ; };
dyz :: [
!! TSEQdoml := dom(y)=dom(z) == l(y)=l(z); // byeq Tldom, Tseg3, 
!! TSEQeq := y = z == l(y) = l(z) & A[i: dom(y), y(i) = z(i)] ;
]; // dyz :: [

!! TSEQF := A[n: natm, F[k:0..n, Q] in SEQ];                 // ?? Q not defined??
!! TSEQFl := A[n: natm, l(F[k:0..n, Q]) = n+1]; 
      
SEQ1 := SEQ && (AxSEQ1 := l(f) ~= 0);                        // moved here because Lseq6 uses AxSEQ1;

dcl[seq,set,set];             // var ss, seq(int);
!! Tseqin := z in seq(A) == z in SEQ & im(z) <: A;
!! Tseq := seq(A) = {z; z in SEQ, im(z) <: A};
!! Tseqim := z in seq(A) -> im(z) <: A;
!! TseqinA := z in seq(A) == z in SEQ & A[k:dom(z), z(k) in A];
!! TseqF := A[n:natm, Q in A -> F[k:0..n, Q] in seq(A)];
// !! SeqInd := A[z:seq(A), Q(z)] == Q([]) & A[z:seq(A), x:A, Q(z) -> Q(z^[x])];
!! Axseq := seq(t) <: FN; 
!! Lseq0 := seq(t) <: SEQ; 
!! Lseq0a := x in seq(t) -> x in SEQ;
!! Lseq1 := seq(t) <: REL;
!! Tseq1 := A[z:seq(t), dom(z) in segm0];
!! Lseq2 := A[z:seq(t), im(z) <: t]; 
!! Lseq3 := A[z:seq(t), dom(z) <: int];
!! Lseq4 := z in seq(A) -> (z ~= [] -> z in SEQ1);
!! Lseq5 := z in seq(A) -> (z ~= [] -> 0 in dom(z));
!! Lseq6 := z in seq(A) -> (z ~= [] -> Last(z) in A);
!! Tseqmon := A <: B -> seq(A) <: seq(B);             // Lseq7 is below;
!! Lseqlz := l(u0)=0 == u0=[];

monseqint := {z; Axtz := z in seq(int),  dom(z) <: int, Axmon := A[i:dom(z), i+1 in dom(z) -> z(i) <= z(i+1) ] }; 
// dseqint :: ! Lseq3 := dom(z) <: int;
// dseqint :: !! \Axmonotone := A[i:dom(z), i+1 in dom(z) -> z(i) <= z(i+1) ];  // was A[z:seq(int), ...
dcl[monotone, seq(int), bool];
!! Axmonotone := A[z:seq(int), monotone(z) == z in monseqint];
!! Lmonotone := seq(nat) <: seq(int);
nat2 := ige(2);
!! Lnat2nat := nat2 <: nat;

dcl[prod, seq(int),int];              // product of all elements of a sequence
// !! Axprod1 := A[z:
!!Lseqnat := seq(nat) <: seq(int);
 
dcl[pf,nat,seq(nat)];                 // prime factorization
!! Axpf := A[n:nat, monotone(pf(n)) & prod(pf(n)) = n & A[j:dom(pf(n)), prime(pf(n)(j))]];
// ! Tprime1 := A[n:nat2, E1[s:seq(primes), monotone(s) & prod(s) = n]]; // by TfnAE1; // move after monoid
// ! Tprime2 := E1x[ps, Axps := ps in fn(nat2, seq(primes)), 
// ! Tprime3 := A[n:nat2, monotone(ps(n) & prod(ps(n)) = n]]; 

dcl[psp,nat2,natm,seq(nat)];
// psp(n:nat2, k: dom(ps(n)) := II[i: k+1..last(ps(n)), ps(i)];
// ! Tpsp0 := A[n:nat2, psp(n,0) * ps(n)(0) = n];
// ! Tpsp1 := A[n:nat2, i:1..last(ps(n)), psp(n,i) * ps(i) = psp(n,i-1)];
// ! Tpsp2 := A[n:nat2, psp(n, last(ps(n))) = 1];

// begin("seq");
dcl[[],SEQ];
!! Axempseq := l([]) = 0;
!! Axempseqt := [] in seq(t);

!! Lconct3_ptd := u0 in seq(A) & v0=[] -> u0^v0 in seq(A);         // var u0,v0, SEQ;
!! Lconct2_ptd := x in seq1(A) & y in seq(A) -> x^y in seq1(A);    // _ptd : precizing type definition;
!! Lconct1_ptd := x in seq(A) & y in seq1(A) -> x^y in seq1(A);                                                             
!! Lconct_ptd := x in seq(A) & y in seq(A) -> x^y in seq(A);       // for more precise type computation; // must be just before the dcl;
dcl[^,SEQ,SEQ,SEQ];  // !! LPreft := u1 in seq1(A) -> u1- in seq(A); // for more precise type computation; // must be just before the dcl;
// dcl[^,seq(t),seq(t),seq(t)];                                // did not work; 
!! Lseq7 := A[x,y:seq(t), x^y in seq(t)];                      // was above dcl[^, ...], did not work, used Lconct_ptd, which was not handled yet;
!! LseqE := A[z: seq(A), l(z) ~= 0 -> E[z1:seq(A),c:A, z = z1^[c] ]];
!! Lseq1E := z in seq1(A) -> E[z1:seq(A),c:A, z = z1^[c]];

// ! SeqInd2 := A[z1,z2:seq(A), Q(z1,z2)] == Q([],[]) & A[z1,z2:seq(A), x1,x2:A, Q(z1,z2) -> Q(z1^[x1],z2^[x2])];
// ! SeqIndd := A[d,Q] == A[d,Q([])] & A[d,x:t, A[d--z,Q(z)] -> Q[z := z^[x]] ]; ??? Not rigorous !!!
// ! SeqIndd1 := A[d,Q] == A[d,Q([])] & A[d,x:t, Q(z) -> Q(z^[x])]; ??? Not rigorous !!!
!! Tseqcomp := A[B:set, f: fn(A,B), z: seq(A), f o z in seq(B)];
!! Tseqcomp_0 := A[B:set, f: fn(A,B), f o [] = [] ];
!! Tseqcomp_1 := A[B:set, f: fn(A,B), x: A, f o [x] = [f(x)] ];
! Tseqcomp_2 := A[B:set, f: fn(A,B), x,x1: A, f o [x,x1] = [f(x), f(x1)] ];

// SEQ1 := SEQ && (AxSEQ1 := l(f) ~= 0);

SEQ1 :: [
!! LSEQ1_a := l(f) > 0; 
!! TSEQ1afn := afn(dom(f)) <: SEQ1;
!! LSEQ1_3 := f in REL; 
]; // SEQ1 :: [

!! TSEQ1_d := x in SEQ1 == x in SEQ & l(x) ~= 0;
!! TSEQ1c1 := [x] in SEQ1;
!! TSEQ1c2 := [x,y] in SEQ1;
!! LSEQ1_0 := 0 in dom([x]);
!! LSEQ1_1 := SEQ1 <: REL;
!! LSEQ1_2 := SEQ1 <: FN;             // move to fit !!!
!! TSEQ1S0 := [x](0) = x;
!! TSEQ1t := SEQ1 <: SEQ;
!! TSEQ1l := A[z:SEQ, z in SEQ1 == l(z) ~= 0];             // was l(z) > 0
!! TSEQ1dom := A[y,z: SEQ1, dom(y)=dom(z) == last(y)=last(z)];
!! TSEQ1F := A[n:nat, F[i:0..n, Q] in SEQ1];

var u1, SEQ1;
!! Tu1lastdom := last(u1) in dom(u1);

dcl[seq1,set,set];                                // change like dcl[Last,...] ???
!! Tseq1in1 := z in seq1(A) == z in seq(A) & l(z) ~= 0;           // was l(z) ~= 0 // a defining axiom;
!! Axseq1 := seq1(A) = {z; z in SEQ1, im(z) <: A};
!! Tseq1t := seq1(A) <: SEQ1;
!! Tseq1in := z in seq1(A) == z in SEQ1 & im(z) <: A;
!! Tseq1inA := z in seq1(A) == z in SEQ1 & A[k:dom(z), z(k) in A];
!! Tseq1comp := A[z:seq1(A),a:afn(dom(z)), z o a in seq1(A)];
!! Tseq1afn := A[z:seq1(A), a:afn(dom(z)), a in seq1(dom(z))];
!! Tseq1F := A[n:nat, Q in A -> F[k:0..n, Q] in seq1(A)];
!! Tseq1lnz := z in seq1(A) -> ~(l(z) = 0);

!! LLastt_ptd := u1 in seq1(A) -> Last(u1) in A;  // must be just before the dcl; for more precise type computation;
dcl[Last,SEQ1,any];                               // was dcl[Last, fn({a; a in SEQ1}, im(a))]; 5.28.22
!! AxLast := Last(u1) = u1(last(u1));             // was A[u1:SEQ1, Last(u1) = u1(last(u1))];
!! TSEQdom := A[y,z: SEQ, dom(y)=dom(z) == last(y)=last(z)];
!! LLast1 := Last(u0^[x]) = x;

!! LPreft_ptd := x in seq1(A) -> x- in seq(A);   // for more precise type computation; // must be just before the dcl; // was u1 in seq1(A) ->
dcl[-,SEQ1,SEQ];   postfix;
!! last(u1) in int;
!! LSEQ1_4 := 0..last(u1)-1 <: dom(u1);  
!! AxPref := (u1-) = F[i:0..last(u1)-1, u1(i)];   // (u1-): parenthesis ??? before relation symbols ???
!! LPref1 := (u0^[x])- = u0;   

SEQ1 :: [
!! TSEQ1_0 := 0 in dom(f);                               // line 4214, not 4215
!! LSEQ_5 := f in FN;
!! LSEQ_6 := f in SEQ1; ! f in SEQ;                   // line 4216, correct !!!
!! LSEQ_7 := dom(f) <: int;
!! LSEQ_8 := last(f)>=3 -> 1 in dom(f) & 2 in dom(f) & 3..last(f)-1 <: dom(f);
!! LSEQ_9 := last(f) in dom(f);                         // line 4219, not 4220;
!! TSEQ1_im0 := f(0) in im(f);
!! Tlast1 := dom(f) = 0 .. last(f);         // is Tl2 ! Axlast;
// !           last(f) in int;
!! Tlast2 := last(f) < l(f);
!! Tlastt := last(f) in nat;
!! Tlast0 := last(f) = 0 -> f = [f(0)];
!! Tlastl := l(f) = last(f)+1;
!! Tlast3 := A[i:dom(f),  last(f)-i in dom(f)]; 
!! Tlastim3 := last(f)>=3 -> im(f) = {f(0),f(1),f(2),f(last(f))} \/ R[i:3..last(f)-1,f(i)];
!! Tlastim3A := last(f)>=3 -> All(z, z in im(f) == z=f(0) or z=f(1) or z=f(2) or z=f(last(f)) or z in R[i:3..last(f)-1,f(i)]);

// Last(f) := f(last(f));                     // f(last(f))
!! TLastim := Last(f) in im(f);
!! TLastim1 := A[x:im(f), x ~= Last(f) -> x in im(f-)];
!! TLastimconc := Last(f) in im(u0^f);                            // var u0,v0, SEQ;
!! TLastimconc1 := Last(f) in im(u0^v0^f);  
!! TLastimconc2 := Last(f) in im(u0^f^v0);                       // var u0,v0, SEQ;
!! L1 := Last(f) in im([a]^f);
!! LSEQ_10 := A[a:afn(dom(f)), f o a in SEQ1];
!! TLastcomp := A[a:afn(dom(f)), a(last(f)) = last(f) -> Last(f o a) = Last(f)];
// ! TLasttransp := A[k:dom(f), f o transp(dom(f),k,last(f)) = pref(f,k-1)^[Last(f)]^segm(f,k+1,last(f)-1)^[f(k)]];
// ! TLasttransp1 := A[a:afn(dom(f)), Last(a o transp(dom(a), inv(a)(last(a)), last(a))) = last(a)]; // move to transp.v !!!
]; // SEQ1 :: [

// dcl[Last, SEQ1, any];   double: was no warning !!! check if double dcls in same scope then check types !!!

!! TLastS := Last([x]) = x;
!! TLast_2 := Last([x,y]) = y;
SEQ :: ! f in SEQ;
SEQ2 := SEQ && (AxSEQ2 := l(f) > 1);                                // ??? PREVT SKIPS IT !!!

!! TSEQ2t := SEQ2 <: SEQ1;
!! TSEQ2t1 := SEQ2 <: SEQ;
!! TSEQ2l := A[z:SEQ, z in SEQ2 == l(z) > 1];

dcl[last1,SEQ2,nat];
dcl[Last1,SEQ2,any];

SEQ2 :: [
!! L0 := f in FN; ! f in SEQ;
!! Axthis := f in SEQ2;
!! Axlast1l := last1(f) = l(f)-2;
!! TSEQ2_1 := l(f) in dom(f);
// !! Tl3 := l(f) > 1;                       // is Tldom3 ! Axdom1; // line 4260, not 4261; same as AxSEQ2;
!! L1 := last(f)-1 in dom(f);
!! AxLast1 := Last1(f) = f(last(f)-1);
]; // SEQ2 :: [


// conc,^(y,z: SEQ) := F[i: 0.: l(y) + l(z) - 1, if(i in dom(y), y(i), z(i-l(y)) ) ];
// dyz:= {y,z; y in SEQ, z in SEQ; }
// !! Tconct := A[dyz, y^z in SEQ];
// !! Tconcdom := A[dyz, dom(y^z) = 0 .. l(y) + l(z) - 1];
// !! Lseq0a := dom(u0) <: int;             // same as Lseq0 above;
!! Lseq01 := seq(t) <: SEQ;
!! Tseq1t0 := seq1(A) <: SEQ;
!! Tseq1t1 := seq1(t) <: seq(t);
// !! Tseq1lnz := z in seq1(A) -> ~(l(z) = 0); 
!! Tconc1 := A[y,z: seq(t), y^z in seq(t)];
!! Lseqconc :=  y in seq(t) & z in seq(t) -> y^z in seq(t); 
!! Tconc2 :=  A[p:seq1(t), q:seq(t), p^q in seq1(t)];

dyz :: [  var i, dom(y^z);                            // dyz := {y,z; y in SEQ; z in SEQ; };
!! L0 := dom(y^z) <: int;
!! L01 := i in dom(y^z);
!! Tconcl := l(y^z) = l(y) + l(z);
// ! L01 := A[i: dom(y^z),  L01a := ~(i in dom(y)) -> i - l(y) in dom(z)];
!! L01a := ~(i in dom(y)) -> i - l(y) in dom(z);
!! Tconc := (y^z)(i) =  if(i in dom(y), y(i):any, z(i-l(y)):any );   "nosimr";
// ! Tconc := A[i: dom(y^z), (y^z)(i) =  if(i in dom(y), y(i):any, z(i-l(y)):any )];
// ! Tconclast := A[y,z: SEQ, last(y^z) = l(y) + l(z) - 1];
!! L02 := dom(y) <: dom(y^z);
! Tconc3 := A[i: dom(y), (y^z)(i) = y(i)];
!! LconcimIn := im(z) <: im(y^z);
]; // dyz :: [ 
dzz1 := {z,z1; z in SEQ1, z1 in SEQ; };
dzz1 :: [
 !! L03 := 0 in dom(z^z1);
 !! L04 := 0 in dom(z);
 !! Tconc1a := (z^z1)(0) = z(0);
]; // dzz1 :: [
dyz1 := {y,z; y in SEQ1, z in SEQ1; };
dyz1 :: [ 
!! L02 := last(y)+1 .. last(y)+last(z)+1 <: int;
!! L0 := last(y)+1 .. last(y)+last(z)+1 <: dom(y^z);
!! L01 := j in last(y)+1 .. last(y)+last(z)+1 -> j-last(y)-1 in dom(z);
!! L03 := z^y in SEQ1;
!! L04 := last(z)+1 in dom(z^y);
!! L05 := 0 in dom(y);	 

! Tconc4 := A[i: last(y)+1 .. last(y)+last(z)+1, (y^z)(i) = z(i-last(y)-1)];
// !              last(z^y) in int;
!! Tconclast := last(z) < last(z^y);
!! Tconclast0 := (z^y)(last(z)+1) = y(0);
]; // dyz1 :: [

!! Lconcl1 := A[y:SEQ, b:any, l(y^[b]) = l(y) + 1];
!! Lconcim := A[y,z: SEQ, im(y^z) = im(y) \/ im(z)];   // move to dyz;
!! Lconcim1 := A[y: SEQ, a:any, im(y^[a]) = im(y)\/{a}];
!! Lconcim2 := A[y,z:SEQ, i:dom(y), j:dom(z), {y(i),z(j)} <: im(y^z)];
!! Lconcim3 := A[z:SEQ, x in im([x]^z)];
! Lconcim3a := A[z:SEQ, x in im([x]^z^u0)];   by Lconcass; is Lconcim3;   // !! Lconcass := A[z,z1,z2: SEQ, (z^z1)^z2 = z^(z1^z2)];  
!! Lconcim4 := A[z:SEQ, x in im([a]^z) == x=a or x in im(z)];
!! Lconcim5 := A[y,z:SEQ, x in im([a]^y^z) == x=a or x in im(y) or x in im(z)];
!! Lconcim6 := A[A:set, a:A, y,z:SEQ1, im(y)<:A & im(z)<:A -> (x in A ==  x=a or x in im(y)&x~=Last(y) or x=Last(y) or 
                              x in im(z)&x~=Last(z) or x=Last(z) or x in A & x~=a & x nin im(y) & x nin im(z))];
!! Lconcempr := A[z:SEQ, []^z = z];
!! Lconcempl := A[z:SEQ, z^[] = z];
! Lconcempemp := [] ^ [] = [];
/*
dtQz1z2 := {t,Q,z1,z2; t in set, Q in fn(t#t, bool), z1 in seq1(t), z2 in seq1(t) };
dtQz1z2 :: [
!! L0 := seq1(t) <: SEQ1; 
!! L0a := seq1(t) <: SEQ; 
!! L00 := z1^z2 in SEQ1;
!! L01 := 1..last(z1^z2) <: dom(z1^z2);
!! L02 := j in 1..last(z1^z2) -> j in int;
!! L03 := j in 1..last(z1^z2) -> j-1 in dom(z1^z2);
!! L04 := j in 1..last(z1) -> j-1 in dom(z1);
!! L05 := j in 1..last(z2) -> j-1 in dom(z2);
!! L06 := j in 1..last(z1^z2) -> j-1 in dom(z1^z2);
!! L07 := 1..last(z1) <: dom(z1); ! L07a := 1..last(z1) <: int; // move to vith: k..m <: int; !!!
!! L08 := 1..last(z2) <: dom(z2); ! L08a := 1..last(z2) <: int;
!! L09 := 1..last(z1^z2) <: dom(z1^z2);
!! L10 := 1..last(z1^z2) <: int;
!! L11 := j in 1..last(z1^z2) -> (z1^z2)(j-1) in t;
!! L12 := j in 1..last(z1^z2) -> (z1^z2)(j) in t;
!! L13 := last(z1) in dom(z1); 
!! L14 := last(z2) in dom(z2); 
!! L15 := 0 in dom(z2);
!! Tconc5 :=  A[i:1..last(z1^z2), Q((z1^z2)(i-1), (z1^z2)(i))] == 
               A[i:1..last(z1), Q(z1(i-1),z1(i))] & Q(z1(last(z1)), z2(0)) & A[i:1..last(z2), Q(z2(i-1),z2(i))]; 
]; // dtQz1z2 :: [
*/
!! Lconc6 := u0^[x] in SEQ1;
!! Tconc6 := A[z:SEQ, x: any, Last(z^[x]) = x];
!! Lconc7 := A[z:SEQ, x:im(z), y:SEQ, x in im(z^y)];
!! Lconc8 := A[y:SEQ1, z:SEQ, Last(y) in im(y^z)];
!! Lseq1ltlc := A[z:SEQ, z1:SEQ1, l(z) < l(z^z1)];    // ltlc: lt l conc
!! Lconcemp := A[z:SEQ, z^[] = z]; // see Tconcempl
SEQ :: !! Lconcemp1 := A[z:SEQ, z=[] -> f^z = f];
!! Lconcemp2 := A[u,y,z:SEQ, y=[] ->u^y^z = u^z];
!! Lconcass := A[z,z1,z2: SEQ, (z^z1)^z2 = z^(z1^z2)];

dz1z2f := {z1,z2,f; z1 in seq(A), z2 in seq(A), f in  fn(A,B) };
dz1z2f :: [
!! L0 := f o z1 in SEQ; 
!! L00 := f o z2 in SEQ; 
]; // dz1z2f :: [
! Tconccomp := A[dz1z2f, f o (z1 ^ z2) = (f o z1) ^ (f o z2)];

// SEQkm := {z:SEQ, k: -1..last(z), m:k..last(z)};
dcl[pref,SEQ,int,SEQ];   //  natm := ige(-1); var n_natm, natm;     // var u0,v0, SEQ;
!! Lpref := n_natm < l(u0) & i in 0..n_natm -> i in dom(u0);
!! Axpref := n_natm < l(u0) -> pref(u0,n_natm) = F[i:0..n_natm, u0(i)];

dcl[-,SEQ1,SEQ];   // tail
// ! Ltail := 0..last(u1)-1 <: dom(u1);
// !! Axtail := -u1 = F[i:0..last(u1)-1, u1(i+1)];

dcl[<|,SEQ,SEQ,bool];
dyz :: [
!! L03 := 0..last(y) <: dom(y);
!! L04 := last(y) <= last(z) & i_int in 0..last(y) -> i_int in dom(z);      // was i, did not work;
!! Axispref := y <| z ==  last(y) <= last(z) & A[i:0..last(y), y(i) = z(i)];
]; // dyz :: [

dpref := {z,k; Ax1 := z in SEQ; Ax2 := k in natm; Ax3 := k < l(z) };
dpref :: [
!! Tpreft := pref(z,k) in SEQ;
!! Tprefdom := dom(pref(z,k)) = 0..k;
!! Tpreflast := pref(z, last(z)) = z;
!! Tprefl := pref(z, l(z)-1) = z;
!! L0 := l(z) > 0 -> 0 in dom(z) & z in SEQ1;
!! L01 := dom(z) <: int; 
!! Tpref0 := l(z) > 0 -> pref(z,0) = [z(0)];
!! Tpref01 := pref(z, -1) = [];  // empseq
!! Tpref01im := im(pref(z, -1)) = {};  
!! Tpref1 := k < m -> im(pref(z,k)) <: im(pref(z,m));
!! Tpref2 := im(pref(z,k)) = {} == k = -1;
!! Tpref3 := l(z) > 0 -> A[i:dom(z), im(pref(z,i)) = im(pref(z,i-1)) \/ {z(i)}];	
!! Tprefim := im(pref(z,k)) <: im(z);
!! Tpref4 := l(z) > 0 -> A[i:dom(z), im(pref(z,i)) =  {z(0)} \/ im(pref(-z,i-1))]; // ! TSEQ1l := A[z:SEQ, z in SEQ1 == l(z) > 0];
!! Tpref5 := z in seq1(t) -> A[i:dom(z), pref(z,i) in seq1(t)];
!! L02 := dom(z) <: natm;
// ! L03 := i in dom(z) & k in dom(z) & k <= i -> k in dom(pref(z,i));
dik := {i,k; i in dom(z); k in dom(z); k <= i; };
dik :: !! L03 := k in dom(pref(z,i));
!! Tpref6 := A[dik, pref(z,i)(k) = z(k)];
didom := {i; i in dom(z); };
didom :: !! L04 := i in dom(pref(z,i)); 
didom :: !! L05 := 0 in dom(pref(z,i));
// didom :: !! L06 := 0 in dom(z);                             // line 4393, 4394;
!! Tpref6a := A[didom, pref(z,i)(i) = z(i)]; 
!! Tpref6b := A[didom, pref(z,i)(0) = z(0)];
!! Tpref7 := A[x:SEQ, k < l(x) -> pref(x^z, k) = pref(x,k)];
!! L07 := k >= 0 -> k in dom(z);
!! Tpref8 := k >= 0 -> z(k) in im(pref(z,k));               // was Tpref12
!! Tpref9 := k <= m -> pref(z,k) <| pref(z,m); 
]; // dpref :: [
// SEQkm := {z:SEQ, k: -1..last(z), m:k..last(z)};
// ?? Tpref10 := E[x:SEQ,pref(z,k+m) = pref(z,k) || x];  // & l(x) = m
// segm := F[i:0..m-k, z(i+k)];

// dcl[-,SEQ1,SEQ];   postfix;
SEQ1 :: [
!! L0 := f in SEQ1; ! f in SEQ; ! afn(dom(f)) <: SEQ1; ! afn(dom(f)) <: SEQ; // for Tinitafn0;
!! L01 := dom(f-) <: dom(f);
!! L02 := dom(f-) <: int;
!! Tinitpref := f- = pref(f, last(f)-1);
!! Tinitt := f- in SEQ;
!! Tinit0 := A[i:dom(f-), (f-)(i) = f(i)];
!! Tinit1 := last(f-) = last(f) - 1;
!! Tinit1a := last(f-) < last(f);
!! Tinint1 := l(f-) = l(f)-1;
!! Tinitl := l(f-) < l(f);
!! Tinit2 := dom(f-) = dom(f) -- {last(f)};
!! Tinit2a := dom(f-) <: dom(f);
!! Tinitdom := dom(f-) = 0..last(f)-1;
!! Tinit3 := A[i:dom(f-), i <= last(f)-1];
!! Tinit4 := A[i:dom(f), i nin dom(f-) -> i = last(f)];
!! Tinit5 := im(f-) <: im(f);
!! TinitA := A[i:dom(f), Q(i)] == A[i:dom(f-), Q(i)] & Q(last(f));
!! Tinit6 := im(f) = im(f-) \/ {Last(f)};
!! Tinitlast := f = f- ^ [Last(f)];
da := {a; a in afn(dom(f)) };
da :: [
!! L0 := a in SEQ1;
!! L01 := last(f) in dom(a);
!! L02 := f o a in SEQ1;
]; // da :: [
! Tinitafn0 := A[da, a(last(f)) = last(f) -> a- in afn(dom(f-))];
! Tinitafn1 := A[da, a(last(f)) = last(f) -> (f o a)- = f- o a-];
]; // SEQ1 :: [
!! LinitS := [x] in SEQ1;
!! TinitS := [x]- = [];
// ! Tinit_2 := 

SEQ2 :: [   ! f in SEQ1;                 // Need a new name for the theory SEQ2, like fingroup ??? Maybe not, if using L00.g, g in SEQ2; ???
!! L00 := f- in SEQ1;
!! L01 := f in SEQ2;
!! L02 := f in SEQ;	 
!! Tinit7 := last(f-) = last1(f)-1;
!! Tinit8 := l((f-)-) = l(f) - 2;                            //  byeq Tinit1((z-)-), Tinit1(z-);
!! Tinit9 := f = (f-)- ^ [Last1(f), Last(f)];
]; // SEQ2 :: [

AsetzBg := {A,B,z,g; A in set, B in set, z in seq(A), g in fn(A,B), A ~= {}};
AsetzBg :: [
// ! L0 := g in REL;
// ! L01 := z in REL;
!! L0 := g o z in SEQ;
!! TzBg1 := g o z in seq(B);
!! TzBgdom := dom(g o z) = dom(z);                            // is Tcompdom; with TSEQdom;
!! TzBgl := l(g o z) = l(z);
!! TzBglast := l(z) > 0 -> last(g o z) = last(z);             // is TSEQ1dom;
!! L01 := l(z) > 0 -> z in SEQ1; 
!! L02 := l(z) > 0 -> g o z in SEQ1;
!! L03 := l(z) > 0 -> Last(z) in A;                           // was Last(z) in dom(g);
!! TzBgLast := l(z) > 0 -> Last(g o z) = g(Last(z));          ///
!! TzBginit1 := l(z) > 0 -> dom((g o z)-) = 0..l(z)-1;        ///
!! TzBginit2 := l(z) > 0 -> dom(g o (z-)) = 0..l(z)-1;        ///
!! TZbGinit3 := l(z) > 0 -> dom((g o z)-) = dom(g o (z-));    // is TzBginit1 & TzBginit2;
!! TzBginit := l(z) > 0 -> (g o z)- = g o (z-);               ///
]; // AsetzBg :: [

!! LinitF := n0 in nat -> F[i:0..n0, Q(i)] in SEQ1;
!! TinitF := A[n:nat, F[i:0..n, Q(i)]- = F[i:0..n-1, Q(i)]]; // ???? A[n:???, Q: ???]

!! Tprf0 := A[x: SEQ, x <| x];
!! Tprf2 := A[x, y,z: SEQ,x <| y & y <| y & y <| z -> x <| z];
dyz :: [
!! Tprf1 := y <| z & z <| y -> y = z;
!! L05 := dom(y) <: dom(z);
!! Tprf3 := y <| z == l(y) <= l(z) & A[i:dom(y), y(i) = z(i)];
!! Tprf4 := y <| z == l(y) <= l(z) & pref(z,l(y)) = y; 
!! Tpref10 := y <| z == y = pref(z, l(y)-1);   // was Tpref10,Tpref8
]; // dyz :: [

// !! Axpref := A[n: -1..last(u0), pref(u0,n) = F[i:0..n, u0(i)]];

// suf(z.k) := F[i:0..last(z)-k, z(i+k)];
dcl[suf,SEQ,nat,SEQ];               // if(u(u0) = []) then suf(u0,k) is not defined;
SEQ :: [
// ! L03 := dom(f) <: nat; ! dom(f) <: int;   // line 4485, correct !!!   same as L10 (line 4612)
dk := {k; k in dom(f)};
dk :: [ 
!! L0 := k in nat; ! k in int;
!! L00 := 0..last(f)-k <: int;
!! L01 := i in 0..last(f)-k -> i+k in dom(f);  // make warning, was i in last(f-k);
!! L02 := f in SEQ;
!! Axsuf :=  suf(f,k) = F[i:0..last(f)-k, f(i+k)];  
!! Tsuft := suf(f,k)  in SEQ;
!! Tsufdom := dom(suf(f,k)) = 0..last(f)-k;
!! Timprefsuf := im(f) = im(pref(f,k-1))\/im(suf(f,k));
!! Tlprefsuf := l(pref(f,k-1)) + l(suf(f,k)) = l(f);
!! Tsufim := im(suf(f,k)) <: im(f);
!! Tsufpref := f = pref(f,k-1) ^ suf(f,k);
!! L03 := 0 in dom(suf(f,k));
!! Tsuf6b := suf(f,k)(0) = f(k);                     // line 4500, main.his: 4501  s= !! Tsuf6b := suf(f,k)(0) = f(k);
]; // dk :: [  

!! TimprefsufU := A[k1,k2: dom(f), im(pref(f,k1)) \/ im(suf(f,k2)) <: im(f)];

]; // SEQ :: [

SEQ1 :: ! Tsuf0 := suf(f, 0) = f;
SEQ2 :: ! Tsuf1 := suf(f, 1) = -f;

SEQ :: ! f in FN;      // should infer automatically !!!   // begin("module SEQinj");
SEQinj := SEQ && (Axinj := injective(f));
!! TISEQt := SEQinj <: SEQ;                                                 // is Tscinl;
SEQ1 :: ! f in FN; 
SEQinj1 := SEQ1 && (Axinj1 := injective(f));
!! TSEQinj1t := SEQinj1 <: SEQ1;
!! TSEQinj1t1 := SEQinj1 <: SEQinj;
!! LSEQinj1a := A[z:SEQ1, [a]^z in SEQinj1 -> z in SEQinj1];
!! LSEQinj1b := [x] in SEQinj1;
SEQinj1 :: [
x_imf := {x; x in im(f)};
// !! L0 := z in seq1(A);
// !! L1 := z in SEQ1;
! L2 := 0 in dom(f);                               is TSEQ1_0;   // SEQ1 :: !! TSEQ1_0 := 0 in dom(f);  // ??? cannot use istr2 ???  
!! L3 := Last(f) in im(f);
// !! L4 := im(z-) <: im(z);                              // move to root !
// !! L5 := dom(z) <: int;                                // move to root ! 
!! Lpl := A[x_imf, E1[p: dom(f), f(p)=x] ];
!! Tpl := Exist1x(pl, (Axpl1 := pl in fn(im(f),dom(f))) & (Axpl2 := A[x:im(f), f(pl(x)) = x])); is TExist1a(Lpl);
!! Lpl1 := A[x_imf, Lpl1a := pl(x) in 0..last(f)];     // last(z): istrin(z,SEQ) used L1 in for2;
!! Lpl2 := A[x_imf, Lpl2a := pl(x) in int];            // for pl(x)+1 in nextf;
!! Lpl3 := A[x_imf, Lpl3a := x ~= Last(f) -> pl(x)+1 in dom(f)];

nextf := F[x_imf, if(x=Last(f), f(0), f(pl(x)+1))];
!! Lnextf_type := nextf in fn(im(f),im(f));            // actually, bfn or afn;
!! Lnextf1 := nextf(Last(f)) = f(0);
!! Lnextf2 := A[x_imf, x ~= Last(f) -> nextf(x) = f(pl(x)+1)];      // A[x:im(z-), nextz(x) = z(pl(x)+1)];
!! Lnextf3 := A[x_imf, nextf(x) in im(f)]; 
// !! Lnextf4 := A[y,z:SEQ1, y^z in SEQinj1 -> nextf.(y^z)(Last(y)) = z(0)]; // use !! Lconc8 := A[y:SEQ1, z:SEQ, Last(y) in im(y^z)];
// !! Lnextf5 := A[x:any, z:SEQ1, [x]^z in SEQinj1 -> nextf.([x]^z)(x) = z(0)];    // Last([x]) = x;
]; // SEQinj1 :: [

!! Lnextf4 := A[y,z:SEQ1, y^z in SEQinj1 -> nextf.(y^z)(Last(y)) = z(0)]; // use !! Lconc8 := A[y:SEQ1, z:SEQ, Last(y) in im(y^z)];
!! Lnextf5 := A[x:any, z:SEQ1, [x]^z in SEQinj1 -> nextf.([x]^z)(x) = z(0)]; // "hintfit"; Lconcim3;  // use !! Lconcim3 := A[z:SEQ, x in im([x]^z)];
// !! Lnextf6 := A[z:SEQ1, [a]^z in SEQinj1 -> z in SEQinj1];
SEQ1 :: !! Lnextf8a := [a]^f in SEQinj1 -> nextf.([a]^f)(Last(f)) = a;
!! Lnextf9 := F[z:seqinj1(A), F[x:A, if(x in im(z), nextf.z(x):A, x)] ] in fn(seqinj1(A), afn(A));
!! Lnextf10 := nextf.[x](x) = x;
!! Lnextf11 := a in im([x]) -> nextf.[x](a) = a;
 
dyz2 := dyz && (Ax1 := z in SEQ1) & (Ax2 := y^z in SEQinj1);
dyz2 :: [
!! L1 := z in SEQinj1;
!! Lnextf6 := A[x:im(z), x ~= Last(z) -> nextf.(y^z)(x) = nextf.z(x)];
!! Lnextf7 := Last(z) in im(y^z);                                 // dyz2 := dyz && (Ax1 := z in SEQ1) & (Ax2 := y^z in SEQinj1);  
!! Lnextf8 := y in SEQ1 -> nextf.(y^z)(Last(z)) = (y:SEQ1)(0);    // in SEQ1
!! L2 := x in im([x]^z^y);
!! L3 := 0 in dom(z); 
!! Lnextf5a := [x]^z^y in SEQinj1 -> nextf.([x]^z^y)(x) = z(0); 
]; // dyz2 :: [

uyz := {u,y,z; u in SEQ, y in SEQ, z in SEQ; Ax1 := u^y^z in SEQinj1; }; 
uyz :: [ 
!! L0 := y ~= [] -> 0 in dom(y); 
!! L1 := im(z) <: im(u^y^z); 
!! L2 := y in SEQ1 -> y in SEQinj1;
!! L3 := z in SEQ1 -> z in SEQinj1;
!! L4 := im(y) <: im(u^y^z); 
!! L5 := y in SEQ1 -> Last(y) in im(u^y^z);
!! L6 := z in SEQ1 -> Last(z) in im(u^y^z);
!! L7 := u in SEQ1 -> 0 in dom(u);
!! L8 := z in SEQ1 -> 0 in dom(z);
!! L9 := x in im(z) -> ~(x in im(u^y));
!! L10 := x in im(y) -> ~(x in im(u^z));
!! L11 :=  y ~= [] -> ~(y(0) in im(u^z)); 
!! Lnextf6a :=  A[x: im(z),  z in SEQ1 & x ~= Last(z) -> nextf.(u^y^z)(x) = nextf.z(x)]; 
!! Lnextf6b :=  A[x: im(y),  y in SEQ1 & x ~= Last(y) -> nextf.(u^y^z)(x) = nextf.y(x)];
!! Lnextf4a := u in SEQ1 & z in SEQ1 & u^y^z in SEQinj1 -> nextf.(u^y^z)(Last(z)) = u(0);
!! Lnextf4b := y in SEQ1 & z in SEQ1 & u^y^z in SEQinj1 -> nextf.(u^y^z)(Last(y)) = z(0);
]; // uyz :: [

SEQinj2 := SEQinj1 && l(f) >= 2;
!! TSEQinj2t := SEQinj2 <: SEQ2;

dcl[seqinj,set,SEQinj];
dcl[seqinj1,set,SEQinj1];
dcl[seqinj2,set,SEQinj2];

!! Axseqinj := z in seqinj(A) == z in SEQinj & im(z) <: A;
!! Axseqinj1 := z in seqinj1(A) == z in SEQinj1 & im(z) <: A;
!! Axseqinj2 := z in seqinj2(A) == z in SEQinj2 & im(z) <: A;
!! LFseqinj := F[x: 0..k, G(x)] in seqinj(A) == A[x: 0..k, G(x) in A] & A[x,y: 0..k, x~=y -> G(x) ~= G(y)];
!! LseqinjSEQ := seqinj(A) <: SEQ;
!! Lseqinj1SEQ1 := seqinj1(A) <: SEQ1; // !! TExist1a := A[x:A, E1[y:B, P(x,y)]] -> Exist1(f, f in fn(A,B) & A[x:A, P(x,f(x))]);
!! Lseqinj1In := seqinj1(A) <: SEQinj1;
!! Lseqinj1 := z in seqinj(A) -> im(z) in finset;
!! Lseqinj2 := z in seqinj(A) -> #(im(z)) = l(z);
!! Lseqinj3 := seqinj(A) <: seq(A);
!! Lseqinj3a := seqinj1(A) <: seq(A);
!! Lseqinj4 := z in seqinj(A) -> (z ~= [] -> z in SEQinj1);
!! Lseqinj5 := z in seqinj(A) & a nin im(z) -> [a]^z in seqinj1(A);
!! Lseqinj6 := z in seqinj(A) & a nin im(z) -> [a]^z in SEQinj1;
!! Lseqinj7 := a in A & y in seqinj(A) & z in seqinj(A) & a nin im(y) & a nin im(z) & im(y) NI im (z) -> [a]^y^z in seqinj1(A);
!! Lseqinj8 := A[a:A, [a] in seqinj1(A)];
// seqinj := SEQinj && im(f) <: A;  // Aset :: begin
// seqinj1 := seqinj && l(f) > 0;
// seqinj2 := seqinj && l(f) > 1;

dcl[seqbij, set, SEQinj];                                  // bijective sequence;
!! Axseqbij := z in seqbij(A) == z in SEQinj & im(z) = A;
// !! Lseqbij1 := z in seqbij(A) & A ~= {] -> z in seq1(A);
!! Lseqbij1 := z in seqbij(A) & A ~= {} -> E[z1:seq(A),x:A, z = z1^[x] & z1 in seqbij(A--{x})] ;      // ????? z = z1^[x]^z2] ?????? no error ???
!! Lseqbij2 := z in seqbij(A) & x in A -> E[z1,z2: seq(A), z = z1^[x]^z2 & z1^z2 in seqbij(A--{x})];  // z = z1^[x]^z2] & z1^z2 in seqbij(S--{x})];
!! Lseqbij3 := A[A:finset, z:seqbij(A), #A = 0 -> z = [] ];
!! Lseqbij4 := A <: B -> seqbij(A) <: seq(B);
!! Lseqbij5 := seqbij(A) ~= {};     

// dcl[-,SEQ1,SEQ];   // tail             // also in 0_bool.v
// ! Ltail := 0..last(u1)-1 <: dom(u1);
// !! Axtail := -u1 = F[i:0..last(u1)-1, u1(i+1)];
SEQ1 :: [
// hd := f(0);
// -, tail := F[i:0.: l(f)-1, f(i+1)];
!! Ltail := f in SEQ1;                      ! f in SEQ;
!! Ltail1 := -f in SEQ;
!! L03 := i in 0..l(f)-1 -> i+1 in dom(f);
!! Axtail := -f = F[i:0.. l(f)-1, f(i+1)];
!! Ttailt := -f in SEQ;
!! Ttailt1 := f in seq(t) -> -f in seq(t);
!! L04 := dom(-f) <: int;
!! L05 := i in dom(-f) -> i+1 in dom(f);
!! TtailA := A[i:dom(-f), (-f)(i) = f(i+1)];
!! Ttaildom := dom(-f) = 0..last(f)-1;
!! Ttaill := l(-f) = l(f)-1;           
//   !!    0 in dom(f);
!! Ttailhd := f = [f(0)] ^ (-f);
!! Ttailim := im(-f) <: im(f); 
ySEQ := {y; y in SEQ};
ySEQ :: [
 !! L06_type := (f^y) in SEQ1; // ! L07 := f in SEQ1;  // line 4555; L07: same as LSEQ_6
 !! Ttailconc := -(f ^ y) = (-f) ^ y;
]; 
!! L07 := [x] in SEQ1;  
!! TtailS := -[x] = [];
!! L08 := dom(f) <: int;
!! TpreftailF := A[k:dom(-f), pref(-f,k) = F[i:dom(-f), f(i+1)]];     // used L04 := dom(-f) <: int;
!! Tpreftailim := A[k:dom(-f), im(pref(-f,k)) = R[i:dom(-f), f(i+1)]];
!! Tpreftailim1 := A[k:dom(f), im(pref(f,k)) = {f(0)} \/ im(pref(-f,k-1))];
]; // SEQ1 :: [

SEQ2 :: ! TLast1tail := Last1(f) = Last(f-);
// !! Lseqinj1SEQ1 := seqinj1(S) <: SEQ1;
!! Lseqinj1a := z in seqinj1(A) & f in bfn(A, B) -> f o z in SEQ1;
!! Ttail1a := z in seqinj1(A) & f in bfn(A, B) -> f o (-z) = -(f o z);

dcl[rev,SEQ,SEQ];                            // reverse sequence
SEQ :: [ 
// rev := F[i: dom(f), f(last(f)-i))];
i_dom_f := {i; i in dom(f)};
!! L04 := A[i_dom_f, last(f)-i in dom(f)];
!! L05 := dom(f) = dom(rev(f)); 
!! L06 := f in SEQ;            // why ??? see L00 in SEQ :: [  (0_bool.v)
!! Axrev := A[i_dom_f, rev(f)(i) = f(last(f)-i)];
!! Trev0 := rev([]) = [];                                 // empty sequence
!! TrevA := rev(f) = F[i_dom_f, f(last(f)-i)];
!! TrevA1 := A[i_dom_f, rev(f)(last(f)-i) = f(i)];
!! Trevt := rev(f) in SEQ;
!! Trev1 := rev(rev(f)) = f;
!! Trevdom := dom(rev(f)) = dom(f);
!! Trevim := im(rev(f)) = im(f);
!! Trevinj := injective(rev(f)) == injective(f);

]; // SEQ :: [

SEQ1 :: [
!! L09 := rev(f) in SEQ1;
!! L06 := 0 in dom(rev(f));
!! Trevlast := last(rev(f)) = last(f);
!! TrevLast := Last(rev(f)) = f(0);                      // ?? First(f) ??
!! TrevFirst := rev(f)(0) = Last(f);
]; // SEQ1 :: [

// Aset :: seq :: begin
// Trev2 := rev(f) in seq(A);                              // f in seq(A) -> rev(f) in seq(A);
// end; // Aset :: seq :: begin

dcl[addm,int,int,nat1,nat];   // addm(n,k,m) = res(n+k,m): addition modulo m: ??? N
dcl[neib,nat,nat,nat1,bool];
dcl[rot,SEQ1,int,SEQ1];       // rot(f,k): rotate f on k: k >0: right, k<0: left;
dcl[rtb,SEQ1,SEQ1,bool];      // rtb := E[k:int, z = rot(q)(k)];

 SEQ1 :: [
// rot(k:int) := F[i:dom(f), f(addm(k,i,l(f))];     // addm(n,k,m) = res(n+k,m): addition modulo m:
var y, SEQ1;
!! L10 := dom(f) <: nat;
!! L11 := f in SEQ1;
!! L12 := l(f) in nat1;
!! L13 := A[i_dom_f, addm(k,i,l(f)) in dom(f)];
!! Axrot := rot(f,k) = F[i_dom_f, f(addm(k,i,l(f)))];   // was A[k:int, // F[i:int, f(addm(k,i,l(f)))] ]: erroneos definition !!!
!! Trott := rot(f,k) in SEQ1;
!! Trott1 := f in seq1(t) -> rot(f,k) in seq1(t);
!! Trotdom := dom(rot(f,k)) = dom(f);
!! Trotim := im(rot(f,k)) = im(f);
!! L14 := dom(f) <: int;
!! TrotA := A[i_dom_f, rot(f,k)(i) = f(addm(k,i,l(f)))];
!! L15 := 0 in dom(y);
!! Trtb1 := A[a: im(f), E[q:SEQ1, rtb(f,q) & q(0) = a]];

]; // SEQ1 :: [

SEQ2 :: [
var y, SEQ2;
!! L03 := 0 in dom(rot(f,1));
!! L04 := 0 in dom(rot(f,-1));
!! L05 := 1 in dom(f);                                         // line 4631, not 4632;
!! Trot10 := rot(f,1)(0) = f(1);  ! last(f) in dom(f);         // rotate by 1 to left
!! Trot1m0 := rot(f,-1)(0) = f(last(f));                       // rotate by 1 to right
! L06 := 0 in dom(rot(f,k));
!! L07 := 1 in dom(rot(f,k));
!! L08 := 0 in dom(y);
!! L09 := 1 in dom(y);  ! dom(f) <: nat; ! l(f) in nat1; ! SEQ2 <: SEQ1;
!! Trotneib := A[i,j:dom(f), neib(i,j,l(f)) -> E[k:int, {f(i),f(j)} = {rot(f,k)(0),rot(f,k)(1)}]];  // use L06, L07;
!! Trtbneib := A[i,j:dom(f), neib(i,j,l(f)) -> E[q: SEQ2, rtb(f,q) & {f(i),f(j)} = {q(0),q(1)}]];
]; // SEQ2 :: [

dyz1 :: [

// rtb := E[k:int, z = rot(y,k)];
!! Trtbcom := rtb(y,z) == rtb(z,y);
!! Trbdom := rtb(y,z) -> dom(y) = dom(z);
!! Trbim := rtb(y,z) -> im(y) = im(z);
]; // dyz1 :: [

dcl[Constseq, set, any, SEQ1];
!! AxConstseq := Constseq(B, b) = {z; z in seq1(B), A[x: dom(z), z(x) = b] };
!! TConstseqincl := Constseq(B, b) <: seq1(B);
!! L04 := Constseq(B, b) <: FN; 
dConstseq := {z,x; Ax1 := z in Constseq(B, b); Ax2 := x in dom(z) };
dConstseq :: [
!! L0 := z in FN; 
!! TConstseqval :=  z(x) = b;
]; // dConstseq :: [
!! L05 := Constseq(B, b) <: SEQ1;
!! TConstseqLast := A[z : Constseq(B, b), Last(z) = b]; 

// constseq(z: any, n:nat) := F[i:0..n-1, z];   // constseq(z,n) = [z,z, ... ,z] (n times)
// !! Axconstseq := A[z:any, n:nat, constseq(z,n) := F[i:0..n-1, z]];

dcl[constseq,any,nat,SEQ];
!! Axconstseq := constseq(z,n0) = F[i:0..n0-1, z];
!! Tconstseq_0 := constseq(z,0) = [];
!! Tconstseq_1 := constseq(z,1) = [z];
!! Tconstseq_2 := constseq(z,2) = [z,z];
!! Tconstseql := l(constseq(z,n0)) = n0;
!! L06 := n0 + n00 in nat;
!! Tconstseq1 := constseq(z,n0) ^ constseq(z,n00) = constseq(z,n0+n00);


INFSEQ := FN && (Axdom := dom(f) = nat);              // Infinite sequences
dcl[tail,fn(INFSEQ#nat, INFSEQ)];
!! Axtail := A[f:INFSEQ,k:nat, tail(f,k) = F[i:nat, f(i+k)] ];

dcl[infseq,fn(set,INFSEQ)];
!! Axinfseq := A[f:infseq(X), im(f) <: X];
//                                         Periodic sequences
dcl[pseq, fn(nat1,INFSEQ)];  var p_nat1, nat1;                                 //  fn({f:INFSEQ, p:nat1}, 
!! Axpseq := f in pseq(p_nat1) == f in INFSEQ & A[i:nat, f(i) = f(i%p_nat1) ];   // p: period;
!! Lpseq0 := f in pseq(p_nat1) -> dom(f) = nat;    
!! L19 := 0..p_nat1-1 <: nat;                                             
!! Lpseq1 := A[f: pseq(p_nat1), im(f) = im(F[i:0..p_nat1-1, f(i)])];  //wlot:f:pseq(p_nat1): check thms(pseq(p_nat1): Axpseq: wrlot Rpart!!!
!! Lpseq2 := A[p:nat1, f: pseq(p), k:nat, im(f) = im(tail(f,k))];

FNpnat := {f,p; Ax1 := f in FN; Ax2 := dom(f) = nat; Ax3 := p in nat1; Ax4 := A[i_nat, f(i) = f(i%p)] }; // f is a periodical function with period p;
FNpnat :: [
!! LFNpnatim := im(F[k:0..p-1, f(k)]) = im(f);
!! LFNpnatim1 := A[k:nat, im(F[i_nat, f(i+k)]) = im(f)];
]; // FNpnat :: [

FNtypes := [FN,IFN,BFN,AFN,FFN,SEQ,SEQ1,SEQ2, SEQinj,SEQinj1,SEQinj2,INFSEQ];
fntypes := [fn,ifn,sfn,bfn,afn,ffn1,ffn,seq,seq1,seqinj,seqinj1,seqinj2,seqbij,Constseq,pseq,infseq,Fn];
disjoint := [int,REL,int,fntypes];   // ??? int,FNtypes;

]  // end module 0_root.v