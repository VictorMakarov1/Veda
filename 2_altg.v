module 2_altg;                  // Newveda_C4: 2_altg.v
use 0_root, 1_group; 
[                        
i_nat := {i; i in nat};

 AFN :: [                     // copied from 0_root to avoid an error with dom(f): dom(f) presents both in 0_root and in 2_altg;
!! LAFNds := A[x:dom(f), x in ds == f(x) ~= x];   
!! LAFNreds := f | ds.f in AFN;
!! LAFNdsdom := ds <: dom(f);
!! LAFNdsid := ds={} == f = id(dom(f)); 
!! LAFNdsIn := A[B:P[dom(f)], A[x:B, f(x) ~= x] == B <: ds];               // ???==
!! TAFNre := B <: dom(f) & f|B in AFN -> A[i:nat, b:B, ((f|B)^i)(b) = (f^i)(b)];
// !! TAFNRS := A[x:dom(f), f(x) = x -> R[i_nat, (f^i)(x)] = {x} ];
]; // AFN :: [

perm := AFN && (Axp := dom(f) in finset1);         // {f; f in afn(A) };    
! Tperm := g in perm == g in AFN & dom(g) in finset1;  byeq Axdconj;                // Axdconj := z in d&&P == z in d & Rep(d,P,z);
! LpermAFN := perm <: AFN;                         is LdconjIn;                     // !! LdconjIn := d&&P <: d; // !! TAFNREL := AFN <: REL;
! LpermREL := perm <: REL;                         is TInIn(LpermAFN & TAFNREL); // ! TInIn := X0 <: Y0 & Y0 <: Z0 -> X0 <: Z0; 
! LpermFN := perm <: FN;                           is TInIn(LpermAFN & TAFNFN);  // for type checking in typ;
! Lperm_type := perm in P[FN];                     by AxP; LpermFN;                 // !! AxP := Z in P[Y] == Z <: Y;
perm :: [
A := dom(f);
// x_A := {x; x in A};
! L0_type := A in finset1;                         is Axp;                     // Axp := dom(f) in finset1;
! L00 := f in afn(A);                              is L4;                      // AFN :: !! L4 := f in afn(dom(f));
! L07 := afn(A) <: AFN;                            is LafnAFN;                 // !! LafnAFN := afn(A) <: AFN;
! L05 := f in AFN;                                 is TinIn(L00 & L07);        // ! TinIn := x in X2 & X2 <: Y2 -> x in Y2;
! L2 := f in perm;                                 by Axdconj; L05 & Axp;      // Axdconj := z in d&&P == z in d & Rep(d,P,z);
! L6 := A[g:afn(A), dom(g) = A];                   is Tafndom;                 // !! Tafndom := A[f: afn(A), dom(f) = A]; 
// ! L01 := A[i_nat, L01_type := f^i in afn(A)];      is Lf;                      // AFN :: !! Lf :=A[i_nat, Lf_type := f^i in afn(dom(f))]; 
// ! L02 := A[i_nat, dom(f^i) = A];                   is L6@AFN(f^(i@i_nat));        // is Tafndom(f^(i@i_nat));        
! L06 := A in finset;                              is TinIn(Axp & Lfinset1In); // ! TinIn := x in X2 & X2 <: Y2 -> x in Y2;
! Lim := A = im(f);                                is AxAFN2;                  // AxAFN2 := dom(f) = im(f)
n := #A;
// ds := {x: A; f(x) ~= x};                        moved to root;
ab_A := {a,b; a in A, b in A};
trp := F[ab_A, Trp(A,a,b)];                         // tr(a,b) \/ id(A--{a,b}]; // F[x:A, if5(x=a,b,x=b,a,x)]];
            // Aab :: !! LTrpAab_type := Trp(A,a,b) in AFN;              //  was !! LTrpAFN := A[Aab, Trp(A,a,b) in AFN];
! L03 := A[ab_A, Ltrp_type := trp(a,b) in perm];
 Proof L03;
F0 := a in A;                                      assume;
Ltrp_type;                                         by Red("F");
G0 := Trp(A,a,b) in perm;                          by Axdconj; G1 & G2;        // Axdconj := z in d&&P == z in d & Rep(d,P,z);
G1 := Trp(A,a,b) in AFN;                           is LTrpAab_type@Aab;        // was is LTrpAFN; // !! LTrpAFN := A[Aab, Trp(A,a,b) in AFN];
G2 := dom(Trp(A,a,b)) in finset1;                  by LTrpdom; is Axp;         // !! LTrpdom := A[Aab, dom(Trp(A,a,b)) = A];
 end Proof L03;

! L04 := A[ab_A, L04_type := trp(a,b) o f in perm];                            // for checking trp(a,b) o f;   
 Proof L04;
F0 := a in A;                          assume;                                 // !! Tafnin1 := f in afn(A) == f in AFN & dom(f)=A; 
F01 := Trp(A,a,b) o f in afn(A);       is LTrpcomp; by Tafnin1; F02 & F03;     // !! LTrpcomp := A[Aab, dom(f)=A -> Trp(A,a,b) o f in afn(A)]; 
F02 := Trp(A,a,b) o f in AFN;
F03 := dom(Trp(A,a,b) o f) = A;
L04_type;                              by Red("F");
G0 := Trp(A,a,b) o f in perm;          by Axdconj; F02 & G2;                   // Axdconj := z in d&&P == z in d & Rep(d,P,z); 
G2 := dom(Trp(A,a,b) o f) in finset1;  by F03; is Axp;
 end Proof L04;

! Lds1 := ds <: A;                    is TabIn;                                // !! TabIn := {x:X; P(x)} <: X;  // ds := {x: A; f(x) ~= x};
! Lds2 := ds in finset;               // is TfinsetIn(L06 & Lds1);             // !! TfinsetIn := A in finset & B <: A -> B in finset;
Lds2 & Lds3;                          is TfinsetIn1(L06 & Lds1);               // !! TfinsetIn1 := A in finset & B <: A -> B in finset & #A <= #B;
! Lds3 := #ds <= #A;                  
]; // perm :: [

perma := perm && {a; Ax2 := a in A; };   // perma := {f,a; Ax1 := f in perm; Ax2 := a in A@perm; }; 
perma :: [                         // !! Axlboundedint := A[S:P[int], lboundedint(S) == S ~= {} & E[a:int, a <= S] ];

orbf := F[i_nat, (f^i)(a)];        // orbit function 
! LorbfFN := orbf in FN;            is TFFN;                      // !! TFFN    := F[d, g] in FN;
! Lorbfdom := dom(orbf)=nat;        is TFdom1;                    // !! TFdom1 := dom(F[x:A, G(x)]) = A; 
! L08 := A[i_nat, (f^i)(a) in A];   is L5;                        // !! L5 := A[i_nat, A[a: dom(f), (f^i)(a) in dom(f)]]; 
! Lorbfim := im(orbf) <: A;         by TimFA; L08;                // !! TimFA := im(F[d, f]) <: B == A[d, f in B];
! Lorbfim1 := im(orbf) in finset;   is TfinsetIn(L06 & Lorbfim);  // !! TfinsetIn := A in finset & B <: A -> B in finset;  
! Lorbfim2 := fin(im(orbf));        by -Axfinset; Lorbfim1;       // !! Axfinset := X in finset == fin(X);  // ! L06 := A in finset;
! LorbfEij := Ex[i,j: nat, (L09 := i ~= j) & (L010 := orbf(i)=orbf(j))]; is TFN5@FN(Lorbfdom & Lorbfim2); 
! Lorbf0 := orbf(0) = a;            by Red("F"); is TAFN0;

! Lorbf1 := A[i_nat, orbf(i) in A]; by Red("F"); is L08;
k := abs(i-j);                                                    // FN :: !! TFN5 := dom(f)=nat & fin(im(f)) -> E[a,b:nat, a ~= b & f(a)=f(b)];
! Lk1 := k in nat1;                 is Labs3;                     // !! Labs3 := A[i,j:int, i ~= j -> abs(i-j) in nat1];
// ! Lk2 := k ~= 0;                    is Labs2(L09);                // !! Labs2 := A[i,j:int, i ~= j -> abs(i-j) ~= 0];
L010; by Red("F"); 
! Lk3 := (f^i)(a) = (f^j)(a);
! Lk4 := (f^k)(a) = a;              is L13(Lk3);                  // !! L13 := A[i,j:int, (f^i)(vd) = (f^j)(vd) -> (f^abs(i-j))(vd) = vd];
// !! Lk := k in nat & (k ~= 0 & (f^k)(a) = a);
S := {k:nat1; (f^k)(a)=a };         // because im(orbf) <: A, A is finite, so E[i,j:nat, i~=j & orbf(i)=orbf(j);
! LSk := k in S;  by Axab; Lk1 & Lk4;
! LS0 := S ~= {};                   is Tinnemp(LSk);              // ! Tinnemp := x in X -> X ~= {};  
! LSnat1 := S <: nat1;              is TabIn;                     // !! TabIn := {x:X; Q(x)} <: X;
! LS1 := S in lbint;                is Tlbint2(LSnat1 & LS0);     // !! Tlbint2 := S <: nat1 & S ~= {} -> S in lbint;
M := min(S);                        // dcl[min,lbint,int];

! LM0 := M in S;                    is Tmin1; by Axab; LM7 & LM3; // !! Tmin1 :=  A[S:lbint, min(S) in S];
! LM1 := M in nat;
// ! LM2 := M ~= 0;
! LM7 := M in nat1;                  // by Tnat1in1; LM1 & LM2;   // !! Tnat1in1 := x in nat1 == x in nat & x ~= 0;
! LM3 := (f^M)(a) = a;
! LM4 := A[k:1..M-1, ~((f^k)(a) = a)]; is Lmin4(LS1);              // !! Lmin4 := (S1 := {k:nat1; ff(i) }) in lbint -> A[i:1..min(S1)-1, ~ff(i)];
! L01 :=  A[i_nat, dom(f^(i%M)) = A];  is L14; // AFN :: L14 := dom(f^i) = dom(f);     // i_nat :: [ !! L01_type := i%M in nat; ];

! LM5 := A[i_nat, orbf(i) = orbf(i%M)];
 EqProof LM5;
F0 := i in nat;                        assume;
F01 := Ex[n:nat, F01a := i=n*M + i%M]; is Tnatres;  // !! Tnatres := A[i:nat, m:nat1, E[n:nat, i = n*m + i%m]]; // actually, E1[
F02 := orbf(i%M) = (f^(i%M))(a);       byeq Red("F");
F03 :=  A[n,r:nat, (f^(n*M+r))(a) = (f^r)(a)]; is L15(LM3); // !! L15 := A[m:nat1, a:dom(f), (f^m)(a) = a -> A[n,r:nat, (f^(n*m+r))(a) = (f^r)(a)]];
F1 := orbf(i);                         by Red("F");
F2 := (f^i)(a);                        by F01a;
F3 := (f^(n*M + i%M))(a);              by F03;  
F4 := (f^(i%M))(a);                    by -F02;
F5 := orbf(i%M);     
 end EqProof LM5;

! LM6 := A[i,j: 0..M-1, i ~= j -> orbf(i) ~= orbf(j)];   // injectivity;
 Proof LM6;
F0 := i in 0..M-1;                     assume;
F01 := j in 0..M-1;                    assume;
F02 := i ~= j;                         assume;
F03 := orbf(i) = orbf(j);              assume; by Red("F");
F1 := (f^i)(a) = (f^j)(a);
k := abs(i-j);
F2 := k in nat1;                       is Labs3;            // !! Labs3 := A[i,j:int, i ~= j -> abs(i-j) in nat1];
F3 := (f^k)(a) = a;                    is L16(F1);          // !! L16 := A[i,j:int, a:dom(f), (f^i)(a) = (f^j)(a) -> (f^abs(i-j))(a) = a];
F4 := k in S;                          by Axab; F2 & F3;
F5 := k < M;                           is Labs4(M,i,j)(F02);       // !! Labs4 := A[m:nat1, i,j: 0..m-1, i~=j -> abs(i-j) < m];
F6 := k nin S;                         is Tmin3(F5);        // !! Tmin3 :=  A[S:lbint,x:int, x < min(S) -> x nin S];
F7 := false;                           is Stautin(F4 & F6); //  ! Stautin := (x in X) & (x nin X) -> false;
 end Proof LM6;

! LM8 := A[i: 0..M-1, orbf(i) in A];   by Red("F"); is L08; // ! L08 := A[i_nat, (f^i)(a) in A];
! LM9 := 0..M-1 <: nat;
! LM10 := 0 in 0..M-1;                 is Tseg9;            // !! Tseg9 := 0 in 0..n1-1;              // var n1, nat1;
// !! Lorbf1 := orbf in seqp(nat,M);            // seqp(nat,M): periodic sequences of nat with period M;

sorb := F[i:0..M-1, orbf(i)];          
! Lsorb1 := sorb in seqinj(A);         by LFseqinj; LM8 & LM6;   // !! LFseqinj := F[x: 0..k, G(x)] in seqinj(A) == 
                                                                 // A[x: 0..k, G(x) in A] & A[x,y: 0..k, x~=y -> G(x) ~= G(y)];
Mp := [orbf, M];
! LMp := Mp in FNpnat;                 by Axab; LorbfFN & Lorbfdom & LM7 & LM5;

! Lsorb2 := im(sorb) = im(orbf);       is LFNpnatim.Mp;  // FNpnat :: !! LFNpnatim := im(F[k:0..p-1, f(k)]) = im(f); // orbf := F[i_nat, (f^i)(a)]; 

! Lsorb0 := seqinj(A) <: SEQ;          is LseqinjSEQ;  // !! LseqinjSEQ := seqinj(A) <: SEQ;  // A's are different: first: A := dom(f), other: var; 

! LsorbSEQ := sorb in SEQ;             is TinIn(Lsorb1 & Lsorb0); 
! Lsorb3 := l(sorb) = M;               is TFl;                        // !! TFl := l(F[i:0..n1-1, G(i)]) = n1;
                                                     // !! Axl := l(f) = #dom(f);
! L1 := im(sorb) in finset;            is LFimseg;   // !! LFimseg := im(F[i:0..k, G(i)]) in finset;
! Lsorb4 := #(im(sorb)) = M;           by -Lsorb3,2; is Lseqinj2(Lsorb1);   // Lseqinj2 := z in seqinj(A) -> #(im(z)) = l(z); // 2: M in sorb;

orb := im(orbf);                       // orbf := F[i_nat, (f^i)(a)];
! Lorb0 := orb = im(orbf);             is Axrefl;    // !! Axrefl := x = x; 
! Lorb1 := orb = im(sorb);             is -Lsorb2;   // ! Lsorb2 := im(sorb) = im(orbf); 
! LorbR := orb = R[i:0..M-1, orbf(i)]; by Lorb1;     is TimF;               // !! TimF   := im(F[d, g]) = R[d, g];  
! Lorbfinset := orb in finset;         by LorbR;     is TfinsetRseg;        // !! TfinsetRseg := R[k:i..j, g] in finset;
! Lorbf01 := a = orbf(0);              is -Lorbf0;                          // ! Lorbf0 := orbf(0) = a; 

! Lorb2 := a in orb;                   by Lorbf01,1; is Tvalim(orbf,0);     // ! Lorbf01 := a = orbf(0); // fx :: !! Tvalim := f(x) in im(f);
//  Proof Lorb2;
// F1 := a in orb;                        by LorbR;
// F2 := a in R[i:0..M-1, orbf(i)];       by TRin;         // !! TRin := z in R[d,f] == E[d, z = f]; 
// F3 := E[i:0..M-1, a = orbf(i)];        is Witness(0);   // uses ! LM10 := 0 in 0..M-1; and ! Lorbf01 := a = orbf(0);  
//  end Proof Lorb2;
  
! Lorb3 := orb ~= {};                  is Tinnemp(Lorb2);                    // ! Tinnemp := x in X -> X ~= {};
! Lorbfinset1 := orb in finset1;       by Tfinset1;   Lorbfinset & Lorb3;
// !! Torb1 := orb = R[i:nat, (f^i)(a)];s
                                                                             // AFN :: !! LAFNinj := injective(f);
! Lorb4 := orb <: A;                   is Lorbfim;                           // ! Lorbfim := im(orbf) <: A; // orb := im(orbf); // A := dom(f);

! Lorb5 := A[x:orb, f(x) in orb];                                            // fA := {f, A; f in FN, A in set, AxfA1 := A <: dom(f) };  
 Proof Lorb5;                          // orbf := F[i_nat, (f^i)(a)];        // ! Lorb0 := orb = im(orbf);
F0 := x in orb;                        assume;  by TimFin;                   // !! TimFin := z in im(F[d,f]) == E[d, z = f]; 
F01 := Ex[i_nat, F01a := x = (f^i)(a)];
F02 := f(x) = (f^(i+1))(a);            byeq F01a, LAFN4;                     // AFN :: !! LAFN4 := A[x:dom(f),k:int, f((f^k)(x)) = (f^(k+1))(x)];
F03 := i+1 in nat;                     is Tnatadd;                           // Tnatadd := A[k,m:nat, k+m in nat];
G0 := f(x) in orb;                     by TimFin;
G1 := E[j:nat, f(x) = (f^j)(a)];       is Witness(i+1);  
 end Proof Lorb5;

! Lorb6 := f|orb in fn(orb,orb);       by Trein@fA; Lorb5;                   // fA :: !! Trein := A[B:set, f|A in fn(A,B) == A[x:A, f(x) in B]];
! Lorb7 := injective(f|orb);           is Tinjre@FN(Lorb4 & LAFNinj);        // !! Tinjre := A <: dom(f) & injective(f) -> injective(f|A); 
! Lorb8 := f|orb in afn(orb);          is Lafn2(Lorbfinset & Lorb6 & Lorb7); // !! Lafn2 := A in finset & f in fn(A,A) & injective(f) -> f in afn(A);
// ! Lorb8a := f|orb in AFN;           is TinIn(Lorb8 & TafnAFN);            // !! TafnAFN := afn(A) <: AFN;
trivorb := #orb = 1;                   // trivial orbit
ntrivorb := ~(#orb = 1);               // nontrivial orbit
]; // perma :: [

dsjp := F[f,g: perm, ds(f) NI ds(g)];      // dom(f) = dom(g) && ...

perm :: [  // 2
x_A := {x; x in A};   // var v_A, A;
! Lorbsin := A[x_A, orb(f,x) in orbs]; is TAinR;           // !! TAinR   := A[d, f in R[d,f]];
! L17 := A[x_A, orb(f,x) <: A];        is Lorb4(f,x@x_A);  // !! Lorb4 := orb <: A; 
! L17a := A[x_A, orb(f,x) in P[A] ];   by AxP; L17;        // !! AxP := Z in P[Y] == Z <: Y;
! L18 :=  A[x_A, x in orb(f,x)];       is Lorb2(f,x@x_A);  // ! Lorb2 := a in orb;
! L18a := A[x:dom(f), x in orb(f,x)];  is L18;             // A := dom(f), rep can replace A with A.g, not dom(g);

! L18b := A[x:dom(f), f(x) in orb(f,x)]; 
 Proof L18b;
F0 := x in dom(f);                      assume;
F01 := x in orb(f,x);                   is L18a;
F02 := orb(f,x) <: dom(f);              is L17;
F03 := A[z:orb(f,x), f(z) in orb(f,x)]; is Lorb5(f,x);     // ! Lorb5 := A[x:orb, f(x) in orb];
G0 := f(x) in orb(f,x);                 is F03(x);    // @perma;  
 end Proof L18b;

! L19 := A[x_A, orb(f,x) ~= {}];       is Lorb3(f,x@x_A);    // ! Lorb3 := orb ~= {}; // ??? commented 2022.11.25 (did not work: new eqadt);

                                                          
! L20 := A[x_A, orb(f,x) = im(orbf(f,x))]; is Lorb0(f, x@L20);  // ! Lorb0 := orb = im(orbf);

! Lorbf_fx := A[x_A, orbf(f,x) = F[i_nat, (f^i)(x)] ];         byeq Red;

! Lorb_fx := A[x_A, orb(f,x) = im(F[i_nat, (f^i)(x)])];        by -Lorbf_fx; L20;
! LorbR1 := A[x:dom(f), orb(f,x) = R[i_nat, (f^i)(x)]];        by -TimF; Lorb_fx;    // !! TimF   := im(F[d,g]) = R[d,g]; 

! L21 := A[x:A, k:nat, orbf(f,(f^k)(x)) = F[i_nat, orbf(f,x)(i+k)] ];
 EqProof L21;
F0 := x in A;                          assume;         
F01 := orbf(f,x) = F[i_nat, (f^i)(x)];                         byeq Red;
F02 := F[i_nat, orbf(f,x)(i+k)] = F[i_nat, (f^(i+k))(x)];      byeq F01, Red("F");  // orbf := F[i_nat, (f^i)(a)];
F1 := orbf(f,(f^k)(x));                by Red;
F2 := F[i_nat, (f^i)((f^k)(x))];       by TAFN3;     // AFN :: !! TAFN3 := A[x:dom(f),i,k:int, (f^i)(f(k)(x)) = (f^(i+k))(x)];
F3 := F[i_nat, (f^(i+k))(x)];          by -F02;
F4 := F[i_nat, orbf(f,x)(i+k)];
 end EqProof L21;

// Mpfx := [orbf(f,x), M(f,x)];

// ! LMpfx := A[x_A, Mpfx in FNpnat];     is LMp(f,x@x_A);            // ! LMp := Mp in FNpnat;    // Mp := [orbf, M];  

! L22 := A[x,y:A, y in orb(f,x) == orb(f,y) = orb(f,x)];
 Proof L22;
F0 := x in A;                          assume;
F01 := y in A;                         assume;  
G0 := y in orb(f,x) == orb(f,y) = orb(f,x); by Deqv; L1 & L2;

L1 := y in orb(f,x) -> orb(f,y) = orb(f,x);
  EqProof L1;                                  
F02 := y in orb(f,x);                  assume; by Lorb_fx,TimFin; // !! TimFin := z in im(F[d,f]) == E[d, z = f];
F03 := Ex[k:nat, F03a := y = (f^k)(x)];                           // ! Lorb_fx := A[x_A, orb(f,x) = im(F[i_nat, (f^i)(x)])];
Mpfx := [orbf(f,x), (M@perma)(f,x)];
! LMpfx := Mpfx in FNpnat;             is LMp(f,x);               // ! LMp := Mp in FNpnat;    // Mp := [orbf, M];  
F1 := orb(f,y);                        by F03a;
F2 := orb(f, (f^k)(x) );               by L20;                    // ! L20 := A[x_A, orb(f,x) = im(orbf(f,x))];
F3 := im(orbf(f, (f^k)(x) ));          by L21;                    // ! L21 := A[x:A, k:nat, orbf(f,(f^k)(x)) = F[i_nat, orbf(f,x)(i+k)] ]; 
F4 := im( F[i_nat, orbf(f,x)(i+k)]);   by LFNpnatim1.Mpfx;        // FNpnat :: !! LFNpnatim1 := A[k:nat, im(F[i_nat, f(i+k)]) = im(f)];  
F5 := im(orbf(f,x));                   by -L20;
F6 := orb(f,x);
  end EqProof L1;

L2 := orb(f,y) = orb(f,x) -> y in orb(f,x);
  Proof L2;
F0 := orb(f,y) = orb(f,x);             assume;
F1 := y in orb(f,y);                   is L18; by F0;             // ! L18 := A[x_A, x in orb(f,x)]; 
F2 := y in orb(f,x);
  end Proof L2;
 end Proof L22;
                                                                
! LorbS := A[x_A, f(x)=x == orb(f,x)={x}]; 
 Proof LorbS;
F0 := x in A;                      assume;
G0 := f(x)=x == orb(f,x)={x};      by Deqv;  L1 & L2;         // ! Deqv := (p==q) == (p->q) & (q->p);  is Taut; // Deqv is a tautology;
L1 := f(x)=x -> orb(f,x)={x};      by LorbR1; is TAFNRS;      // ! LorbR1 := A[x:dom(f), orb(f,x) = R[i_nat, (f^i)(x)]];
L2 := orb(f,x)={x} -> f(x)=x;                                 // !! TAFNRS := A[x:dom(f), f(x)=x -> R[i_nat, (f^i)(x)] = {x} ];
  Proof L2;
F0 := orb(f,x)={x};                assume;
F1 := f(x) in orb(f,x);            is L18b;   by F0;          // ! L18b := A[x:dom(f), f(x) in orb(f,x)]; 
F2 := f(x) in {x};                 by Axcoll1;                // !! Axcoll1 := All(x, All(a, x in {a} == x = a)); 
F3 := f(x)=x;
  end Proof L2; 
 end Proof LorbS;
                                                                                    // !! Axneq := z ~= z1 == ~(z = z1); 
! LorbSN := A[x_A, f(x) ~= x == orb(f,x) ~= {x}];  by Axneq,Axneq,-TAAN; LorbS;     // !! TAAN := A[x:B, P(x)== Q(x)] == A[x:B, ~P(x) == ~Q(x)]; 

orbs := R[x_A, orb(f,x)];                                     // x_A := {x; x in A}; 
! Torbs := orbs = R[x_A, orb(f,x)];       is Axrefl;          // x = x; 
! Torbs1 := orbs = R[x:dom(f), orb(f,x)]; is Torbs;
! Torbs2 :=  A[x_A, orb(f,x) in orbs];    is TAinR;           // !! TAinR   := A[d, f in R[d,f]];   // A := dom(f);
! L7 := orbs in finset;                   is TfinsetR(L06);   // !! TfinsetR := X in finset -> R[x:X, g] in finset; // ! L06 := A in finset;
! LorbsInP := orbs <: P[dom(f)];          by TRA; L17a;       // !! TRA  := R[d, f] <: B == A[d, f in B];  // ! L17a := A[x_A, orb(f,x) in P[A] ]; 

Q_orbs := {Q; AxQ := Q in orbs};
! LQ_orbs := Q_orbs = orbs;            is Tabin;           // ! Tabin := {x; x in X} = X;                                                        
! L7a := Q_orbs in finset;             by LQ_orbs; L7;

Q_orbs :: [  // 1
! L0 := Ex[x0:A, L0a := Q = orb(f,x0)];  by -TRin; AxQ;               // !! TRin := z in R[d,f] == E[d, z = f]; 
! LQnemp := Q ~= {};                   by L0a;  is L19;               // ! L19 := A[x_A, orb(f,x) ~= {}];
! L01 := A = dom(f);                   is Axrefl;                     // !! Axrefl := x = x;
! LQA := Q <: A;                       by L0a; is Lorb4(f,x0);        // ! Lorb4 := orb <: A;
! LQdom := Q <: dom(f);                by -L01; LQA;                  // because dom(f) = (2,0,1630), A = (2,0,13); not merging for printing; req ???
! L8 := Q in finset;                   is TfinsetIn(L06 & LQA);       // !! TfinsetIn := A in finset & B <: A -> B in finset; / ! L06 := A in finset;
! L8a := Q in finset1;                 by Tfinset1; L8 & LQnemp;      // !! Tfinset1 := X in finset1 == X in finset & X ~= {}; 

x_Q := {x; x in Q};                    // Q_orbs := {Q; AxQ := Q in orbs};
x_Q :: !! L0 := x in dom(f);
 
! LQorb := A[x_Q, orb(f,x) = Q];      // ! L22 := A[x,y:A, y in orb(f,x) == orb(f,y) = orb(f,x)];  // ??? x_Q: error in rnam 
 Proof LQorb;
F0 := x in Q;                          assume;                        // z in orb(f,x0);
F01 := x in A;                         is TinIn(F0 & LQA);            // ! LQA := Q <: A;
F1 := orb(f,x) = Q;                    by L0a, -L22; F0;              // is L22(x0,z)(F0);
 end Proof LQorb;
                                                           
! LQdsIn := Q <: ds == atl2(Q);        // x_Q := {x: x in Q};         // ! LQA := Q <: A;   // ! LQnemp := Q ~= {};
 Proof LQdsIn;                                                        // !! TAIn1 := A <: B & A[x:B, P(x)] -> A[x:A, P(x)];  
F0 := A[x_Q, f(x)~=x == orb(f,x)~={x}]; is TAIn1(LQA & LorbSN);       // ! LorbSN := A[x_A, f(x) ~= x == orb(f,x) ~= {x}];
F00 := A[x_Q, F0a := orb(f,x) ~= {}];   is L19;                       // ! L19 := A[x_A, orb(f,x) ~= {}];
F01 := A[x_Q, orb(f,x) ~= {x} == atl2(orb(f,x))]; is Tatl2a(F0a);     // !! Tatl2a := X ~= {} -> X ~= {a} == atl2(X);              
F1 := A[x_Q, x in ds == atl2(orb(f,x))]; by LAFNds(x@x_Q),-F01; F0;   // !! LAFNds := A[x:dom(f), x in ds == f(x) ~= x];
F1;                                    by LQorb;                      // ! LQorb := A[x_Q, orb(f,x) = Q];
F2 := A[x_Q, x in ds == atl2(Q)];      by TAeqvcon(LQnemp);           // !! TAeqvcon := B ~= {} -> A[x:B, P(x) == R] == (A[x:B, P(x)] == R);
F3 := A[x_Q, x in ds] == atl2(Q);      by -TInA; LQdsIn;              // !! TInA := A <: B == A[x:A, x in B]; 
// F4 := Q <: ds == atl2(Q);           // error: no merging;
 end Proof LQdsIn;
                      
! LQds1 := atl2(Q) == A[x_Q, f(x) ~= x];  byeq -LQdsIn, -LAFNdsIn;    // !! LAFNdsIn := A[B:P[dom(f)], A[x:B, f(x) ~= x] == B <: ds];        
// !! LQds1c := atl2(Q) -> A[x:Q, c(x) ~= x];  // !! LQds1 := atl2(Q) -> A[x:Q, f(x) ~= x]; is LQds1.c;

! LfQ_type := f|Q in afn(Q);           by L0a; is Lorb8(f,x0);        //  ! Lorb8 := f|orb in afn(orb); 
LfQ_type;                              by Tafnin1; LfQ_AFN & LfQ_dom; // !! Tafnin1 := f in afn(A) == f in AFN & dom(f)=A;
! LfQ_AFN := f|Q in AFN;
! LfQ_dom := dom(f|Q) = Q; 
! LfQ_dom1 := dom(f|Q) <: A;           by LfQ_dom; LQA;               // ! LQA := Q <: A;
! LfQ_dom2 := dom(f|Q) in finset1;     by LfQ_dom; L8a;
! LfQ_perm := f|Q in perm;             by Tperm;  LfQ_AFN & LfQ_dom2; // ! Tperm := g in perm == g in AFN & dom(g) in finset1; 

! LfQ_orb := A[x:Q, orb(f|Q,x) = Q]; 
 EqProof LfQ_orb;                      // !! TAFNre := B <: dom(f) & f|B in AFN -> A[i:nat, b:B, ((f|B)^i)(b) = (f^i)(b)];
F0 := x in Q;                          assume;                        // ! TinIn := x in X2 & X2 <: Y2 -> x in Y2; 
F01 := x in A;                         is TinIn(F0 & LQA);            // ! LQA := Q <: A;
F02 := A[i:nat,b:Q,((f|Q)^i)(b)=(f^i)(b)];                            is TAFNre(LQdom & LfQ_AFN);
F03 := A[x:Q, orb(f|Q,x) =  R[i_nat, ((f|Q)^i)(x)]];                  is LorbR1.(f|Q);
F1 := orb(f|Q,x);                      by F03;                        // ! LorbR1 := A[x:dom(f), orb(f,x) = R[i_nat, (f^i)(x)]]; 
F2 := R[i_nat, ((f|Q)^i)(x)];          by F02;
F3 := R[i_nat, (f^i)(x)];              by -LorbR1;
F4 := orb(f,x);                        by LQorb;                      // ! LQorb := A[z:Q, orb(f,z) = Q]; 
F5 := Q;
 end EqProof LfQ_orb;

! LQorbR := R[x:Q, orb(f,x)] = {Q};
 Proof LQorbR;                                           // !! TRAC1 := X ~= {} -> A[x:X, G(x)=C] == R[x:X, G(x)] = {C}];
F1 := A[x:Q, orb(f,x) = Q] == R[x:Q, orb(f,x)] = {Q};    is TRAC1(LQnemp);   // ! LQnemp := Q ~= {};
LQorbR;                                is F1(LQorb);      // !! LQorb := A[x:Q, orb(f,x) = Q]; // F2 := R[x:Q, orb(f,x)] = {Q};
 end Proof LQorbR;

! LfQ_orbs := orbs.(f|Q) = {Q};
 EqProof LfQ_orbs;                                       // fA := {f, A; f in FN, A in set, AxfA1 := A <: dom(f) };         
// F0 := orbs.(f|Q) = R[x:dom(f|Q), orb(f|Q,x)]; is Torbs.(f|Q);
F1 := orbs.(f|Q);                       by Torbs.(f|Q);  // ! Torbs := orbs(f) = R[x_A, orb(f,x)]; ??? worked in C1, but not in C3;
F2 := R[x:dom(f|Q), orb(f|Q,x)];        by Tredom@fA;    // !! Tredom := dom(f|A) = A; 
F3 := R[x:Q, orb(f|Q,x)];               by LfQ_orb;      // !! LfQ_orb := A[x:Q, orb(f|Q,x) = A)];
F4 := R[x:Q, Q];                        by TRS1(LQnemp); // !! TRS1 := X ~= {} -> R[x:X, c] = {c};
F5 := {Q};
 end EqProof LfQ_orbs;
]; // Q_orbs:: [  // 1

! LorbsU := U[x_A, orb(f,x)] = A;      is TUIn1(L17 & L18);  // !! TUIn1 := A[x:A, G(x) <: A] & A[x:A, x in G(x)] -> U[x:A, G(x)] = A;
! Lorbsun := union(orbs) = A;          by -TUunion; LorbsU;  // !! TUunion := U[d,w] = union(R[d,w]);
! Lorbsnemp := A[Q_orbs, Q ~= {}];     by TAR; L19;          // !! TAR  := A[x: R[d, f], Q(x)] == A[d, Q(f) ]; // ! L19 := A[x_A, orb(f,x) ~= {}];
// !! LQds1A := A[Q_orbs, atl2(Q) == A[x_Q, f(x) ~= x]];           // ! LQds1 := atl2(Q) == A[x_Q, f(x) ~= x];
! L24 := A[Q:orbs,x:Q, x in A & Q = orb(f,x)];
 Proof L24;
F0 := Q in orbs;                       assume;    by TRin;       // !! TRin := z in R[d,f] == E[d, z = f]; // orbs := R[x_A, orb(f,x)];
F00 := Ex[y:A, F0a := Q = orb(f,y)];
F01 := Q <: A;                         by F0a; is L17;           // ! L17 := A[x_A, orb(f,x) <: A];
F02 := x in Q;                         assume; by F0a;
F03 := x in orb(f,y);                  by L22;
F04 := orb(f,x) = orb(f,y);                                      // is L22(F03);
G1 := x in A;                          is TinIn(F02 & F01);
G2 := Q = orb(f,x);                    by F04;  F0a;
 end Proof L24;

! LorbsNI := A[Q,Q1:orbs, Q /\ Q1 ~= {} -> Q = Q1];
 Proof LorbsNI;
F0 := Q in orbs;                        assume;  // by TRin;     // !! TRin := z in R[d,f] == E[d, z = f]; // orbs := R[x_A, orb(f,x)];
// F00 := Ex[y:A, F0a := Q = orb(f,y)];
F01 := Q1 in orbs;                      assume;  // by TRin; 
// F02 := Ex[x1:A, F02a := Q = orb(f,x1)];
F03 := Q /\ Q1 ~= {};                   assume;  by TInempE;     // ! TInempE := A/\B ~= {} == Exist(x, x in A & x in B); byeq TinnempE, AxI;
F04 := Existx(x, (F04a := x in Q) & (F04b := x in Q1));
(F02 := x in A) & (F1 := Q = orb(f,x)); is L24(Q,x);
F02 & (F2 := Q1 = orb(f,x));            is L24(Q1,x);
F3 := Q = Q1;                           is Axeq2(F1 & F2);       // !! Axeq2 := x=a & y=a -> x=y;
 end Proof LorbsNI;

partA := [A,orbs];                      // !! Tprtin := [A,B] in partition == union(B)=A & A[Q:B, Q ~= {}] & A[Q1,Q2:B,  Q1/\Q2 ~= {} -> Q1=Q2]; 
! LpartA := partA in partition;         by Tprtin; Lorbsun & Lorbsnemp & LorbsNI;

! Lorbsneq := A[Q1,Q2: orbs, Q1 ~= Q2 == Q1 NI Q2];     is Tprt2a.partA;   // partition :: !! Tprt2a := A[Q1_Q2_B, Q1 ~= Q2 == Q1 NI Q2];
! LorbsE := All(Q, Q in orbs == E[x:A, Q = orb(f,x)]);  is TRin;           // !! TRin := z in R[d,f] == E[d, z = f]; 

torbs := Q_orbs && one(Q);             // trivial orbits;                  // one(Q) == #Q = 1; (if Q is finite);
                                                                           // we are in perm;
ntorbs := Q_orbs && atl2(Q);           // nontrivial orbits;               // Q_orbs := {Q; Q in orbs}; // atl2(Q) == #Q >= 2;
! LntorbsX := X in ntorbs == X in orbs & atl2(X);  byeq Axdconj,LQ_orbs;   // Axdconj := z in d&&P == z in d & Rep(d,P,z); 
! LntorbsX1 := X in ntorbs -> atl2(X);  is Taut((p == q1 & q2) -> (p->q2))(LntorbsX); 

! L27 := A[Q_orbs, atl2(Q) or one(Q)]; // ! Lorbsnemp := A[Q_orbs, Q ~= {}];
 Proof L27;
F0 := Q in orbs;                      assume;
F1 := Q = {} or one(Q) or atl2(Q);    is  Temp_one_atl2;         // !! Temp_one_atl2 := X = {} or one(X) or atl2(X);
F2 := ~(Q = {});                      by -Axneq; is Lorbsnemp;   // !! Axneq := z ~= z1 == ~(z = z1); // ! Lorbsnemp := A[Q_orbs, Q ~= {}];
F3 := atl2(Q) or one(Q);              is Taut((p or p1 or p2) & ~(p) -> (p2 or p1))(F1 & F2); 
 end Proof L27;

! L27a := A[Q_orbs, ~(atl2(Q) & one(Q))];   is Tatl2b;           // !! Tatl2b := ~(atl2(X) & one(X));

! Lorbs := orbs = ntorbs \/ torbs;
 EqProof -Lorbs;                      // ??? EOL is not considered as space !!!
F1 := ntorbs \/ torbs;                by LdconjU;                // !! LdconjU := (d&&P) \/ (d&&Q) = d&&(P or Q); 
F2 := Q_orbs&&(atl2(Q) or one(Q));    by LdconjA(L27);           // !! LdconjA := A[d,P] == d&&P = d;  
F3 := Q_orbs;                         by LQ_orbs;                // ! LQ_orbs := Q_orbs = orbs;
F4 := orbs;
 end EqProof -Lorbs;

// ipp!findts: not in ts, s, its=  LorbF1 4415
// ERROR: hprs: s != T= #2.958  #2.64655  - (LorbF1 ):= #2.957  ntorbs \/ torbs  s= -


! LorbsNItnt := ntorbs NI torbs;      by LdconjNI;  L27a;        // !! LdconjNI := d&&P NI d&&Q == A[d, ~(P & Q)]; 


// ! Tntorbs := X in Q_orbs -> X in ntorbs == atl2(X);  is Ldconjimp; // ! Ldconjimp :=  z in d -> z in (d && P) == Rep(d,P,z);
! Tntorbs := A[Q_orbs, Q in ntorbs == atl2(Q)];
 Proof Tntorbs;
F0 := Q in orbs;                       assume; by -LQ_orbs;             // ! LQ_orbs := Q_orbs = orbs;
F01 := Q in Q_orbs;
G0 := Q in ntorbs == atl2(Q);          byeq Ldconjimp(F01);             // ! Ldconjimp :=  z in d -> z in (d && P) == Rep(d,P,z);
 end  Proof Tntorbs;

! Ttorbs := A[Q_orbs, Q in torbs == one(Q)];                            // one(Q) == #Q = 1; (if Q is finite);
 Proof Ttorbs;
F0 := Q in orbs;                       assume; by -LQ_orbs;             // ! LQ_orbs := Q_orbs = orbs;
F01 := Q in Q_orbs;
G0 := Q in torbs == one(Q);            byeq Ldconjimp(F01);             // ! Ldconjimp :=  z in d -> z in (d && P) == Rep(d,P,z);
 end  Proof Ttorbs;
                                                                        // ! Lorbsnemp := A[z:orbs, z ~= {}]; 
! LntorbsIn := ntorbs <: orbs;         by -LQ_orbs; is LdconjIn;        // !! LdconjIn := d&&P <: d; // ! LQ_orbs := Q_orbs = orbs;
! Lntorbsnemp := A[z:ntorbs, z ~= {}]; is TAIn1(LntorbsIn & Lorbsnemp); // !! TAIn1 := A <: B & A[x:B, P(x)] -> A[x:A, P(x)]; 

// ! Lntorbs := A[Q_orbs, A[a,b:Q, a ~= b -> Q in ntorbs]];         // not used;
/* Proof Lntorbs;
F0 := Q in orbs;                       assume;
F01:= a in Q;                          assume;
F02:= b in Q;                          assume;
F03 := a ~= b;                         assume;                    // !! Tatl2 := a in X & b in X & a ~= b -> atl2(X);
F1 := atl2(Q);                         is Tatl2(F01 & F02 & F03); // Q_orbs :: ! L8 := Q in finset;
F2 := Q in ntorbs;                     by Axdconj; F0 & F1;       // !! Axdconj := z in (d&&P) == z in d & Rep(d,P,z);
 end Proof Lntorbs;
*/                                                                  // !! Ldconjfs := d in finset -> d&&P in finset;
! L9 := ntorbs in finset;              is Ldconjfs(L7a);          // ! L7a := Q_orbs in finset; // orb(f,x) ~= {}

! Lntorbs0 := A[x_A, orb(f,x) ~= {x} == orb(f,x) in ntorbs]; 
 EqProof Lntorbs0;
F0 := x in A;                          assume;                    // ! Torbs2 :=  A[x_A, orb(f,x) in orbs];
F01 := orb(f,x) in Q_orbs;             by LQ_orbs; is Torbs2;     // ! LQ_orbs := Q_orbs = orbs;  
F02 := orb(f,x) ~= {};                 is L19;                    // ! L19 := A[x_A, orb(f,x) ~= {}];
F1 := orb(f,x) ~= {x};                 by Tatl2a(F02);            // !! Tatl2a := X ~= {} -> X ~= {a} == atl2(X);
F2 := atl2(orb(f,x));                  by -Tntorbs;               // ! Tntorbs := A[Q_orbs, Q in ntorbs == atl2(Q)];  
F3 := orb(f,x) in ntorbs;      
 end EqProof Lntorbs0;
                                                                                             // !! LAFNds := A[x:dom(f), x in ds == f(x) ~= x]; 
! Lntorbs1 := A[x:dom(f), x in ds == orb(f,x) in ntorbs];  by LAFNds,-Lntorbs0;  is LorbSN;  // ! LorbSN := A[x_A, f(x) ~= x == orb(f,x) ~= {x}]; 
/* Proof Lntorbs1;
F0 := x in dom(f);                     assume;
F01 := f(x) ~= x;                      assume;                     
F1 := x in orb(f,x);                   is L18;                             // ! L18 := A[x_A, x in orb(f,x)]; 
F2 := f(x) in orb(f,x);                is L18b;                            // !! L18b := A[x:dom(f), f(x) in orb(f,x)]; 
F3 := orb(f,x) in ntorbs;              is Lntorbs(orb(f,x))(f(x),x)(F01);  // ! Lntorbs := A[Q_orbs, A[a,b:Q, a ~= b -> Q in ntorbs]];
 end  Proof Lntorbs1;
*/                                                                       
! Lntorbs2 := A[Q_orbs, Q <: ds == Q in ntorbs]; byeq LQdsIn@Q_orbs,-Tntorbs;  // ! LQdsIn := Q <: ds == atl2(Q);  

! Lntorbsun := union(ntorbs) = ds;                                         // ! Tntorbs := A[Q_orbs, Q in ntorbs == atl2(Q)];      
 Proof Lntorbsun;                      by Axext;  L1 & L2;                // ! Axext := X = Y == X <: Y & Y <: X;  
L1 :=  union(ntorbs) <: ds;            by AxIn;
G1 := All(x, x in union(ntorbs) -> x in ds);
  Proof G1;                            // x in union(ntorbs);
assume(x);
F0 := x in union(ntorbs);              assume;  by Tunionin;               // !! Tunionin := x in union(A) == Exist(Y, Y in A & x in Y);
F1 := Existx(Y, (F1a := Y in ntorbs) &  (F1b := x in Y)); 
F2 := Y <: ds;                         by Lntorbs2;  F1a;                  // !! Lntorbs2 := A[Q_orbs, Q <: ds == Q in ntorbs]; 
F3 := x in ds;                         is TinIn(F1b & F2);
  end Proof G1;
L2 := ds <:  union(ntorbs);            by AxIn;  
G2 := All(x, x in ds -> x in union(ntorbs));
  Proof G2;
assume(x);
F0 := x in ds;                         assume;                             
F01 := x in A;                         is TinIn(F0 & Lds1);                // ! Lds1 := ds <: A;  
F1 := orb(f,x) in ntorbs;              by -Lntorbs1; F0;                   // !! Lntorbs1 := A[x:dom(f), x in ds == orb(f,x) in ntorbs];  
F2 := orb(f,x) <: union(ntorbs);       is Tunion5(F1);                     // !! Tunion5 := X in A -> X <: union(A);
F3 := x in orb(f,x);                   is L18;                             // ! L18 := A[x_A, x in orb(f,x)]; 
F4 := x in union(ntorbs);              is TinIn(F3 & F2);                  // ! TinIn := x2 in X2 & X2 <: Y2 -> x2 in Y2;
  end Proof G2;
 end Proof Lntorbsun;
                                                                           // ! LntorbsIn := ntorbs <: orbs;
LntorbsNI := A[Q,Q1:ntorbs, Q /\ Q1 ~= {} -> Q = Q1]; is TAIn2(LntorbsIn & LorbsNI); // !! TAIn2 := A <: B & A[x,y:B, P(x,y)] -> A[x,y:A, P(x,y)];  
               // !! Tunion10 := B ~= {{}} -> union(B) ~= {} == B ~= {}; // !! TASemp := A[X:B, X ~= {}] -> B ~= {{}};
partds := [ds, ntorbs];
! Lpartds := partds in partition;      by Tprtin; Lntorbsun & Lntorbsnemp & LntorbsNI;  // ! Lntorbsnemp := A[z:ntorbs, z ~= {}];

! Lds4 := ds ~= {} == ntorbs ~= {};    is Tprt15.partds; // partition :: !! Tprt15 := A ~= {} == B ~= {};
/*
 Proof Lds4;
F0 := ds ~= {};       assume;                  // ds := {x: dom(f); f(x) ~= x};
x := arb(ds);                      
F01 := x in ds;       is Axarb(F0);             by Axab; F02 & F03;  // !! Axarb := X ~= {} == arb(X) in X;
F02 := x in A;                                  // A := dom(f);
F03 := f(x) ~= x;
F04 := R <: A;                                  is Lorb4(f,x);       // ! Lorb4 := orb <: A; 
F05 := A[z:R, f(z) in R];                       is Lorb5(f,x);       // perma :: ! Lorb5 := A[x:orb, f(x) in orb]; 
R := orb(f,x);
F1 := R in Q_orbs;    by LQ_orbs;               is Lorbsin;          // ! LQ_orbs := Q_orbs = orbs; // ! Lorbsin := A[x_A, orb(f,x) in orbs];
F2 := R in finset;    is Lorbfinset(f,x);                            // ! Lorbfinset := orb in finset;
F3 := x in R;         is Lorb2(f,x);                                 // perma :: ! Lorb2 := a in orb; 
F4 := f(x) in R;      is F05;                   // F05 := A[z:R, f(z) in R];      // is Lorb5(f,x)(x);                               
F5 := atl2(R);        is Tatl2(F4 & F3 & F03);  // !! Tatl2 := a in X & b in X & a ~= b -> atl2(X); // atl2(X) == #X > 1;  (if X is a finite set);
F6 := R in ntorbs;    by Axdconj; F1 & F5;                           // !! Axdconj := z in (d&&P) == z in d & Rep(d,P,z);
F7 := ntorbs ~= {};   is Tinnemp(F6);                                // ! Tinnemp := x in X -> X ~= {}; 
 end Proof Lds4;
*/
                                                                     // ! Teqvneg := (p==q) == (~p == ~q);  
! Lds4a := ds = {} == ntorbs = {};  by Teqvneg, -Axneq; Lds4;        // !! Axneq := z ~= z1 == ~(z = z1);               
! LntorbsSun := A[Q: ntorbs, ntorbs={Q} == union(ntorbs)=Q];         is Tprt16.partds; // partition :: !! Tprt16 := A[Q:B, B={Q} == union(B)=Q];

// Q_orbs :: !! LQ_mcls := Q in mcls.f;
corb := F[Q_orbs, f||Q];                 // cycle for the orbit Q;   // fA :: !! Tredom := dom(f|A) = A; // !! Treval := A[x:A, (f|A)(x) = f(x)];
! Lcorb := A[Q_orbs, corb(Q) = f||Q];    byeq Red("F");              // ! Tdvl := A[f_AFN_B_P, f||B = F[x:dom(f), if(x in B, f(x), x)]]; 
! LcorbF := A[Q_orbs, corb(Q) = F[x_A, if(x in Q, f(x), x)]];        byeq Lcorb, Tdvl; 
! Lcorbdom := dom(corb) = orbs;          byeq TFdom1;                // !! TFdom1 := dom(FAGx) = A; // FAGx := F[x:A, G(x)];          


/*
 EqProof LcorbF;                                              // byeq; did not work !!!
F0 := Q in orbs;                             assume;
F1 := corb(Q);                               by Lcorb;                     // ! Lcorb := A[Q_orbs, corb(Q) = f||Q]; 
F2 := f|Q || A;                              by Tdvl(f|Q@Q_orbs, A);       // ! Tdvl := A[f_AFN_A_set, f||A = F[x:A, if(x in dom(f), f(x), x)]];
F3 := F[x_A, if(x in dom(f|Q), (f|Q)(x), x)]; by Tredom(f,Q@Q_orbs);       // fA :: !! Tredom := dom(f|A) = A; 
F4 := F[x_A, if(x in Q, (f|Q)(x), x)];       by TrevalA; // (f,Q@Q_orbs,x@x_A); // !! TrevalA := A[f_FN_A_P_dom_f_x_A, (f|A)(x) = f(x)];
F5 := F[x_A, if(x in Q, f(x), x)]; 
 end EqProof LcorbF; 
*/

/* Proof Lcorbafn;                                // !! LafnFif := B<:A & f in afn(B) -> F[x:A, if(x in B, f(x), x)] in afn(A);
F0 := Q in orbs;                              assume; by TRin;             // !! TRin := z in R[d,f] == E[d, z = f]; 
F01 := Ex[x_A, F01a := Q = orb(f,x)];                                      // fA :: !! Treval := A[x:A, (f|A)(x) = f(x)];
F02 := f|orb(f,x) in afn(orb(f,x));           is Lorb8(f,x);               // ! Lorb8 := f|orb in afn(orb);
F03 := orb(f,x) <: A;                         is Lorb4(f,x);               // ! Lorb4 := orb <: A; 
F04 := F[x_A, if(x in orb(f,x), (f|orb(f,x))(x), x)] in afn(A); is LafnFif(F03 & F02); by Treval@fA;  
                                              // !! LafnFif := B<:A & f in afn(B) -> F[x:A, if(x in B, f(x), x)] in afn(A);
F05 := F[x_A, if(x in orb(f,x), f(x), x)] in afn(A); by -Lcorb;            // ! Lcorb := A[Q_orbs, corb(Q) = f||Q]; 
F1 := corb(Q) in afn(A);
//  end Proof Lcorbafn; 
*/
                                                                            // ! Ldvldom := A[f_AFN_B_P, dom(f||B) = dom(f)];  
Q_orbs :: [   // 2 (corb)              // Q_orbs := {Q; Q in orbs};         // orbs := R[x_A, orb(f,x)];  // ! Lcorb := A[Q_orbs, corb(Q) = f||Q]; 
c := f||Q;           // c := corb(Q);  // corb := F[Q_orbs, f || Q];        // ! L07 := afn(A) <: AFN;
// ! Lc := c = F[x_A, if(x in Q,f(x),x)]; is LcorbF;                        // ! LcorbF := A[Q_orbs, corb(Q) = F[x_A, if(x in Q, f(x), x)]]
! Lcdom := dom(c) = A;                 is  Ldvldom;                         // ! Ldvldom := A[f_AFN_B_P, dom(f||B) = dom(f)]; 
! Lcdomfin1 := dom(c) in finset1;      by Lcdom; Axp;                       // Axp := dom(f) in finset1;
! Lcafn := c in afn(A);                is Ldvlafn;                          // !! Ldvlafn := A[f_AFN_B_P, Ldvlafn_type := f||B in afn(dom(f))];
! LcAFN := c in AFN;                   is TinIn(Lcafn & L07);               // ! TinIn := x in X2 & X2 <: Y2 -> x in Y2;  
! LcAFNa := f||Q in AFN;               is LcAFN;
! Lcperm := c in perm;                 by Tperm; LcAFN & Lcdomfin1;         // ! Tperm := g in perm == g in AFN & dom(g) in finset1; 
! LcorbIFN := c in IFN;                is TinIn(LcAFN & TAFNIFN);           // !! TAFNIFN := AFN <: IFN;
! Lcntorbs := ntorbs.c <: orbs.c;      is LntorbsIn.c;                      // ! LntorbsIn := ntorbs <: orbs; 
! LcQP := Q in P[dom(c)];              by Lcdom, AxP; LQA;                  // !! AxP := Z in P[Y] == Z <: Y;  // ! LQA := Q <: A;
                                        // f_AFN_B_P := {f,B; Axf := f in AFN, AxB := B in P[dom(f)], Ax1 := f|B in AFN };
! LcQf := A[x:Q, c(x) = f(x)];         is LdvlB(f,Q);                       // !! LdvlB := A[f_AFN_B_P, A[x:B, (f||B)(x) = f(x) ]];
! Lcid := A[x:A--Q, c(x)=x];           is Ldvlid(f,Q);                      // !! Ldvlid := A[f_AFN_B_P, A[x:A--B, (f||B)(x) = x ]];
/*
 EqProof Lcid;
F0 := x in A--Q;                       assume; by AxD; F01 & F02;           // !! AxD := a1 in X1 -- Y1 == a1 in X1 & a1 nin Y1;
F01 := x in A;
F02 := x nin Q;                        by Axnin;                            // !! Axnin := x nin X == ~(x in X); 
F03 := ~(x in Q);
F1 := c(x);                            by Lc, Red("F");
F2 := if(x in Q, f(x), x);             by Tif2(F03);                        // !! Tif2 := ~p -> if(p,a,b) = b; 
F3 := x;
 end EqProof Lcid;
*/                                                                          
! LQds1c := atl2(Q) == A[x:Q, c(x) ~= x]; by LcQf; LQds1;        // ! LcQf := A[x:Q, c(x) = f(x)];    // !! LQds1 := atl2(Q) == A[x:Q, f(x) ~= x]; 

! Lc_type := c in perm;
 Proof Lc_type;
F0 := dom(c) in finset1;               by Lcdom; Axp;                       // ! Lcdom := dom(c) = A; 
Lc_type;                               by Axdconj; LcAFN & F0;              // Axdconj := z in d&&P == z in d & Rep(d,P,z); 
// G0 := c in perm;
 end Proof Lc_type;                    

! LcQ := c|Q = f|Q;                    is Ldvlre;                           // !! Ldvlre := A[f_AFN_B_P, (f||B)|B = f|B ];  
! LcQ_type := c|Q in perm;             by LcQ; LfQ_perm;                    // ! LfQ_perm := f|Q in perm;   
! LcQ_AFN := c|Q in AFN;               is TinIn(LcQ_type & LpermAFN);       // ! LpermAFN := perm <: AFN;

! Lcorb1 := A[x:Q, orb(c,x) = Q];     
 EqProof Lcorb1;                       // !! TAFNre := B <: dom(f) & f|B in AFN -> A[i:nat, b:B, ((f|B)^i)(b) = (f^i)(b)];
F0 := x in Q;                          assume;                              // fA := {f, A; f in FN, A in set, AxfA1 := A <: dom(f) };  
F00 :=  x in dom(c|Q);                 by Tredom@fA; F0;                    // fA :: !! Tredom := dom(f|A) = A; 
F01 := x in dom(c);                    by Lcdom;    is TinIn(F0 & LQA);     // ! LQA := Q <: A; // ! TinIn := x in X2 & X2 <: Y2 -> x in Y2;
F02 := A[i:nat,b:Q,((c|Q)^i)(b)=(c^i)(b)];          is TAFNre(LQA & LcQ_AFN);
F03 := orb(c|Q,x) = R[i_nat, ((c|Q)^i)(x)];         is  LorbR1.(c|Q)(x);
F1 := orb(c,x);                        by LorbR1.c;                         // ! LorbR1 := A[x:dom(f), orb(f,x) = R[i_nat, (f^i)(x)]];
F2 := R[i_nat, (c^i)(x)];              by -F02;
F3 := R[i_nat, ((c|Q)^i)(x)];          by -F03;
F4 := orb(c|Q,x);                      by LcQ;                              // ! LcQ := c|Q = f|Q;                        
F5 := orb(f|Q,x);                      by LfQ_orb;                          // ! LfQ_orb := A[x:Q, orb(f|Q,x) = Q];
F6 := Q;
 end EqProof Lcorb1;

! LcorbS := A[x:A--Q, orb(c,x) = {x}];                
 Proof LcorbS;
F0 := x in A--Q;                       assume;
F01 := c(x) = x;                       is Lcid;                             // ! Lcid := A[x:A--Q, c(x)=x];
F02 := A[x:dom(c), c(x) = x == orb(c,x) = {x}];        is LorbS.c;          // !! LorbS := A[x_A, f(x)=x == orb(f,x) = {x}];
F1 := orb(c,x) = {x};                  is F02(F01); 
 end Proof LcorbS;

R := R[x:A--Q, orb(c,x)];
! LR := R = R[x:A--Q, {x}];            byeq LcorbS;

! LR1 := R <: torbs.c;                   
 Proof LR1;                            by TRA;                              // !! TRA  := R[d, f] <: B == A[d, f in B];
G0 := A[x:A--Q, orb(c,x) in torbs.c];
  Proof G0;
F0 := x in A--Q;                       assume;
F00 := x in A;                         is TDin1(F0);                        // ! TDin1 := a1 in X1 -- Y1 -> a1 in X1; 
F01 := x in dom(c);                    by Lcdom; F00;                       // ! Lcdom := dom(c) = A; 
F02 := A[x:dom(c), orb(c,x) in orbs.c]; is Lorbsin.c;                       // ! Lorbsin := A[x_A, orb(f,x) in orbs];
F03 := orb(c,x) in orbs.c;             is F02;
F04 := A[Q: orbs.c, Q in torbs.c == one(Q)];   is Ttorbs.c;                 // ! Ttorbs := A[Q_orbs, Q in torbs == one(Q)];
G1 := orb(c,x) in torbs.c;             by F04;
G2 := one(orb(c,x));                   by LcorbS;                           // ! LcorbS := A[x:A--Q, orb(c,x) = {x}]; 
G3 := one ({x});                       is ToneS;                            // !! ToneS := one({x});                     
  end Proof G0;
 end Proof LR1;
     
! LcorbR := R[x:Q, orb(c,x)] = {Q};                    // ! LQorbR := R[x:Q, orb(f,x)] = {Q};
 Proof LcorbR;                                         // !! TRAC1 := X ~= {} -> A[x:X, G(x)=C] == R[x:X, G(x)] = {C}];
F1 := A[x:Q, orb(c,x)= Q] == R[x:Q, orb(c,x)] = {Q};   is TRAC1(LQnemp); 
LcorbR;                                is F1(Lcorb1);  // !! LQorb := A[x:Q, orb(f,x) = Q]; // F2 := R[x:Q, orb(c,x)] = {Q}; 
 end Proof LcorbR; 

! Lcorb2 := orbs.c = {Q} \/ R;                         // R := R[x:A--Q, orb(c,x)];
 EqProof Lcorb2;                                                             
F0 := orbs.c = R[x:dom(c), orb(c,x)];   is Torbs1.c;     by Lcdom;          // l! Torbs1 := orbs = R[x:dom(f), orb(f,x)];
F01 := orbs.c = R[x:A, orb(c,x)];                                           // ! Lcdom := dom(c) = A;  // ! LQA := Q <: A;
F02 := A = Q \/ (A--Q);                 is TInDU3a(LQA);                    // !! TInDU3a := X <: Y -> Y = X \/ (Y -- X);             
F1 := orbs.c;                           by F01;
F2 := R[x:A, orb(c,x)];                 by F02;                          
F3 := R[x: Q \/ (A--Q), orb(c,x)];      by TRU;                             // !! TRU := R[x: A\/B,F(x)] = R[x:A, F(x)] \/ R[x:B, F(x)];
F4 := R[x:Q, orb(c,x)] \/ R;            by LcorbR;                          // ! LcorbR := R[x:Q, orb(c,x)] = {Q};
F5 := {Q} \/ R;                                                             // R := R[x:A--Q, orb(c,x)]
 end EqProof Lcorb2;

! LcorbQc := Q in orbs.c;              by Lcorb2; is TUS1;                  // !! TUS1 := X in {X} \/ Y;// c := corb(Q);  
// !! Lcorb3 := R <: torbs.c;            see LR1;

! LcorbU := orbs.c = ntorbs.c \/ torbs.c; is Lorbs.c;                       // !! Lorbs := orbs = ntorbs \/ torbs; // 
! LcorbNI := ntorbs.c NI torbs.c;      is LorbsNItnt.c;                     // !! LorbsNItnt := ntorbs NI torbs;

! Lcorb4 := ntorbs.c <: {Q};
 Proof Lcorb4; 
F1 := ntorbs.c \/ torbs.c = {Q} \/ R;  is Axeq2a(LcorbU & Lcorb2);          // !! Axeq2a := a=x & a=y -> x=y;
F2 := ntorbs.c <: {Q};                 is TNI6a(LcorbNI & F1 & LR1);        // !! TNI6a := A NI B & A\/B = A1\/B1 & B1 <: B  -> A <: A1;
 end Proof Lcorb4;                                                          // x in A, x nin B, x nin B1, x in A\/B, x in A1\/B1, x in A1;

! Lcorb4a := ntorbs.(f||Q) <: {Q};     is Lcorb4;
    
! LcorbX := X in ntorbs.(f||Q) -> X=Q; // Proof(0;assume, 1: X in {Q}, is TinIn(0,Lcorb4a); 2: X=Q; is TinS(2)); // short proof;
 Proof LcorbX;
F0 := X in ntorbs.(f||Q);              assume;
F1 := X in {Q};                        is TinIn(F0 & Lcorb4a); by Axcoll1;  // !! Axcoll1 := All(x, All(a, x in {a} == x = a));
F2 := X=Q;
 end Proof LcorbX;

! Lcorb5 := A[Q:orbs.c, Q in ntorbs.c == atl2(Q)]; is Tntorbs.c;  // ! Tntorbs := A[Q_orbs, Q in ntorbs == atl2(Q)]; 
                     
! Lcorb6 := atl2(Q) == ntorbs.c = {Q};
 Proof Lcorb6;                         by Deqv; L1 & L2;          // ! Deqv := (p==q) == (p->q) & (q->p);  
L1 := atl2(Q) -> ntorbs.c = {Q};
  Proof L1;
F0 := atl2(Q);                         assume;                               
F02 := Q in ntorbs.c;                  by Lcorb5;   F0;           // ! Lcorb5 := A[Q:orbs.c, Q in ntorbs.c == atl2(Q)];             
F1 := ntorbs.c = {Q};                  is TSIn4b(Lcorb4 & F02);   // !! TSIn4b := X <: {a} & b in X -> X = {a};
  end Proof L1;
L2 := ntorbs.c = {Q} -> atl2(Q);
  Proof L2;
F0 := ntorbs.c = {Q};                  assume;
F01 := Q in ntorbs.c;                  by F0;  is TinS;           // ! TinS := a in {a}; 
F1 := atl2(Q);                         by -Lcorb5; F01;
  end Proof L2;
 end Proof Lcorb6;

! Lcorb6a := atl2(Q) == ntorbs.(f||Q) = {Q}; is Lcorb6;           // "scope:Q_orbs"; the parser has to cal


/* ! Lcorb4 := X in ntorbs.c -> X=Q;
 Proof Lcorb4;
F0 := X in ntorbs.c;                   assume; 
F01 := X in orbs.c;                    is TinIn(F0 & Lcntorbs);             // ! Lcntorbs := ntorbs.c <: orbs.c; ??? LntorbsIn.c            
F02 := A[X:orbs.c, X in ntorbs.c == atl2(X)]; is Tntorbs.c;                 // !! Tntorbs := A[Q_orbs, Q in ntorbs == atl2(Q)];
F03 := atl2(X);                        is F02(F0);
F04 := All(x, X ~= {x});               is Tatl2S(F03);                      // !! Tatl2S :=  atl2(X) -> All(x, X ~= {x});;
F01;   / * F01 := X in orbs.c; * /       by Lcorb2;                           // ! Lcorb2 := orbs.c = {Q} \/ R[x:A--Q, orb(c,x)];
F00 := X in {Q} \/ R[x:A--Q, orb(c,x)]; by AxU;                             // !! AxU := a1 in X1\/Y1 == a1 in X1 or a1 in Y1 ;
F1 := X in {Q} or X in R[x:A--Q, orb(c,x)];  
F2 := ~(X in R[x:A--Q, orb(c,x)]);     by TRinN;                            // !! TRinN := ~(a in R[d,g]) == A[d, a ~= g];
F3 := A[x:A--Q, X ~= orb(c,x)];        by LcorbS;
F4 := A[x:A--Q, X ~= {x}];             is F04;
F5 := X in {Q};                        is Taut((p or q) & ~q -> p)(F1 & F2); by Axcoll1;
F6 := X = Q;                                                                 // !! Axcoll1 := All(x, All(a, x in {a} == x = a)); 
 end Proof Lcorb4;
*/

// !! LcorbQ1 := #Q > 1 -> Q in ntorbs.c;                                 
// Proof LcorbQ1;         
// F0 := A[Q: orbs.c, Q in ntorbs.c == #Q > 1];  is Tntorbs.c;               // !! Tntorbs := A[Q_orbs, Q in ntorbs == atl2(Q)]; 
// F0 := #Q > 1;                          assume;         
// F2 := Q in ntorbs.c;
// end Proof LcorbQ1;

// dcl[atl2,set,bool];   // atl2(X): X has atleast 2 elements; (#X >= 2, but we have to prove that X is a finite set);
// !! Axatl2 := atl2(X) == E[a,b:X, a ~= b];

! LcorbQ1 := atl2(Q) -> Q in ntorbs.c;          // atl2(Q): Q has atleast 2 elements; (#Q > 1, but we have to prove that Q is a finite set);
 Proof LcorbQ1;                                 // ??? replace with Tntorbs.c ??? not used
F0 := A[X: orbs.c, X in ntorbs.c == atl2(X)];  is Tntorbs.c;               // !! Tntorbs := A[Q_orbs, Q in ntorbs == atl2(Q)]; 
F01 := atl2(Q);                        assume;         
F2 := Q in ntorbs.c;                   by F0; F01;
 end Proof LcorbQ1;
                                       // atl2(X): X has at least 2 elements; (#X >= 2, but we have to prove that X is a finite set);
! LQds2 := atl2(Q) == ds.c = Q;         // atl2(Q) == #Q > 1;  // atl2(X): X has at least 2 elements;  ???==
 EqProof LQds2;
F0 := A[Q: ntorbs.c, ntorbs.c={Q} == union(ntorbs.c)=Q]; is LntorbsSun.c;  // ! LntorbsSun := A[Q: ntorbs, ntorbs={Q} == union(ntorbs)=Q]; 
F1 := atl2(Q);                  by Lcorb6;                                 // !! Lcorb6 := atl2(Q) == ntorbs.c = {Q};
F2 := ntorbs.c = {Q};           by F0;
F3 := union(ntorbs.c) = Q;      by Lntorbsun.c;                            // ! Lntorbsun := union(ntorbs) = ds;    
F4 := ds.c = Q;
 end EqProof LQds2;

! LQds2a := atl2(Q) == ds.(f||Q) = Q;              is LQds2;               // dcl[atl2,fn(set,bool)];  // var Pf, fn(set,bool);
! LQds2b := atl2(ds.(f||Q)) == ds.(f||Q) = Q;      by Teq1; LQds2a;        // !! Teq1 := (Pf(a) == a=b) == (Pf(b) == a=b);

! Lcorbeqeq := A[Q1: ntorbs, (f||Q = f||Q1 == Q=Q1)];
 Proof Lcorbeqeq;
F0 := Q1 in ntorbs;             assume;  by Tntorbs; F02;  // !! Tntorbs := A[Q_orbs, Q in ntorbs == atl2(Q)];
F01 := f||Q1 in AFN;            is LcAFN.Q1;
F02 := atl2(Q1);                by LQds2a@Q_orbs;          // LQds2a := atl2(Q) == ds.(f||Q) = Q;
F03 := ds.(f||Q1) = Q1;          
G0 := f||Q = f||Q1 == Q=Q1;     by Deqv; L1 & L2;          // ! Deqv := (p==q) == (p->q) & (q->p);
                                                           // !! AxeqG := (G(x) = G(x1) == x=x1) == (G(x) = G(x1) -> x=x1) Teq5
L1 := f||Q = f||Q1 -> Q=Q1;
  Proof L1;
H0 := f||Q = f||Q1;             assume;
H1 := ds.(f||Q) = ds.(f||Q1);   byeq H0; by F03;
H2 := ds.(f||Q) = Q1;         
H3 := atl2(ds.(f||Q));          by H2; F02;
H4 := ds.(f||Q) = Q;            by -LQds2b@Q_orbs;  H3;    // ! LQds2b := atl2(ds.(f||Q)) == ds.(f||Q) = Q;
H5 := Q=Q1;                     by -H4; H2;  
  end Proof L1;

L2 := Q=Q1 -> f||Q = f||Q1;     is Axeqf;                  // !! Axeqf := a=b -> G(a)=G(b);
 end Proof Lcorbeqeq;

! Lcorbeqin := A[Q1:ntorbs, f||Q = f||Q1 -> Q in ntorbs];  // we are in Q_orbs := {Q; AxQ := Q in orbs};
 Proof Lcorbeqin;
F0 := Q1 in ntorbs;             assume;
F01 := f||Q = f||Q1;            assume; by Lcorbeqeq;      // ! Lcorbeqeq := A[Q1: ntorbs, (f||Q = f||Q1 
F1 := Q = Q1;
G0 := Q in ntorbs;              by F1; F0;
 end Proof Lcorbeqin; 

! Lcorb7 := E[Q1:ntorbs, f||Q = f||Q1] == Q in ntorbs;
 Proof Lcorb7;                         by Deqv;  L1 & L2;           // ! Deqv := (p==q) == (p->q) & (q->p);          
L1 := E[Q1:ntorbs, f||Q = f||Q1] -> Q in ntorbs;
  Proof L1;
F0 := Ex[Q1:ntorbs, F0a := f||Q = f||Q1]; assume;
F1 :=  Q in ntorbs;                    is  Lcorbeqin(F0a);          // ! Lcorbeqin := A[Q1:ntorbs, f||Q = f||Q1 == Q in ntorbs];
  end Proof L1;

L2 := Q in ntorbs -> E[Q1:ntorbs, f||Q = f||Q1 ];
  Proof L2;
F0 := Q in ntorbs;                     assume;
F01 := f||Q = f||Q;                    is Axrefl;                   // !! Axrefl := x=x; 
F1 := E[Q1:ntorbs, f||Q = f||Q1 ];     is Witness(Q);
  end Proof L2;
 end Proof Lcorb7;

! Lcorb8 := ntorbs.(f||Q) ~= {} == ntorbs.(f||Q) = {Q};                 // ! Deqv := (p==q) == (p->q) & (q->p);
 Proof Lcorb8;                                by Deqv; L1 & L2;         // ! Lcorb4a := ntorbs.(f||Q) <: {Q};
L1 := ntorbs.(f||Q) ~= {} -> ntorbs.(f||Q) = {Q};   is TSIn4a(Lcorb4a); // !! TSIn4a := X <: {a} -> X ~= {} -> X = {a};                      
L2 := ntorbs.(f||Q) = {Q} -> ntorbs.(f||Q) ~= {};   is TSeq4;           // !! TSeq4 := X={a} -> X ~= {}; 
 end Proof Lcorb8;

! Lcorb9 := ntorbs.(f||Q) ~= {} == atl2(Q);    byeq Lcorb8, -Lcorb6a;
                                                                                 // ! Lcorb4a := ntorbs.(f||Q) <: {Q};
! Lcorb10 := one(ntorbs.(f||Q)) == ntorbs.(f||Q) ~= {};  is TSIn4c(Lcorb4a);     // !! TSIn4c := X <: {a} -> one(X) == X ~= {};

! Lcorb11 := one(ntorbs.(f||Q)) == Q in ntorbs;  byeq Lcorb10,Lcorb9, -Tntorbs;  // ! Tntorbs := A[Q_orbs, Q in ntorbs == atl2(Q)];

]; // Q_orbs :: [   // 2

! Lcorbinj := A[Q,Q1: ntorbs, f||Q = f||Q1 == Q=Q1];  is Lcorbeqeq@Q_orbs;       // ! Lcorbeqeq := A[Q1: ntorbs, (f||Q = f||Q1 == Q=Q1)];

! LcorbafnA := A[Q_orbs, c in afn(A)];    is Lcafn@Q_orbs;               // Q_orbs :: ! Lcafn := c in afn(A); // c := f||A;
! Lcorb_typeA := A[Q_orbs, c in perm];    is Lc_type@Q_orbs;             // Q_orbs :: ! Lc_type := c in perm;  

Q_ntorbs := {Q; AxQ := Q in ntorbs};      // Q_orbs := {Q; AxQ := Q in orbs};  // was Q_ntorbs := Q_orbs && ( AxQnt := Q in ntorbs);
Q_ntorbs :: [                              
! L00 := Q in orbs;                       is TinIn(AxQ & LntorbsIn);     // ! LntorbsIn := ntorbs <: orbs; 
! L0 := Q in Q_orbs;                      by LQ_orbs; L00;               // ! LQ_orbs := Q_orbs = orbs;
! L01 := Q in P[dom(f)];                  by AxP; is LQdom.Q;            // Q_orbs :: ! LQdom := Q <: dom(f); // !! AxP := Z in P[Y] == Z <: Y; 
! L02 := f|Q in AFN;                      is LfQ_AFN.Q;                  // Q_orbs :: ! LfQ_AFN := f|Q in AFN;
! L03 := f||Q in AFN;                     is LcAFN.Q;                    // ! LcAFN := c in AFN;  // c := f||Q;
! L04 := atl2(Q);                         by -Tntorbs; AxQ;              // !! Tntorbs := A[Q_orbs, Q in ntorbs == atl2(Q)]; 
! L05 := ds.(f||Q) = Q;                   by -(LQds2a.Q); L04;           // ! LQds2a := atl2(Q) == ds.(f||Q) = Q;
! L06 := f||Q in perm;                    is Lc_type.Q;       // ! Lc_type := c in perm;  // ! Tperm := g in perm == g in AFN & dom(g) in finset1

! Lcorbds := f||Q = f == ds.f = Q;
 Proof Lcorbds;                           by Deqv; L1 & L2;              // ! Deqv := (p==q) == (p->q) & (q->p);
L1 := f||Q = f -> ds.f = Q;
  Proof L1;
K0 := f||Q = f;                           assume;
K1 := ds.f = ds.(f||Q);                   byeq -K0; by L05;
K2 := ds.f = Q;
  end Proof L1;
L2 := ds.f = Q -> f||Q = f;
  Proof L2;
K0 := f || ds.f = f;                      is Ldvlds(f,Q);                // !! Ldvlds := A[f_AFN_B_P, (f||ds.f) = f ];
K01 := ds.f = Q;                          assume;
K1 := f||Q = f;                           by -K01; K0;
  end Proof L2;
 end Proof Lcorbds;

]; // Q_ntorbs :: [

/*
! Lcorbds := A[Q_ntorbs, f||Q = f == ds.f = Q];
 Proof Lcorbds;
F0 := Q in ntorbs;                        assume;
G0 := f||Q = f == ds.f = Q;               by Deqv; L1 & L2;
L1 := f||Q = f -> ds.f = Q;//
  Proof L1;
K0 := f||Q = f;                           assume;
!! K01 := ds.(f||Q) = Q;
K1 := ds.f = ds.(f||Q);                   byeq -K0; by K01;
K2 := ds.f = Q;
  end Proof L1;
L2 := ds.f = Q -> f||Q = f;
  Proof L2;
!! K0 := f || ds.f = f;
K01 := ds.f = Q;                          assume;
K1 := f||Q = f;                           by -K01; K0;
  end Proof L2;
 end Proof Lcorbds;
*/
     // ??? A[Q_orbs, corb in perm];      is Lc_type@Q_orbs;     ??? was not caught!!! ??? 2022.12.04;

dsc := #ds + #ntorbs;                          //even(dsc(f)) == even(f); ??? n - #orbs ???
evenp := even(dsc);                            // evenp(f): f is an even permutation iff even(dsc(f)); // ab_A := {a,b; a in A, b in A};
                                              
!! T1 := A[ab_A, a ~= b -> evenp.(trp(a,b) o f) == ~(evenp.(f:perm))];    //  was evenp(trp(a,b) o f): ERROR (not function term);

// cycle := most1(ntorbs);                        // atm1: at most 1;  // #ntorbs <= 1;     // f is a cycle; // !!! change most1 to atm1;

ntrivcycle := one(ntorbs);                     // #ntorbs = 1;      // f is a nontrivial cycle;
! Tntrivcycle := ntrivcycle == one(ntorbs);    is Taut(p==p);

trivcycle := ntorbs = {};                      // #ntorbs = 0;      // f is a trivial cycle;
// ! Axtrivcycle := trivcycle == ntorbs={};       is Taut(p==p);
 
! Ltrivcycle := trivcycle -> f = id(dom(f));
 Proof Ltrivcycle;
F0 := trivcycle;                               assume; by -Lds4a;   // ! Lds4a := ds = {} == ntorbs = {};
F01 := ds = {};                                by LAFNdsid;         // !! LAFNdsid := ds={} == f = id(dom(f));
F1 :=  f = id(dom(f));
 end Proof Ltrivcycle;

! Lft := f in fn(A,A);                         is Tafnfn1(L00);  // !! Tafnfn1 := f in afn(A) -> f in fn(A,A); // ! L00 := f in afn(A);

cycles := R[Q_orbs, f||Q ];                                      
! L23 := cycles <: afn(A);             by TRA; LcorbafnA;         // !! TRA  := R[d, f] <: B == A[d, f in B]; // ! Lcafn := c in afn(A); 
! K7 := cycles <: AFN;                 is TInIn(L23 & L07);    // used in L3;  // ! L07 := afn(A) <: AFN;  // c := f||A;
! L25 := cycles in finset;             is TfinsetR(L7);           // !! TfinsetR := X in finset -> R[x:X, g] in finset; 
! L26 := cycles <: perm;               by TRA; Lcorb_typeA;       // ! L7 := orbs in finset; // ! Lcorb_typeA := A[Q_orbs, corb in perm];
! LcyclesFS := cycles in FS(afn(A));   is AxFS(L23 & L25);        // !! AxFS := X in FS(A) == X <: A & X in finset;
! L28 := cycles <: REL;                is TInIn(K7 & TAFNREL); // for type checking in Lcyclescomm; (+6sec if commented ???);    
                                       // ntcycles = im(cnt);  g in ntcycles -> g = f||Orb(g) 
ntcycles := R[Q_ntorbs, f||Q];         // im(cnt):nontrivial cycles;      // ! LntorbsIn := ntorbs <: orbs; // was R[Q_ntorbs, f||Q];  2023.01.06  
! L10 := ntcycles <: cycles;           is TRmon(LntorbsIn);       // !! TRmon := A <: B -> R[x:A, G(x)] <: R[x:B, G(x)]; 
! L11 := ntcycles <: perm;             is TInIn(L10 & L26);    // ! TInIn := X0 <: Y0 & Y0 <: Z0 -> X0 <: Z0;
 // !! TRin := z in R[d,f] == E[d, z = f];
                                       // !! TFinj1 := injective(FAGx) == A[x1,x2:A, G(x1)=G(x2) == x1=x2]; // FAGx := F[x:A, G(x)];
cnt := corb|ntorbs;                    // the cycle for a nontrivial orbit;  // ! LntorbsIn := ntorbs <: orbs;             
! Lcnt0 := cnt = F[Q_ntorbs, f||Q];    is TFre(LntorbsIn);        // !! TFre := B <: A -> F[x:A, G(x)] | B = F[x:B, G(x)];
                                       // fA := {f, A; f in FN, A in set, AxfA1 := A <: dom(f) }; // ! Lcorb12: for Timre(corb,ntorbs); 
! Lcntinj := injective(cnt);           by Lcnt0, TFinj1; is Lcorbinj; // ! Lcorbinj := A[Q,Q1: ntorbs, f||Q = f||Q1 == Q=Q1]; 
! Lcorb12 := ntorbs <: dom(corb);      by Lcorbdom; is LntorbsIn;     // ! Lcorbdom := dom(corb) = orbs;  // ! Lcorb := A[Q_orbs, corb(Q) = f||Q];
! Lcntdom := dom(cnt) = ntorbs;        is Tredom(corb,ntorbs);             // fA :: !! Tredom := dom(f|A) = A; 
! Lcntim := im(cnt) = ntcycles;        byeq Timre(corb,ntorbs), Lcorb;     // fA :: !! Timre := im(f|A) = R[x:A, f(x)]; 
! Lcntfn := cnt in fn(ntorbs,ntcycles); by -Lcntdom,2, -Lcntim; is Tfndomim.cnt; // FN :: !! Tfndomim := f in fn(dom(f), im(f)); 
! Lcntbfn := cnt in bfn(ntorbs,ntcycles); by Tbfnin1;  Lcntfn & Lcntinj & Lcntim; 
                                       // !! Tbfnin1 := f in bfn(A,B) == f in fn(A,B) & injective(f) & im(f) = B; 
Orb := inv(cnt);                       // the orbit for a nontrivial cycle;
! LOrb := Orb in bfn(ntcycles,ntorbs); is Tbfninv(Lcntbfn);                // !! Tbfninv := f in bfn(A,B) -> inv(f) in bfn(B,A);
! LOrb1 := A[g1,g2: ntcycles, Orb(g1)=Orb(g2) == g1=g2]; is TbfnA(LOrb);   // !! TbfnA := f in bfn(A,B) -> A[x1,x2:A, f(x1)=f(x2) == x1=x2];

! LOrb2 := A[Q_ntorbs, Orb(f||Q) = Q];
 Proof LOrb2;
F0 := Q in ntorbs;                     assume;
F1 := cnt(Q) = f||Q;                   byeq Lcnt0, Red("F");                    // too complex ???          
F2 := Orb(f||Q) = Q;                   by -F1; is Tbfninv4(Lcntbfn & F0);  // !! Tbfninv4 := f in bfn(A,B) & x in A -> inv(f)(f(x)) = x;
 end Proof LOrb2;

! LOrb3 := A[g:ntcycles, ntorbs.g = {Orb(g)} ];
 Proof LOrb3;                                                              // ntcycles := R[Q_ntorbs, f||Q];
F0 := g in ntcycles;                   assume; by TRin;                    // !! TRin := z in R[d,f] == E[d, z = f];
F01 := Ex[Q_ntorbs, F01a := g = f||Q];                                     // Q_orbs :: ! Lcorb6a := atl2(Q) == ntorbs.(f||Q) = {Q}; 
F1 := atl2(Q);                         is Tntorbs(Q in ntorbs); by Lcorb6a.Q; // ! Tntorbs := A[Q_orbs, Q in ntorbs == atl2(Q)];
F2 := ntorbs.(f||Q) = {Q};             by -F01a;
F3 := ntorbs.g = {Q};                  by -LOrb2; // -,F01a: did not work, y because Q is also in ntorbs and g; (the cause was Q@Q_orbs in ntorbs);
F4 := ntorbs.g = {Orb(f||Q)};          by -F01a;  // ??? Is it legal for rep2i to search for Q in ntorbs in the dot term ntorbs.g 2023.01.22 ???
F5 := ntorbs.g = {Orb(g)};
 end Proof LOrb3;

cycle := perm && (Axcycle :=  most1(ntorbs) ); 
! LcycleIn1 := cycle <: perm;         is LdconjIn;                          // !! LdconjIn := d&&P <: d;   // LpremREL := perm <: REL;
! LcycleIn2 := cycle <: REL;          is TInIn(LcycleIn1 & LpermREL);    // ! TInIn := X0 <: Y0 & Y0 <: Z0 -> X0 <: Z0; 

// !! Lcycledom := g in cycle -> dom(g) = dom(f);   // ??? WRONG ???        // !! Tafndom := A[f: afn(A), dom(f) = A];   

cycle :: [                            // ntrivcycle := one(ntorbs);         // trivcycle := ntorbs = {};
! Lntrivcycle := ntrivcycle == ~trivcycle;      is Tatm1a(Axcycle);         // !! Tatm1a := most1(X) -> one(X) == ~(X=={})
! Ltrivntor := trivcycle or ntrivcycle;         is Tatm1or(Axcycle);        // !! Tatm1or := most1(X) -> (X={} or one(X));
// !! Lntcycles := f in ntcycles == ntrivcycle.f; 
]; // cycle :: [

! Lntcycles := A[g:cycles, g in ntcycles == ntrivcycle.g];        // ntrivcycle := one(ntorbs);   
 EqProof Lntcycles;
F0 := g in cycles;                     assume; by TRin;           // cycles := R[Q_orbs, f||Q ];
F01 :=  Ex[Q:orbs, F01a := g = f||Q ]; 
F02 := f||Q in perm;                   is Lc_type@Q_orbs;         // Q_orbs :: ! Lc_type := c in perm; // c := f||Q;
F03 :=  ntrivcycle.g == one(ntorbs.g); is Tntrivcycle.g;          // ! Tntrivcycle := ntrivcycle == one(ntorbs);
F1 := g in ntcycles;                   by F01a;                   // F01a := g = f||Q
F2 := f||Q in ntcycles;                by TRin;                   // !! TRin := z in R[d,f] == E[d, z = f]; 
F3 := E[Q1:ntorbs, f||Q = f||Q1 ];     by Lcorb7@Q_orbs;          // Q_orbs :: Lcorb7 := E[Q1:ntorbs, f||Q = f||Q1 ] == Q in ntorbs;
F4 := Q in ntorbs;                     by -(Lcorb11@Q_orbs);      // ! Lcorb11 := one(ntorbs.(f||Q)) == Q in ntorbs;
F5 := one(ntorbs.(f||Q));              by -F01a;                  // F01a := g = f||Q
F6 := one(ntorbs.g);                   by -F03;
F7 := ntrivcycle.g;
 end EqProof Lntcycles;

/*
g_cycles := {g; Axg := g in cycles};
g_cycles :: [ Axg;                     by TRin;
! LcyclesQ := Ex[Q:orbs, Axg1 := g = f||Q ];  // Existx(Q, (AxQ1 := Q in orbs) & (Axg1 := g = f||Q) );
! LcyclesQin := Q in orbs;              is true;                  // Q:orbs => Q in orbs';
! LcyclesfQ := f||Q in perm;            is Lcorb_typeA;           // ! Lcorb_typeA := A[Q_orbs, c in perm];
! LcyclesX := X in ntorbs.g -> atl2(X); is LntorbsX1.g;           // ! LntorbsX1 := X in ntorbs -> atl2(X); 
// ! LOrb1 :=  ntorbs.g = {Orb(g)};     // atm1(Q)
   
! Lcycles1 := ntorbs.g <: ntorbs;                                 // "]" was not caught; ???
 Proof Lcycles1;                       by TInA;                   // ! TInA := A <: B == A[x:A, x in B]; 
L0 := A[X: ntorbs.g, X in  ntorbs];
  Proof L0;
// F0 := f||Q in perm;                    
F0 := X in ntorbs.g;                   assume;  by Axg1;
F1 := X in ntorbs.(f||Q);              // ntorbs.(f||Q) = {Q},  
F2 := X = Q;                           is LcorbX@Q_orbs(F1);         // ! LcorbX := X in ntorbs.(f||Q) -> X=Q;  
F3 := atl2(X);                         is LcyclesX(F0);              // ! LcyclesX := X in ntorbs.g -> atl2(X); 
F4 := atl2(Q);                         by -F2; F3;
F5 := Q in ntorbs;                     by LntorbsX; Q in orbs & F4;  // ! LntorbsX := X in ntorbs == X in orbs & atl2(X); 
F6 := X in  ntorbs;                    by F2; F5;
  end Proof L0;
 end Proof Lcycles1;

// !! Lcycles2 := ntorbs.g ~= {} == one(ntorbs.g);    // !! Lcycles2a := ntorbs.(f||} ~= {} == one(ntorbs.(f||Q);

// Q_ntorbs := {Q; AxQ := Q in ntorbs};                           // ! Lcorb6a := atl2(Q) == ntorbs.(f||Q) = {Q};
                                                                  // ! LcorbQ1 := atl2(Q) -> Q in ntorbs.c; 
// ! Lntcycles := A[g_cycles, g in ntcycles == ntrivcycle.g];     // A[g:cycles.f, g in ntcycles.f == ntrivcycle.g];

! Lntcycles := g in ntcycles == ntrivcycle.g;                     // ntrivcycle := one(ntorbs);   
EqProof Lntcycles;
!! F0 := one(ntorbs.g) == ntrivcycle.g;
F1 := g in ntcycles;                   by Axg1;                   // Axg1 := g = f||Q
F2 := f||Q in ntcycles;                by TRin;                   // !! TRin := z in R[d,f] == E[d, z = f]; 
F3 := E[Q1:ntorbs, f||Q = f||Q1 ];     by Lcorb7@Q_orbs;          // Q_orbs :: Lcorb7 := E[Q1:ntorbs, f||Q = f||Q1 ] == Q in ntorbs;
F4 := Q in ntorbs;                     by -(Lcorb11@Q_orbs);      // !! Lcorb11 := one(ntorbs(f||Q)) == Q in ntorbs;
F5 := one(ntorbs.(f||Q));              by -Axg1;                  // Axg1 := g = f||Q
F6 := one(ntorbs.g);                   by F0;
F7 := ntrivcycle.g;
 end EqProof Lntcycles;

!! Lcycle_triv_nt := trivcycle.g or ntrivcycle.g;    // trivcycle := ntorbs = {}; // ntrivcycle := one(ntorbs);
!! Lntrivcycle := ntrivcycle.g == ~trivcycle.g;      // is Tatm1a(cycle);   // !! Tatm1a := most1(X) -> one(X) == ~(X=={})

]; // g_cycles :: [


! Lcyclesnt0 := A[g1,g2:cycle, dom(g1)=dom(g2) -> (ntorbs.g1=ntorbs.g2 -> g1=g2)]; // if g1,g2: cycles then 
 Proof Lcyclesnt0;
F01 := g1 in cycle;                    assume;
// F01a := dom(g1) = dom(f);              is Lcycledom(F01);               // !! Lcycledom := g in cycle -> dom(g) = dom(f); ??? WRONG ???
F02 := g2 in cycle;                    assume;                    
// F02a := dom(g2) = dom(f);              is Lcycledom(F02); 
F04 := dom(g1) = dom(g2);              assume;
F03 := ntorbs.g1=ntorbs.g2;            assume;
// F04 := dom(g1) = dom(g2);              is Axeq2(F01a & F02a);               // !! Axeq2 := x=a & y=a -> x=y;
F1 := trivcycle.g1 or ntrivcycle.g1;   is Ltrivntor.g1;                     // ! Ltrivntor := trivcycle or ntrivcycle;
G0 := g1=g2;                           by Case2(F1); L1 & L2;               // ! Lntrivcycle := ntrivcycle == ~trivcycle;
L1 := trivcycle.g1 -> G0;
  Proof L1;
H0 := trivcycle.g1;                    assume;                    // trivcycle := ntorbs = {};            
H01 := g1 = id(dom(g1));               is Ltrivcycle.g1(H0);      // ! Ltrivcycle := trivcycle -> f = id(A); 
H02 := ntorbs.g1 = {};                 is H0;  by F03;               
H1 := ntorbs.g2 = {};
H2 := g2 = id(dom(g2));                is Ltrivcycle.g2(H1); 
H3 := g1=g2;                           byeq H01,F04,-H2;
  end Proof L1;
L2 := ntrivcycle.g1 -> G0;             // G0 := g1=g2;
  Proof L2;
H0 := ntrivcycle.g1;                   assume;                    // ntrivcycle := one(ntorbs);
H00 := one(ntorbs); 
!! H01 := g1 in ntcycles;
!! H02 := g2 in ntcycles;
H1 := ntorbs.g1 = {Orb(g1)};           is LOrb3;                  // !! LOrb3 := A[g:ntcycles, ntorbs.g = {Orb(g)};
H2 := ntorbs.g2 = {Orb(g2)};           is LOrb3;   
H3 := {Orb(g1)} = {Orb(g2)};           is Axeq3a(H1 & H2 & F03);  // !! Axeq3a := x=a1 & y=a2 & x=y -> a1=a2;
H4 := Orb(g1) = Orb(g2);               by -TSeq2a; H3;            // ! TSeq2a := {a} = {b} == a = b;
H5 := g1=g2;                           by -(TbfnA(LOrb)); H4;     // !! TbfnA := f in bfn(A,B) -> A[x1,x2:A, f(x1)=f(x2) == x1=x2];
  end Proof L2;                                                   // ! LOrb := Orb in bfn(ntcycles,ntorbs);
 end Proof Lcyclesnt0;
*/

! Lcyclesnt:= A[g1,g2:cycles, ntorbs.g1=ntorbs.g2 -> g1=g2];

!! LntcyclesInAFN := ntcycles <: AFN;

NN1_ntc := {N,N1; Ax0 := N in ntcycles, Ax1 := N1 in ntcycles};
NN1_ntc :: [
! L29 := N in perm;                    is TinIn(Ax0 & L11);       
! L30 := N1 in perm;                   is TinIn(Ax1 & L11); 
]; // NN1_ntc :: [

!! L12 := A[NN1_ntc, L9_type := N o N1 in perm];
!! Lntc1 := A[NN1_ntc, ds(N o N1) = ds(N:perm) \/ ds(N1:perm)];   // ds := {x: A; f(x) ~= x};
!! Lntc2 := U[N:ntcycles, ds.N] = ds.f;                           // was ds(N:perm)] = ds(f:perm);
!! Lntc3 := A[NN1_ntc, N~=N1 == ds.N NI ds.N1];          // ds(N) NI ds(N1);
                                                         // !! TAFNREL := AFN <: REL;                       
! Lcyclescomm := A[g1,g2:cycles, g1 o g2 = g2 o g1];
 Proof Lcyclescomm;
K0 := g1 in cycles;                     assume;
!! K0a := g1 in cycle;
K1 := g1 in afn(A);                     is TinIn(K0 & L23);  // ! L23 := cycles <: afn(A);  
K2 := g2 in cycles;                     assume;
!! K2a :=  g2 in cycle;
K3 := g2 in afn(A);                     is TinIn(K2 & L23);
K4 := A[f: afn(A), f o id(A) = f];      is Tafn4;            // !! Tafn4 := A[f: afn(A), f o id(A) = f]; // different A's;
K4a := A[f: afn(A), id(A) o f = f];     is Tafn4a;           // !! Tafn4a := A[f: afn(A), id(A) o f = f];
K5 := dom(g1) = A;                      is Tafndom1(K1);     // !! Tafndom1 := f in afn(A)-> dom(f) = A; 
K6 := dom(g2) = A;                      is Tafndom1(K3);     // Axneq := z ~= z1 == ~(z = z1);  
K8 := ntrivcycle.g1 == ~(trivcycle.g1); is Lntrivcycle.g1;   // ! Lntrivcycle := ~(ntrivcycle) == trivcycle;
K9 := ntrivcycle.g2 == ~(trivcycle.g2); is Lntrivcycle.g2;

Lcase := g1=g2 or trivcycle.g1 or trivcycle.g2 or g1 ~= g2 & ntrivcycle.g1 & ntrivcycle.g2; by Axneq,K8,K9; 
                                        is Taut(p or q or r or (~p)&(~q)&(~r));       
G0 := g1 o g2 = g2 o g1;                by Case4(Lcase);   L0 & L1 & L2 & L3;

! L0 := g1=g2 -> G0;
  Proof L0;
F0 := g1=g2;                            assume;
G0;                                     by F0;
F1 := g2 o g2 = g2 o g2;                is Axrefl;            // !! Axrefl := x = x;  
  end Proof L0;
L1 := trivcycle.g1 -> G0;
  Proof L1;
F0 := trivcycle.g1;                     assume;
F00 := trivcycle.g1 -> g1 = id(dom(g1)); is Ltrivcycle.g1;      // !! Ltrivcycle := trivcycle -> f = id(A); // A := dom(f);
F01 := g1 = id(dom(g1));                 is F00(F0);  by K5;  
F01a := g1 = id(A);
F02 := g1 o g2 = g2;                      by F01a; is K4a;      // !! K4a := A[f: afn(A), id(A) o f = f];
F03 := g2 o g1 = g2;                      by F01a; is K4;       // !! K4 := A[f: afn(A), f o id(A) = f]; 
F1 := g1 o g2 = g2 o g1;                  is Axeq2(F02 & F03);  // !! Axeq2 := x=a & y=a -> x=y;             
  end Proof L1;

L2 := trivcycle.g2 -> G0;
  Proof L2;
F0 := trivcycle.g2;                      assume;
F00 := trivcycle.g2 -> g2 = id(dom(g2)); is Ltrivcycle.g2;      // !! Ltrivcycle := trivcycle -> f = id(A); // A := dom(f);
F01 := g2 = id(dom(g2));                 is F00(F0);  by K6;
F01a := g2 = id(A);
F02 := g1 o g2 = g1;                     by F01a; is K4;       // !! Tafn4 := A[f: afn(A), f o id(A) = f]; 
F03 := g2 o g1 = g1;                     by F01a; is K4a;      // !! Tafn4a := A[f: afn(A), id(A) o f = f];
F1 := g1 o g2 = g2 o g1;                 is Axeq2(F02 & F03);  // !! Axeq2 := x=a & y=a -> x=y;             
  end Proof L2;

L3 := g1 ~= g2 & ntrivcycle.g1 & ntrivcycle.g2 -> G0;
  Proof L3;
F0 := g1 ~= g2;                          assume;
F01 := ntrivcycle.g1;                    assume;  by -(Lntcycles(g1)); // !! Lntcycles := A[g:cycles, g in ntcycles == ntrivcycle.g];  
F01a := g1 in ntcycles;
F02 := ntrivcycle.g2;                    assume;  by -(Lntcycles(g2));
F02a := g2 in ntcycles;
F1 := ds.g1 NI ds.g2;                    is Lntc3(F0);           // !! Lntc3 := A[NN1_ntc, N~=N1 == ds.N NI ds.N1];
F2 := g1 o g2 = g2 o g1;                 is Tafncomm(K1 & K3 & F1); // !! Tafncomm := f in afn(A) & g in afn(A) & ds.f NI ds.g -> f o g = g o f;
  end Proof L3;
 end Proof Lcyclescomm;
                                       // fcs := {C; AxC1 := C in FS(elg); AxC2 := A[x,y: C, x*y = y*x] };
! LSymA_type := Sym(A) in group;       is TSym(A);                // finset1 :: Sym := [afn(A), compA]; // finset1 :: ! TSym := Sym in group;
!! LfcsSymA := fcs.(Sym(A)) = {C; C in FS(afn(A)); A[f,g:C, f o g = g o f] }; // byeq Red("dot"); 
! Lcyclesfcs := cycles in fcs.(Sym(A));       by LfcsSymA, Axab; LcyclesFS & Lcyclescomm;

comp := Pset.(Sym(A));
!! Lcomp_type := comp in fn(fcs.(Sym(A)), A);        // Ax1 := Pset in fn(fcs,elg)

cc := comp(cycles);                            // composition
!! Lcc_type := cc in afn(A);
!! Lccdom := dom(cc) = A;

!! T2 := f = cc;                               // !! Tfneq := A[f,g: FN, f=g == dom(f)=dom(g) & A[x:dom(f), f(x)=g(x)]];
/* Proof T2;                                     by Tfneq; L1 & L2;  
L1 := dom(f) = dom(cc);                        byeq Lccdom;
L2 := A[x:A, f(x) = cc(x)];
  Proof L2;
F0 := x in A;                                  assume;
qx := orb(f,x);
F1 := x in qx;                                 is Lorb2(f,x);  perma :: !! Lorb2 := a in orb;
zx := corb(qx);
F2 := f(x) = zx(x);                            is ???
C1 := cycles - {zx};
Q1 := orbs(f) - {qx};
F3 := A[q1:Q1, x nin q1];                      is ???
F4 := cc = zx o comp(C1);                      is Tcompx ???
F5 := A[z:C1, z(x) = x];                       is Lx;
F6 := comp(C1)(x) = x;                         is Tcompx1; ???
F7 := cc(x) = (zx o comp(C1))(x);              by 
F8 := cc(x) = zx(comp(C1)(x));                 by F6, -F2, Axsym;   // Axsym := u=v == v=u; 
F9 := f(x) = cc(x);
//  end Proof L2;s
// end Proof T2;
*/ ///////////////////////correct

! Lcff := seqinj1(A) <: SEQinj1;               is Lseqinj1In;        // !! Lseqinj1In := seqinj1(A) <: SEQinj1;
cf := F[z:seqinj1(A), F[x:A, if(x in im(z), nextf.z(x):A, x)] ];     "nosimr";
! Lcf_type := cf in fn(seqinj1(A), afn(A));  is Lnextf9;
               // !! Lnextf9 := F[z:seqinj1(A), F[x:A, if(x in im(z), nextf.z(x):A, x)] ] in fn(seqinj1(A), afn(A));  
! Lcf0 := A[x_A, [x] in seqinj1(A)];  is Lseqinj8;  //  !! Lseqinj8 := A[a:A, [a] in seqinj1(A)];
! Lcf1 := A[x_A, [x] in SEQinj1];     is LSEQinj1b; //  !! LSEQinj1b := [x] in SEQinj1;
// ! Lcf2 := A[x_A, im([x]) = {x}];      is LSEQ1im;   //  !! LSEQ1im := im([x]) = {x};
// ! Lcf3 := A[x_A, x in im([x]) ];      is LSEQim1;   //  !! LSEQim1 :=  x in im([x]);
// ! Lcf4:= A[x_A, nextf.[x](x) = x];    is Lnextf10;  //  !! Lnextf10 := nextf.[x](x) = x;

! Lcfid := A[x_A, cf([x]) = id(A)]; 
 EqProof Lcfid;
F0 := x in A;                                    assume;
F01 := a in im([x]) -> nextf.[x](a) = a;         is Lnextf11;     // !! Lnextf11 := a in im([x]) -> nextf.[x](a) = a;  
F1 := cf([x]);                                   by Red("F");
F2 := F[a:A, if(a in im([x]), nextf.[x](a), a)]; by Tif4(F01);    // !! Tif4 := (p -> a=c) -> if(p,a,b) = if(p,c,b); 
F3 := F[a:A, if(a in im([x]), a, a)];            by Tif3;         // !! Tif3 := if(p,a,a) = a;
F4 := F[a:A, a];                                 by -TidF;        // !! TidF := id(A) = F[x:A, x]; 
F5 := id(A);
 end EqProof Lcfid;

aCD := {a,C,D; Axa := a in A; AxC := C in seqinj(A); AxD := D in seqinj(A); AxaC := a nin im(C); AxaD := a nin im(D); AxCD := im(C) NI im(D)};
aCD :: [
// ! L1a := seqinj(A) <: seq(A);        is Lseqinj3;                 // !! Lseqinj3 := seqinj(A) <: seq(A);   // different A's;
! L1 := C in seq(A);                 is TInin(Lseqinj3 & AxC);    // is TInin(L1a & AxC);     
! L2 := D in seq(A);                 is TInin(Lseqinj3 & AxD);         // !! TInin := X <: Y & x in X -> x in Y;
! LCim := im(C) <: A;                is Tseqim(L1);               // !! Tseqim := z in seq(A) -> im(z) <: A;
! LDim := im(D) <: A;                is Tseqim(L2);   
! L1C := C ~= [] -> C in SEQinj1;    is Lseqinj4(AxC);            // !! Lseqinj4 := z in seqinj(A) -> (z ~= [] -> z in SEQinj1);
! L1D := D ~= [] -> D in SEQinj1;    is Lseqinj4(AxD);            // !! L1 := seqinj1(A) <: SEQinj1;
! L2C := C ~= [] -> C in SEQ1;       is Lseq4(L1);                // !! Lseq4 := z in seq(A) -> (z ~= [] -> z in SEQ1);               
! L2D := D ~= [] -> D in SEQ1;       is Lseq4(L2); 
! L3C := C ~= [] -> 0 in dom(C);     is Lseq5(L1);                // !! Lseq5 := z in seq(A) -> (z ~= [] -> 0 in dom(z));
! L3D := D ~= [] -> 0 in dom(D);     is Lseq5(L2);                
! L4C := [a]^C in SEQinj1;           is Lseqinj6(AxC & AxaC);     // !! Lseqinj6 := z in seqinj(A) & a nin im(z) -> [a]^z in SEQinj1;
! L4D := [a]^D in SEQinj1;           is Lseqinj6(AxD & AxaD); 
// !! L5 := C ~= [] & x in im(C-) -> x in A;                      // !! TSEQinj1t := SEQinj1 <: SEQ1;
// !! L6 := C ~=[] -> im(C-) <: im(C);
! L7 := C ~=[] -> Last(C) in A;      is Lseq6(L1);                 // !! Lseq6 := z in seq(A) -> (z ~= [] -> Last(z) in A);
! L8 := D ~=[] -> Last(D) in A;      is Lseq6(L2);                
! LaC := [a]^C in seqinj1(A);        is Lseqinj5(AxC & AxaC);      // !! Lseqinj5 := z in seqinj(A) & a nin im(z) -> [a]^z in seqinj1(A);
! L10 := [a]^C in seq(A);            is TInin(Lseqinj3a & LaC);    // !! Lseqinj3a := seqinj1(A) <: seq(A);
! LaCim := im([a]^C) <: A;           is Tseqim(L10);
! LaD := [a]^D in seqinj1(A);        is Lseqinj5(AxD & AxaD); 
! L11 := [a]^D in seq(A);            is TInin(Lseqinj3a & LaD); 
! LaDim := im([a]^D) <: A;           is Tseqim(L11);               // !! Tseqim := z in seq(A) -> im(z) <: A;
! L12 := im(D) NI im(C);             by TNIsym; AxCD;              // ! TNIsym := X NI Y == Y NI X; 

saDC := [a]^D^C;                     // !! Lseqconc :=  y in seq(t) & z in seq(t) -> y^z in seq(t)]; 
! L3 := saDC in seq(A);              is Lseqconc(L11 & L1);        // ! L11 := [a]^D in seq(A); // ! L1 := C in seq(A); 
! LaDCim := im(saDC) <: A;           is Tseqim(L3);                // !! Tseqim := z in seq(A) -> im(z) <: A;
! LaDC := saDC in seqinj1(A);       is Lseqinj7(Axa & AxD & AxC & AxaD & AxaC & L12);   
              // Lseqinj7 := a in A & y in seqinj(A) & z in seqinj(A) & a nin im(y) & a nin im(z) & im(y) NI im (z) -> [a]^y^z in seqinj1(A);
! L5 := saDC in SEQinj1;             is TInin(Lseqinj1In & LaDC);  // !! Lseqinj1In := seqinj1(A) <: SEQinj1;
M := [[a],D,C];                      // uyz := {u,y,z; u in SEQ, y in SEQ, z in SEQ; Ax1 := u^y^z in SEQinj1; };
! L0a := [a] in SEQ;                 is LSEQ0;                     // !! LSEQ0 := All(x, [x] in SEQ);
! L0C := C in SEQ;                   is Lseq0a(L1);                // !! Lseq0a := x in seq(t) -> x in SEQ; // ! L1 := C in seq(A); 
! L0D := D in SEQ;                   is Lseq0a(L2);                // ! L2 := D in seq(A); 
! L5_type := M in uyz;               by Axab; L0a & L0D & L0C & L5;
! L9 := im(C) <: im(saDC);           is L1.M;                      // !! L1 := im(z) <: im(u^y^z); 
! L9a := im(D) <: im(saDC);          is L4.M;                      // !! L4 := im(y) <: im(u^y^z);   
! LinimC := x in im(C) -> ~(x in im([a]^D));         is L9.M;      // !! L9 := x in im(z) -> ~(x in im(u^y));
! LinimD := x in im(D) -> ~(x in im([a]^C));         is L10.M;     // !! L10 := x in im(y) -> ~(x in im(u^z));
! LD0imaC :=  D ~= [] -> ~(D(0) in im([a]^C));       is L11.M;     // !! L11 :=  y ~= [] -> ~(y(0) in im(u^z)); 
! L5C := x ~= a & x nin im(C) -> ~(x in im([a]^C));  by Axneq,Axnin,Lconcim4; is Taut;             // !! Axneq := z ~= z1 == ~(z = z1); 
! L5D := x ~= a & x nin im(D) -> ~(x in im([a]^D));  by Axneq,Axnin,Lconcim4; is Taut;             // !! Axnin := x nin X == ~(x in X); 
! L6 := x ~= a & x nin im(D) & x nin im(C) -> ~(x in im([a]^D^C)); by Axneq, Axnin,Axnin,Lconcim5; is Taut;
  // !! Lconcim4 := A[z:SEQ, x in im([a]^z) == x=a or x in im(z)]; // !! Lconcim5 := A[y,z:SEQ, x in im([a]^y^z) == x=a or x in im(y) or x in im(z)];
aC := cf([a]^C);
! LaC0 := aC = F[x:A, if(x in im([a]^C), nextf.([a]^C)(x):A, x)];  byeq Red("F");
! LaC_type := aC in afn(A);        is typeaxiom;
! LdomaC := dom(aC) = A;           is Tafndom1(LaC_type);

! LaC1 := C = [] -> aC = id(A);
 EqProof LaC1;
F0 := C = [];                      assume;
F01 := [a]^C = [a];                by F0; is Lconcempl;            // is !! Lconcempl := A[z:SEQ, z^[] = z];
aC;                                by F01;                         // aC := cf([a]^C);
F2 := cf([a]);                     by Lcfid;                       // !! Lcfid := A[x_A, cf([x]) = id(A)]; 
F3 := id(A);
 end EqProof LaC1;

! L4 := im(C) <: im([a]^C);       is LconcimIn@dyz;                // dyz :: !! LconcimIn := im(z) <: im(y^z);

! LaC2 := x in im([a]^C) -> aC(x) = nextf.([a]^C)(x);
 EqProof LaC2;
F0 := x in im([a]^C);             assume; 
F01 := x in A;                    is TinIn(F0 & LaCim);            // ! LaCim := im([a]^C) <: A; 
F1 := aC(x);                      by LaC0, Red("F");
F2 := if(x in im([a]^C), nextf.([a]^C)(x):A, x);   by Tif1(F0);    // !! Tif1 := p -> if(p,a,b) = a;
F3 := nextf.([a]^C)(x);
 end EqProof LaC2;

! LaC3 := x in A & ~(x in im([a]^C)) -> aC(x) = x;
 EqProof LaC3;
F0 := x in A;                     assume;
F01 := ~(x in im([a]^C));         assume; 
F1 := aC(x);                      by LaC0, Red("F");           // ! LaC0 := aC = F[x:A, if(x in im([a]^C), nextf.([a]^C)(x):A, x)];
F2 := if(x in im([a]^C), nextf.([a]^C)(x), x);   by Tif2(F01); // !! Tif2 := ~p -> if(p,a,b) = b;   // :A : error, 2022.10.03;
F3 := x;
 end EqProof LaC3;

! LaCa := C ~= [] -> aC(a) = C(0);
 EqProof LaCa;
F0 := C ~= [];                    assume;
F01 := a in im([a]^C);            is Lconcim3;              // !! Lconcim3 := A[z:SEQ, x in im([x]^z)];
F02 := C in SEQ1;                 is L2C(F0);               // ! L2C := C ~= [] -> C in SEQ1;
F1 := aC(a);                      by  LaC2(F01);            // ! LaC0 := aC = F[x:A, if(x in im([a]^C), nextf.([a]^C)(x):A, x)];  byeq Red("F");  
F2 := nextf.([a]^C)(a);           by Lnextf5(L4C);          // !! Lnextf5 := A[x:any, z:SEQ1, [x]^z in SEQinj1 -> nextf.([x]^z)(x)) = z(0)];
F3 := C(0);                                                 // ! L4C := [a]^C in SEQinj1;
 end EqProof LaCa;

! LaCim1 := C ~= [] & x in im(C) & x ~= Last(C) -> aC(x) = nextf.C(x);      // x in im(C) -> C ~= [];
 Proof LaCim1;                    // SUCCESS! main: grand total time= 91.837
F0 := C ~= [];                    assume;
F01 := x in im(C);                assume;                   // dyz := {y,z; y in SEQ; z in SEQ; };       
F02 := im(C) <: im([a]^C);        is LconcimIn@dyz;         // dyz :: !! LconcimIn := im(z) <: im(y^z);
F03 := x in im([a]^C);            is TinIn(F01 & F02);      // ! TinIn := x2 in X2 & X2 <: Y2 -> x2 in Y2;
F04 := x ~= Last(C);              assume;                   // dyz2 := dyz && (Ax1 := z in SEQ1) & (Ax2 := y^z in SEQinj1);  
F05 := [a] in SEQ1;               is LSEQ1c1;               // !! LSEQ1c1 := [x] in SEQ1;
F06 :=  nextf.([a]^C)(x) = nextf.C(x);                      is Lnextf6([a], C)(x)(F04);   
F1 := aC(x) = nextf.([a]^C)(x);   is LaC2(F03);             by F06;  // !! LaC2 := x in im([a]^C) -> aC(x) = nextf.([a]^C)(x);
F2 := aC(x) = nextf.C(x);         // dyz2 :: !! Lnextf6 := A[x:im(z), x ~= Last(z) -> nextf.(y^z)(x) = nextf.z(x)];
 end Proof LaCim1;

! LaCLastC := C ~= [] -> aC(Last(C)) = a;  
 EqProof LaCLastC;
F0 := C ~= [];                    assume;                   // var u0,v0, SEQ; // v_SEQ, v1_SEQ, // u0 := var(SEQ,0) ??? 
F01 := C in SEQ1;                 is L2C(F0);               // ! L2C := C ~= [] -> C in SEQ1;
F02 := Last(C) in im([a]^C);      is TLastimconc@SEQ1;      // SEQ1 :: !! TLastimconc := Last(f) in im(u0^f); 
F03 := Last(C) in A;              is TinIn(F02 & LaCim);    // ! LaCim := im([a]^C) <: A; system can infer it: ! LaCim := im([a]^C) <: A; 
F1 := aC(Last(C));                by LaC0, Red("F");        // ! LaC0 := aC = F[x:A, if(x in im([a]^C), nextf.([a]^C)(x):A, x)];
F2 := if(Last(C) in im([a]^C), nextf.([a]^C)(Last(C)), Last(C));    by Tif1(F02);   // !! Tif1 := p -> if(p,a,b) = a; 
F3 := nextf.([a]^C)(Last(C));     by Lnextf8a@SEQ1(L4C);    // SEQ1 :: !! Lnextf8a := [a]^f in SEQinj1 -> nextf.([a]^f)(Last(f)) = a;
F4 := a;                                                    // ! L4C := [a]^C in SEQinj1; 
 end EqProof LaCLastC;
                                  // !! LinimD := x in im(D) -> ~(x in im([a]^C);   // !! LaC3 := ~(x in im([a]^C)) -> aC(x) = x;
! LaCimD :=  x in im(D) -> aC(x) = x;  // is HS(LinimD & LaC3); // ! HS := (p->q) & (q->r) -> (p->r); // // Hypothetical Syllogism
 Proof LaCimD;
F0 := x in im(D);                 assume;
F01 := ~(x in im([a]^C));         is LinimD(F0);            // !! LinimD := x in im(D) -> ~(x in im([a]^C)); 
F02 := x in A;                    is TinIn(F0 & LDim);      // ! LDim := im(D) <: A;
F1 := aC(x) = x;                  is LaC3(F02 & F01);        // ! LaC3 := x in A & ~(x in im([a]^C)) -> aC(x) = x;
 end Proof LaCimD;

! LaCD0 := D ~= [] -> aC(D(0)) = D(0); 
 Proof LaCD0; 
F0 := D ~= [];                    assume;
F01 := D(0) in im(D);             is TSEQ1_im0.D;           // SEQ1 :: !! TSEQ1_im0 := f(0) in im(f);
F02 := D(0) in A;                 is TinIn(F01 & LDim);     // ! LDim := im(D) <: A; 
F1 := ~(D(0) in im([a]^C));       is LD0imaC(F0);           // !! LD0imaC :=  D ~= [] -> ~(D(0) in im([a]^C));
F2 := aC(D(0)) = D(0);            is LaC3(F02 & F1);        // ! LaC3 := x in A & ~(x in im([a]^C)) -> aC(x) = x;
 end Proof LaCD0;
 
! LaCelse := x in A & x ~= a & x nin im(C) -> aC(x) = x;    // is HS(L3 & LaC3);    
 Proof LaCelse;
F0 := x in A;                     assume;
F01 := x ~= a;                    assume;
F02 := x nin im(C);               assume;
F03 := ~(x in im([a]^C));         is L5C(F01 & F02);        // !! L5C :=  x ~= a & x nin im(C) -> ~(x in im([a]^C));
F1 := aC(x) = x;                  is LaC3(F0 & F03);        // ! LaC3 := x in A & ~(x in im([a]^C)) -> aC(x) = x;
 end Proof LaCelse;

aD := cf([a]^D);

! LaD0 := aD = F[x:A, if(x in im([a]^D), (nextf.([a]^D))(x):A, x)];  byeq Red("F");
! LaD_type := aD in afn(A);      is typeaxiom;
! LdomaD := dom(aD) = A;         is Tafndom1(LaD_type);            // !! Tafndom1 := f in afn(A)-> dom(f) = A;
! LimaD := im(aD) = A;           is Tafnim1(LaD_type);             // !! Tafnim1 := f in afn(A)-> im(f) = A;

! LaD1 := D = [] -> aD = id(A);
 EqProof LaD1;
F0 := D = [];                      assume;
F01 := [a]^D = [a];                by F0; is Lconcempl;            // is !! Lconcempl := A[z:SEQ, z^[] = z];
aD;                                by F01;                         // aD := cf([a]^D); 
F2 := cf([a]);                     by Lcfid;                       // !! Lcfid := A[x_A, cf([x]) = id(A)]; 
F3 := id(A);
 end EqProof LaD1;

! LaD2 := x in im([a]^D) -> aD(x) = nextf.([a]^D)(x);
 EqProof LaD2;
F0 := x in im([a]^D);             assume; 
F01 := x in A;                    is TinIn(F0 & LaDim);            // ! LaDim := im([a]^D) <: A; 
F1 := aD(x);                      by LaD0, Red("F");
F2 := if(x in im([a]^D), nextf.([a]^D)(x):A, x);   by Tif1(F0);    // !! Tif1 := p -> if(p,a,b) = a;
F3 := nextf.([a]^D)(x);
 end EqProof LaD2;

! LaD3 := x in A & ~(x in im([a]^D)) -> aD(x) = x;
 EqProof LaD3;
F0 := x in A;                     assume;
F01 := ~(x in im([a]^D));         assume; 
F1 := aD(x);                      by LaD0, Red("F"); // ! LaD0 := aD = F[x:A, if(x in im([a]^D), nextf.([a]^D)(x):A, x)];
F2 := if(x in im([a]^D), nextf.([a]^D)(x), x);   by Tif2(F01);   // !! Tif2 := ~p -> if(p,a,b) = b;   // :A : error, 2022.10.03;
F3 := x;
 end EqProof LaD3;

! LaDa := D ~= [] -> aD(a) = D(0);
 EqProof LaDa;
F0 := D ~= [];                    assume;
F01 := a in im([a]^D);            is Lconcim3;              // !! Lconcim3 := A[z:SEQ, x in im([x]^z)];
F02 := D in SEQ1;                 is L2D(F0);               // ! L2D := D ~= [] -> D in SEQ1;
F1 := aD(a);                      by LaD2(F01);             // ! LaD0 := aD = F[x:A, if(x in im([a]^D), nextf.([a]^D)(x):A, x)];  byeq Red("F");  
F2 := nextf.([a]^D)(a);           by Lnextf5(L4D);          // !! Lnextf5 := A[x:any, z:SEQ1, [x]^z in SEQinj1 -> nextf.([x]^z)(x)) = z(0)];
F3 := D(0);                                                 // ! L4D := [a]^D in SEQinj1;
 end EqProof LaDa;

! LaDim1 := D ~= [] & x in im(D) & x ~= Last(D) -> aD(x) = nextf.D(x);
 Proof LaDim1;
F0 := D ~= [];                    assume;
F01 := x in im(D);                assume;                   // dyz := {y,z; y in SEQ; z in SEQ; };       
F02 := im(D) <: im([a]^D);        is LconcimIn@dyz;         // dyz :: !! LconcimIn := im(z) <: im(y^z);
F03 := x in im([a]^D);            is TinIn(F01 & F02);      // ! TinIn := x2 in X2 & X2 <: Y2 -> x2 in Y2;
F04 := x ~= Last(D);              assume;                   // dyz2 := dyz && (Ax1 := z in SEQ1) & (Ax2 := y^z in SEQinj1);  
F05 := [a] in SEQ1;               is LSEQ1c1;               // !! LSEQ1c1 := [x] in SEQ1;
F06 :=  nextf.([a]^D)(x) = nextf.D(x);                      is Lnextf6([a], D)(x)(F04);   
F1 := aD(x) = nextf.([a]^D)(x);   is LaD2(F03);             by F06;  // !! LaD2 := x in im([a]^D) -> aD(x) = nextf.([a]^D)(x);
F2 := aD(x) = nextf.D(x);         // dyz2 :: !! Lnextf6 := A[x:im(z), x ~= Last(z) -> nextf.(y^z)(x) = nextf.z(x)];
 end Proof LaDim1;

! LaDimC :=  x in im(C) -> aD(x) = x;
 Proof LaDimC;
F0 := x in im(C);                 assume;
F01 := ~(x in im([a]^D));         is LinimC(F0);            // !! LinimC := x in im(C) -> ~(x in im([a]^D)); 
F02 := x in A;                    is TinIn(F0 & LCim);      // ! LCim := im(C) <: A;
F1 := aD(x) = x;                  is LaD3(F02 & F01);       // ! LaD3 := x in A & ~(x in im([a]^D)) -> aD(x) = x;
 end Proof LaDimC;
 
! LaDLastC := C ~= [] & D ~= [] -> aD(Last(C)) = Last(C); 
 Proof LaDLastC;
F0 := C ~= [];                    assume;
F01 := D ~= [];                   assume;
F02 := Last(C) in im(C);          is TLastim@SEQ1;          // SEQ1 :: !! TLastim := Last(f) in im(f); 
F1 := aD(Last(C)) = Last(C);      is LaDimC(F02);           // ! LaDimC :=  x in im(C) -> aD(x) = x;
 end Proof LaDLastC;

! LaDLastD := D ~= [] -> aD(Last(D)) = a; 
 EqProof LaDLastD;
F0 := D ~= [];                    assume;                   // var u0,v0, SEQ; // v_SEQ, v1_SEQ, // u0 := var(SEQ,0) ??? 
F01 := D in SEQ1;                 is L2D(F0);               // ! L2D := D ~= [] -> D in SEQ1;
F02 := Last(D) in im([a]^D);      is TLastimconc@SEQ1;      // SEQ1 :: !! TLastimconc := Last(f) in im(u0^f); 
F03 := Last(D) in A;              is TinIn(F02 & LaDim);    // ! LaDim := im([a]^C) <: A; system can infer it: ! LaDim := im([a]^D) <: A; 
F1 := aD(Last(D));                by LaD0, Red("F");        // ! LaD0 := aD = F[x:A, if(x in im([a]^D), nextf.([a]^D)(x):A, x)];
F2 := if(Last(D) in im([a]^D), nextf.([a]^D)(Last(D)), Last(D));    by Tif1(F02);   // !! Tif1 := p -> if(p,a,b) = a; 
F3 := nextf.([a]^D)(Last(D));     by Lnextf8a@SEQ1(L4D);    // SEQ1 :: !! Lnextf8a := [a]^f in SEQinj1 -> nextf.([a]^f)(Last(f)) = a;
F4 := a;                                                    // ! L4D := [a]^D in SEQinj1; 
 end EqProof LaDLastD;

! LaDelse := x in A & x ~= a & x nin im(D) -> aD(x) = x;    // no x in A ???: because aD(x) was merged with correct aD(x) in LaD2, LaD3, ... 
 Proof LaDelse;
F0 := x in A;                     assume;
F01 := x ~= a;                    assume;
F02 := x nin im(D);               assume;
F03 := ~(x in im([a]^D));         is L5D(F01 & F02);        // !! L5D :=  x ~= a & x nin im(D) -> ~(x in im([a]^D));
F1 := aD(x) = x;                  is LaD3(F0 & F03);        // ! LaD3 := x in A & ~(x in im([a]^D)) -> aD(x) = x;
 end Proof LaDelse;

aDC := cf(saDC);                  // saDC := [a]^D^C;
! LaDC0 := aDC = F[x:A, if(x in im(saDC),  nextf.saDC(x):A, x)];   byeq Red("F");
! LaDC_type := aDC in afn(A);     is typeaxiom;
! LaDCdom := dom(aDC) = A;        is Tafndom1(LaDC_type);   // !! Tafndom1 := f in afn(A)-> dom(f) = A;
! LaDC01 := C=[] -> saDC = [a]^D;  is Lconcemp1@SEQ;        // SEQ :: !! Lconcemp1 := A[z:SEQ, z=[] -> f^z = f];
! LaDC02 := D=[] -> saDC = [a]^C;  is Lconcemp2;            // !! Lconcemp2 := A[u,y,z:SEQ, y=[] ->u^y^z = u^z];

! LaDC1 := C=[] -> aDC = aD;  
 Proof LaDC1;
F0 := C=[];                       assume; 
F01 := saDC = [a]^D;              is LaDC01(F0);            //  ! LaDC01 = C=[] -> saDC = [a]^D;
F1 := aDC = aD;                   byeq F01;
 end Proof LaDC1;

! LaDC2 := D=[] -> aDC = aC; 
 Proof LaDC2;
F0 := D=[];                       assume; 
F01 := saDC = [a]^C;              is LaDC02(F0);            //  ! LaDC02 = D=[] -> saDC = [a]^C;
F1 := aDC = aC;                   byeq F01;
 end Proof LaDC2;

! LaDCa := D ~= [] -> aDC(a) = D(0);                       // ! LaDC0 := aDC = F[x:A, if(x in im(saDC),  nextf.saDC(x):A, x)];
 EqProof LaDCa;
F0 := D ~= [];                   assume;
F01 := D in SEQ1;                is L2D(F0);               // ! L2D := D ~= [] -> D in SEQ1;  
F02 := a in im(saDC);            is Lconcim3a;             // ! Lconcim3a := A[z:SEQ, x in im([x]^z^u0)]; 
F1 := aDC(a);                    by LaDC0, Red("F");
F2 := if(a in im(saDC),  nextf.saDC(a), a);                 by Tif1(F02);
F3 := nextf.saDC(a);             by Lnextf5a@dyz2(L5);      // dyz2 :: !! Lnextf5a := [x]^z^y in SEQinj1 -> nextf.([x]^z^y)(x) = z(0);
F4 := D(0);                                                 // !! L5 := saDC in SEQinj1;
 end EqProof LaDCa;

! LaDCim1C := x in im(C) & x ~= Last(C) -> aDC(x) = nextf.C(x);
 EqProof LaDCim1C;
F0 := x in im(C);                assume;  // uyz := {u,y,z; u in SEQ, y in SEQ, z in SEQ1; Ax1 := u^y^z in SEQinj1; }; 
F00 := C in SEQ1;                is LSEQim@SEQ(F0);         // SEQ :: LSEQim := x in im(f) -> f in SEQ1;
F01 := x ~= Last(C);             assume;  // uyz :: !! Lnextf6a :=  A[x: im(y),  z in SEQ1 & x ~= Last(z) -> nextf.(u^y^z)(x) = nextf.z(x)];
F02 := x in im(saDC);            is TinIn(F0 & L9);         // !! L9 := im(C) <: im(saDC);
F03 := nextf.saDC(x) = nextf.C(x);                          is Lnextf6a([a],D,C)(x)(F00 & F01);
F1 := aDC(x);                    by LaDC0, Red("F");
F2 := if(x in im(saDC),  nextf.saDC(x), x);                 by Tif1(F02);
F3 := nextf.saDC(x);             by F03;
F4 := nextf.C(x);
 end EqProof LaDCim1C;
                       
! LaDCim1D := x in im(D) & x ~= Last(D) -> aDC(x) = nextf.D(x);
 EqProof LaDCim1D;
F0 := x in im(D);                assume;  // uyz := {u,y,z; u in SEQ, y in SEQ, z in SEQ1; Ax1 := u^y^z in SEQinj1; }; 
F00 := D in SEQ1;                is LSEQim@SEQ(F0);         // SEQ :: LSEQim := x in im(f) -> f in SEQ1;
F01 := x ~= Last(D);             assume;  // uyz :: !! Lnextf6b :=  A[x: im(y),  y in SEQ1 & x ~= Last(y) -> nextf.(u^y^z)(x) = nextf.y(x)];
F02 := x in im(saDC);            is TinIn(F0 & L9a);        // !! L9a := im(D) <: im(saDC);
F03 := nextf.saDC(x) = nextf.D(x);                          is Lnextf6b([a],D,C)(x)(F00 & F01);
F1 := aDC(x);                    by LaDC0, Red("F");
F2 := if(x in im(saDC),  nextf.saDC(x), x);                 by Tif1(F02);
F3 := nextf.saDC(x);             by F03;
F4 := nextf.D(x);
 end EqProof LaDCim1D;

! LaDC_LastC := C ~= [] -> aDC(Last(C)) = a;
 EqProof LaDC_LastC;
F0 := C ~= [];                  assume;
F01 := C in SEQ1;               is L2C(F0);                           // ! L2C := C ~= [] -> C in SEQ1;
F02 := Last(C) in im(saDC);     is TLastimconc1@SEQ1;                 // SEQ1 :: !! TLastimconc1 := Last(f) in im(u0^v0^f);
F03 := [a] in SEQ1;             is LSEQ1c1;                           // !! LSEQ1c1 := [x] in SEQ1;
F1 := aDC(Last(C));             by LaDC0, Red("F");      
F2 := if(Last(C) in im(saDC),  nextf.saDC(Last(C)), Last(C));         by Tif1(F02);  
F3 := nextf.saDC(Last(C));      by Lnextf4a([a],D,C)(F03 & F01 & L5); // !! L5 := saDC in SEQinj1;    
F4 := [a](0);                   by LSEQ1S0;                           // !! LSEQ1S0 := [x](0) = x;   // F04; 
F5 := a;                        // uyz :: !! Lnextf4a := u in SEQ1 & z in seq1 & u^y^z in SEQinj1 -> nextf.(u^y^z)(Last(z)) = u(0);
 end EqProof LaDC_LastC;

! LaDC_LastD := D ~= [] & C ~= [] -> aDC(Last(D)) = C(0);
 EqProof LaDC_LastD;
F0 := D ~= [];                  assume;
F00 := C ~= [];                 assume;                     
F01 := C in SEQ1;               is L2C(F00);                // ! L2C := C ~= [] -> C in SEQ1;
F02 := Last(D) in im(saDC);     is TLastimconc2@SEQ1;       // SEQ1 :: !! TLastimconc2 := Last(f) in im(u0^f^v0); 
F03 := D in SEQ1;               is L2D(F0);                 // ! L2D := D ~= [] -> D in SEQ1; 
F1 := aDC(Last(D));             by LaDC0, Red("F");         
F2 := if(Last(D) in im(saDC),  nextf.saDC(Last(D)), Last(D));            by Tif1(F02);   // !! L5 := saDC in SEQinj1;
F3 := nextf.saDC(Last(D));      by Lnextf4b([a],D,C)(F03 & F01 & L5);    
F4 := C(0);                     // uyz :: !! Lnextf4b := y in SEQ1 & z in SEQ1 & u^y^z in SEQinj1 -> nextf.(u^y^z)(Last(y)) = z(0);
 end EqProof LaDC_LastD;

! LaDCelse := x in A & x~=a & x nin im(D) &  x nin im(C) -> aDC(x) = x;
 EqProof LaDCelse;
F0 := x in A;                     assume;
F01 := x ~= a;                    assume;
F02 := x nin im(D);               assume;
F03 := x nin im(C);               assume;
F04 := ~(x in im(saDC));          is L6(F01 & F02 & F03);            // !! L6 := x ~= a & x nin im(D) & x nin im(C) -> ~(x in im([a]^D^C));
F1 := aDC(x);                     by LaDC0, Red("F");
F2 := if(x in im(saDC), nextf.saDC(x), x);  by Tif2(F04);            // !! Tif2 := ~p -> if(p,a,b) = b;  
F3 := x;
 end EqProof LaDCelse;
                                                                     // ! LaC_type := aC in afn(A);// ! LaD_type := aD in afn(A);
! LaCaD := aC o aD in afn(A);     is Tafncomp1(LaC_type & LaD_type); // !! Tafncomp1 := f in afn(A) & g in afn(A) -> f o g in afn(A)];  
! LaCaDdom := dom(aC o aD) = A;   is Tafndom1(LaCaD);                // !! Tafndom1 := f in afn(A)-> dom(f) = A;
! L0 := im(aD) <: dom(aC);        by LimaD, LdomaC; is TInrefl;       // ! TInrefl := X <: X; 
! L01 := dom(aD) = dom(aC o aD);  by LdomaD, LaCaDdom; is Axrefl;    // ? byeq ?

! LT3case := C=[] or D=[] or C ~= [] & D ~= [];  by Axneq, Axneq;     is Taut;

! T3 := aC o aD = aDC;         // ! Case3 := (p1 or p2 or p3) -> q == (p1 -> q) & (p2 -> q) & (p3 -> q);
 Proof T3;    by Case3(LT3case);   L1 & L2 & L3;
L1 := C=[] -> aC o aD = aDC;
  EqProof L1;
F0 := C=[];                    assume;
F1 := aC o aD;                 by LaC1(F0);      // !! LaC1 := C=[] -> aC = id(A);
F2 := id(A) o aD;              by Tafn4a;        // !! Tafn4a := A[f: afn(A), id(A) o f = f]; 
F3 := aD;                      by -LaDC1(F0);
F4 := aDC;
  end EqProof L1;

L2 := D=[] -> aC o aD = aDC;
  EqProof L2;
F0 := D =[];                   assume;
F01 := A[f: afn(A), f o id(A) = f];              is Tafn4;  // !! Tafn4 := A[f: afn(A), f o id(A) = f]; // DIFFERENT A's !!! 
F1 := aC o aD;                 by LaD1(F0);      // !! LaD1 := D=[] -> aD = id(A);
F2 := aC o id(A);              by F01;         
F3 := aC;                      by -LaDC2(F0);    // !! LaDC2 := D=[] -> aDC = aC; 
F4 := aDC;
  end EqProof L2;

! L3 := C ~= [] & D ~= [] -> aC o aD = aDC;
 Proof L3;
F0C := C ~= [];                 assume;
F01 := C in SEQ1;              is L2C(F0C);       // !! L2C := C ~= [] -> C in SEQ1;   // wlot can prove F01 ;
F0D := D ~= [];                assume; 
F03 := D in SEQ1;              is L2D(F0D);       // !! L2D := D ~= [] -> D in SEQ1;   // wlot can prove F03;
F07 := C in SEQinj1;           is L1C(F0C);       // !! L1C := C ~= [] -> C in SEQinj1; // F0C := C ~= []; 
F08 := D in SEQinj1;           is L1D(F0D);       // L1D := D ~= [] -> D in SEQinj1;    // F0D := D ~= [];

G0 := aC o aD = aDC;           by Tfneq; Ldom & LA; // !! Tfneq := A[f,g: FN, f=g == dom(f)=dom(g) & A[x:dom(f), f(x)=g(x)]]; 
Ldom := dom(aC o aD) = dom(aDC); byeq LaCaDdom, -LaDCdom;

! LAcase := x in A == x=a or x in im(D) & x~=Last(D) or x=Last(D) or x in im(C) & x~=Last(C) or x=Last(C) or
                 x in A & x~=a & x nin im(D) & x nin im(C); is Lconcim6(A,a,D,C)(LDim & LCim);    // ! LDim := im(D) <: A; ! LCim := im(C) <: A;
 
// !! Lconcim6 := A[A:set, a:A, y,z:SEQ1, im(y)<:A & im(z)<:A -> (x in A ==  x=a or x in im(y)&x~=Last(y) or x=Last(y) or 
//                              x in im(z)&x~=Last(z) or x=Last(z) or x in A & x~=a & x nin im(y) & x nin im(z)];

! LA := A[x:dom(aC o aD),(aC o aD)(x) = aDC(x)]; 
   Proof LA;
F0 := x in dom(aC o aD);       assume; by LaCaDdom;
F0A := x in A;                 by LAcase;         // fgcomp := {f,g ; f in FN, g in FN, Axfg := im(g) <: dom(f)};
F1 := x=a or x in im(D) & x ~= Last(D) or x=Last(D)  or x in im(C) & x~=Last(C) or x=Last(C) or x in A & x~=a & x nin im(D) & x nin im(C);
G0 := (aC o aD)(x) = aDC(x);   by Tcompval(aC, aD);       // !! Tcompval := A[x:dom(g), (f o g)(x) = f(g(x))];
G1 := aC(aD(x)) = aDC(x);      by Case6(F1); L1 & L2 & L3 & L4 & L5 & L6;

! L1 := x=a -> G1;                                // Case 3.1. x=a:(aC∘aD)(a)=first(D);aDC(a)=first(D); // first(D) = D(0);
    Proof L1;
F0 := x=a;                     assume;                          // F0D := D ~= []; 
F1 := aC(aD(x)) = D(0);        byeq F0,LaDa(F0D),LaCD0(F0D);    // !! LaDa := D ~= [] -> aD(a) = D(0); // !! LaCD0 := D ~= [] -> aC(D(0)) = D(0); 
F2 := aDC(x) = D(0);           byeq F0,LaDCa(F0D);       // !! LaDCa := D ~= [] -> aDC(a) = D(0);
G1;                            byeq F1, -F2;             // 9.11.22:DNW: is Axeq2(F1 & F2);  // !! Axeq2 := x=a & y=a -> x=y; DNW: did not work; 
    end Proof L1;              // G1 := aC(aD(x)) = aDC(x); 

! L2 := x in im(D) & x ~= Last(D) -> G1;          // Case 3.2. x∈im(D) and x≠last(D):(aC∘aD)(x)=next(D,x);aDC(x)=next(D,x);        
    Proof L2;
F0 := x in im(D);              assume;
F01 := x ~= Last(D);           assume;                   // F0D := D ~= [];  // !! LaCimD  := x in im(D) -> aC(x) = x;
F02 := nextf.D(x) in im(D);    is Lnextf3.D(x);          // !! Lnextf3 := A[x_imf, nextf(x) in im(f)]; 
F03 := aC(nextf.D(x)) = nextf.D(x);  is LaCimD(F02);     // !! LaCimD :=  x in im(D) -> aC(x) = x;           
F1 := aC(aD(x)) = nextf.D(x);  byeq LaDim1(F0D & F0 & F01), F03;    // !! LaDim1 := D ~= [] & x in im(D) & x ~= Last(D) -> aD(x) = nextf.D(x);    
F2 := aDC(x) = nextf.D(x);     byeq LaDCim1D(F0 & F01);  // !! LaDCim1D := x in im(D) & x ~= Last(D) -> aDC(x) = nextf.D(x);
G1;                            byeq F1, -F2;
    end Proof L2;                // G1 := aC(aD(x)) = aDC(x); 

! L3 := x=Last(D) -> G1;                         // Case 3.3. x=last(D);(aC∘aD)(last(D))=first(C);aDC(x)=first(C);
    Proof L3;                    // was Proof L1;  ??? not catched ???  // !! LaCa := C ~= [] -> aC(a) = C(0);
F0 := x=Last(D);               assume;                        // F0D := D ~= []; // !! LaCD0 := D ~= [] -> aC(D(0)) = D(0); 
F1 := aC(aD(x)) = C(0);        byeq F0,LaDLastD(F0D), LaCa(F0C);    // !! LaDLastD := D ~= [] -> aD(Last(D)) = a;  
F2 := aDC(x) = C(0);           byeq F0,LaDC_LastD(F0D & F0C); // !! LaDC_LastD := D ~= [] & C ~= [] -> aDC(Last(D)) = C(0); 
G1;                            byeq F1, -F2;                  // G1 := aC(aD(x)) = aDC(x);
    end Proof L3;                // byeq F0,LaDLastD(F0D )& LaCa; ??? did not catched ???

! L4 := x in im(C) & x~=Last(C) -> G1;           // Case 3.4. x∈im(C) and x≠last(C):(aC∘aD)(x)=next(C,x);aDC(x)=next(C,x);
    Proof L4;
F0 := x in im(C);              assume;                    // G1 := aC(aD(x)) = aDC(x); 
F01 := x ~= Last(C);           assume;                    // F0D := D ~= [];  // !! LaCimD  := x in im(D) -> aC(x) = x;
F02 := nextf.C(x) in im(C);    is Lnextf3.C(x);           // !! Lnextf3 := A[x_imf, nextf(x) in im(f)]; 
F03 := aC(x) = nextf.C(x);     is LaCim1(F0C & F0 & F01); // !! LaCim1 := C ~= [] & x in im(C) & x ~= Last(C) -> aC(x) = nextf.C(x); 
F1 := aC(aD(x)) = nextf.C(x);  byeq LaDimC(F0), F03;      // !! LaDimC :=  x in im(C) -> aD(x) = x; 
F2 := aDC(x) = nextf.C(x);     byeq LaDCim1C(F0 & F01);   // !! LaDCim1C := x in im(C) & x ~= Last(C) -> aDC(x) = nextf.C(x);  
G1;                            byeq F1, -F2;              // G1 := aC(aD(x)) = aDC(x); 
    end Proof L4;

! L5:= x=Last(C) -> G1;                          // Case 3.5. x=last(C);(aC∘aD)(last(C))=a;aDC(last(C))=a
    Proof L5;
F0 := x=Last(C);              assume;                      // F0C := C ~= []; // !! LaCLastC := C ~= [] -> aC(Last(C)) = a;
F1 := aC(aD(x)) = a;          byeq F0,LaDLastC(F0C & F0D),LaCLastC(F0C);  // !! LaDLastC := C ~= [] & D ~= [] -> aD(Last(C)) = Last(C);   
F2 := aDC(x) = a;             byeq F0,LaDC_LastC(F0C);     // !! LaDC_LastC := C ~= [] -> aDC(Last(C)) = a; 
G1;                           byeq F1, -F2;                // G1 := aC(aD(x)) = aDC(x);
    end Proof L5;                

! L6 := x in A & x~=a & x nin im(D) &  x nin im(C) -> G1; // Case 3.6. x≠a,x∉im(C),x∉im(D):(aC∘aD)(x)=x;aDC(x)=x; 
    Proof L6;
F00 := x in A;               assume;
F0 := x~=a;                  assume;
F01 := x nin im(D);          assume;                                     // F0A := x in A;
F02 := x nin im(C);          assume;                                     // !! LaCelse := x in A & x ~= a & x nin im(C) -> aC(x) = x;
F1 := aC(aD(x)) = x;         byeq LaDelse(F00 & F0 & F01), LaCelse(F0A & F0 & F02);  // !! LaDelse := x ~= a & x nin im(D) -> aD(x) = x;
F2 := aDC(x) = x;            byeq LaDCelse(F00 & F0 & F01 & F02);        // !! LaDCelse := x in A & x~=a & x nin im(D) &  x nin im(C) -> aDC(x) = x;
G1;                          byeq F1, -F2;                               // G1 := aC(aD(x)) = aDC(x);
    end Proof L6;
   end Proof LA;
  end Proof L3;
 end Proof T3;

 ]; // aCD :: [
]; //  perm :: [  // 2

// !! LdconjIn := (d&&P) <: d;                   // && precedence ???
// !! Ldconjfs := d in finset -> (d&&P) in finset;
// !! Tafnfn1 := f in afn(A) -> f in fn(A,A); 
// !! TafnAFN := afn(A) <: AFN; // rename to LafnAFN???
// !! LafnFif := B<:A & f in afn(B) -> F[x:A, if(x in B, f(x), x)] in afn(A);
// !! Lafn2 := A in finset & f in fn(A,A) & injective(f) -> f in afn(A);
// !! TFdom1   := dom(F[x:A, G(x)]) = A;                 // root :: !! TFdom1 := dom(FAGx) = A; 
// !! TAinIna := A[d, g in A] & A<:B -> A[d, g in B];  
// !! TfinsetRa := X in finset -> R[x:X, G(x)] in finset;
// AFN :: !! LAFNinj := injective(f);
// AFN :: !! LAFN4 := A[x:dom(f),k:int, f((f^k)(x)) = (f^(k+1))(x)];
// AFN :: !! L4 := f in afn(dom(f));!! L4 := f in afn(dom(f));
// !! Lafn9 := g in AFN & dom(g)=A -> g in afn(A);
// dcl[||, fn({f:AFN, A:set; dom(f) <: A}, afn(A)];   // extension of f on A;
// f_AFN_A_set := {f:AFN, A:set; dom(f) <: A};
// (||) := F[{f:AFN, A:set; dom(f) <: A}, F[x:A, if(x in dom(f), f(x), x)]];
// ! Tdvl := A[f_AFN_A_set, f||A = F[x:A, if(x in dom(f), f(x), x)]];                 byeq Red("F");  // dvl: double vertical line;
// ! Ldvldom := A[f_AFN_A_set, dom(f||A) = A];                                        by Tdvl; is TFdom1;
// !! Ldvlafn := A[f_AFN_A_set, Ldvlafn_type := f||A in afn(A)];

] // end module 2_altg.v