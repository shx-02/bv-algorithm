needs "Multivariate/transcendentals.ml";;

needs "Multivariate/cross.ml";;

needs "Multivariate/realanalysis.ml";;

needs "Library/grouptheory.ml";;

needs "Multivariate/cvectors.ml";;

needs "Multivariate/vectors.ml";;

needs "Library/binary.ml";;

needs "Library/words.ml";;

let COND_RIGHT_F =
 prove
  (`(if b then b else F) = b`,
   BOOL_CASES_TAC `b:bool` THEN
   REWRITE_TAC []);;

let COND_T_F =
 prove
  (`(if b then  T else F) = b`,
   BOOL_CASES_TAC `b:bool` THEN
   REWRITE_TAC []);;

let MOD_ZERO = prove
 (`!n. n MOD 0 = n`,
  MESON_TAC[DIVISION_0]);;

let DIV_ZERO = prove
 (`!n. n DIV 0 = 0`,
  MESON_TAC[DIVISION_0]);;

let UNION_RESTRICT = prove
 (`!P s t:A->bool.
        {x | x IN (s UNION t) /\ P x} =
        {x | x IN s /\ P x} UNION {x | x IN t /\ P x}`,
  SET_TAC[]);;

let NUMSEG_CLAUSES_LT = prove
 (`{i | i < 0} = {} /\
   (!k. {i | i < SUC k} = k INSERT {i | i < k})`,
  REWRITE_TAC[LT] THEN SET_TAC[]);;

let DISJOINT_SING = prove
 (`(!s a:A. DISJOINT s {a} <=> ~(a IN s)) /\
   (!s a:A. DISJOINT {a} s <=> ~(a IN s))`,
  SET_TAC[]);;

  
(* ------------------------------------------------------------------------- *)
(* For the definition and verification of the N_H gate  *)
(* ------------------------------------------------------------------------- *)

let numbit = new_definition `numbit i n = ODD(n DIV (2 EXP i))`;;

let bits_of_num = new_definition
 `bits_of_num n = {i | numbit i n}`;;

let IN_BITS_OF_NUM = prove
 (`!n i. i IN bits_of_num n <=> ODD(n DIV 2 EXP i)`,
  REWRITE_TAC[bits_of_num; numbit; IN_ELIM_THM]);;

let BITS_OF_NUM_SUBSET_NUMSEG_LT = prove
 (`!n. bits_of_num n SUBSET {i | i < n}`,
  REWRITE_TAC[SUBSET; IN_ELIM_THM; IN_BITS_OF_NUM] THEN
  MESON_TAC[DIV_LT; EVEN; LT_POW2_REFL; LET_TRANS; NOT_LE; NOT_EVEN]);;

let FINITE_BITS_OF_NUM = prove
 (`!n. FINITE(bits_of_num n)`,
  MESON_TAC[BITS_OF_NUM_SUBSET_NUMSEG_LT; FINITE_NUMSEG_LT; FINITE_SUBSET]);;

let BITSET_EQ_BITSNUM = prove
(`!a:num. bitset a = bits_of_num a `,
SIMP_TAC[bitset;bits_of_num;numbit]);;

let ITERATE_CLAUSES_NUMSEG_LT = prove
 (`!op. monoidal op
        ==> iterate op {i | i < 0} f :A = neutral op /\
            (!k. iterate op {i | i < SUC k} f =
                 op (iterate op {i | i < k} f) (f k))`,
  SIMP_TAC[NUMSEG_CLAUSES_LT; ITERATE_CLAUSES; FINITE_NUMSEG_LT] THEN
  REWRITE_TAC[IN_ELIM_THM; LT_REFL; monoidal] THEN MESON_TAC[]);;

let NSUM_CLAUSES_NUMSEG_LT = prove
 (`nsum {i | i < 0} f = 0 /\
   (!k. nsum {i | i < SUC k} f = nsum {i | i < k} f + f k)`,
  MP_TAC(MATCH_MP ITERATE_CLAUSES_NUMSEG_LT MONOIDAL_ADD) THEN
  REWRITE_TAC[NEUTRAL_ADD; nsum]);;

let DIGITSUM_BOUND = prove
 (`!B b k. (!i. i < k ==> b i < B)
           ==> nsum {i | i < k} (\i. B EXP i * b i) < B EXP k`,
  GEN_TAC THEN GEN_TAC THEN INDUCT_TAC THEN
  REWRITE_TAC[NSUM_CLAUSES_NUMSEG_LT; EXP; ARITH] THEN
  REWRITE_TAC[LT] THEN DISCH_TAC THEN
  MATCH_MP_TAC(ARITH_RULE
   `s < e /\ e * (x + 1) <= e * b ==> s + e * x < b * e`) THEN
  ASM_SIMP_TAC[LE_MULT_LCANCEL; ARITH_RULE `b + 1 <= c <=> b < c`]);;

let ZERO_DIV = prove
(`!n.0 DIV n = 0`,
GEN_TAC THEN ASM_CASES_TAC`n = 0` THENL [ASM_SIMP_TAC[]
THEN SIMP_TAC[SPEC`0` DIV_ZERO];ALL_TAC] THEN ASM_SIMP_TAC[DIV_0]);;

let ZERO_MOD = prove
(`!n. 0 MOD n = 0`,
GEN_TAC THEN ASM_CASES_TAC`n = 0` THENL
[ASM_SIMP_TAC[MOD_ZERO];ALL_TAC] THEN ASM_SIMP_TAC[MOD_0]);;

let DIGITSUM_SPLIT = prove
 (`!B b s n.
        FINITE s
        ==> B EXP n * nsum {i | i IN s /\ n <= i} (\i. B EXP (i - n) * b i) +
            nsum {i | i IN s /\ i < n} (\i. B EXP i * b i) =
            nsum s (\i. B EXP i * b i)`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[GSYM NSUM_LMUL; MULT_ASSOC; GSYM EXP_ADD] THEN
  SIMP_TAC[ARITH_RULE `n:num <= i ==> n + i - n = i`] THEN
  MATCH_MP_TAC NSUM_UNION_EQ THEN ASM_REWRITE_TAC[GSYM NOT_LT] THEN
  SET_TAC[]);;

let DIGITSUM_DIV,DIGITSUM_MOD = (CONJ_PAIR o prove)
 (`(!B b s n.
        FINITE s /\ (!i. i IN s ==> b i < B)
        ==> nsum s (\i. B EXP i * b i) DIV (B EXP n) =
            nsum {i | i IN s /\ n <= i} (\i. B EXP (i - n) * b i)) /\
   (!B b s n.
        FINITE s /\ (!i. i IN s ==> b i < B)
        ==> nsum s (\i. B EXP i * b i) MOD (B EXP n) =
            nsum {i | i IN s /\ i < n} (\i. B EXP i * b i))`,
  REWRITE_TAC[AND_FORALL_THM] THEN REPEAT GEN_TAC THEN
  ASM_CASES_TAC `B = 0` THENL
   [ASM_REWRITE_TAC[CONJUNCT1 LT; SET_RULE `(!x. ~(x IN s)) <=> s = {}`] THEN
    SIMP_TAC[EMPTY_GSPEC; NOT_IN_EMPTY; CONJUNCT1 NSUM_CLAUSES] THEN
    SIMP_TAC[ZERO_DIV;ZERO_MOD];ALL_TAC] THEN
  REWRITE_TAC[TAUT `(p ==> q) /\ (p ==> r) <=> p ==> q /\ r`] THEN
  STRIP_TAC THEN MATCH_MP_TAC DIVMOD_UNIQ THEN CONJ_TAC THENL
   [GEN_REWRITE_TAC (RAND_CONV o LAND_CONV) [MULT_SYM] THEN
    MATCH_MP_TAC(GSYM DIGITSUM_SPLIT) THEN ASM_REWRITE_TAC[];ALL_TAC]
    THEN ONCE_SIMP_TAC[SET_RULE
     `{x | x IN s /\ P x} = {x | x IN {y | P y} /\ x IN s}`] THEN
    REWRITE_TAC[NSUM_RESTRICT_SET; MESON[MULT_CLAUSES]
     `(if p then a * b else 0) = a * (if p then b else 0)`] THEN
    MATCH_MP_TAC DIGITSUM_BOUND THEN ASM_MESON_TAC[LE_1]);;

let MULT_EQ_NOT_0 = prove
 (`!m n. ~(m = 0) /\ ~(n = 0) <=> ~(m * n = 0)`,
SIMP_TAC[TAUT`~(m = 0) /\ ~(n = 0) <=> ~(m = 0 \/ n = 0)`]
THEN SIMP_TAC[CONTRAPOS_THM;MULT_EQ_0]);;

let DIV_MOD_ALT = prove
 (`!m n p. (m DIV n) MOD p = (m MOD (n * p)) DIV n`,
  REPEAT GEN_TAC THEN
  ASM_CASES_TAC `p = 0` THENL [ASM_REWRITE_TAC[MOD_ZERO; MULT_CLAUSES];ALL_TAC] THEN
  ASM_CASES_TAC `n = 0` THENL [ASM_SIMP_TAC[MOD_0; MULT_CLAUSES; DIV_ZERO];ALL_TAC] THEN
  REPEAT (POP_ASSUM MP_TAC) THEN SIMP_TAC[TAUT`p ==> q ==> r <=> p /\ q ==> r`]
  THEN SIMP_TAC[MULT_EQ_NOT_0;DIV_MOD] THEN SIMP_TAC[ARITH_RULE`p * n:num = n * p`]
  THEN SIMP_TAC[DIV_MOD]);;

let DIGITSUM_DIV_MOD = prove
 (`!B b s n.
        FINITE s /\ (!i. i IN s ==> b i < B)
        ==> nsum s (\i. B EXP i * b i) DIV (B EXP n) MOD B =
            if n IN s then b n else 0`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[DIV_MOD_ALT] THEN
  REWRITE_TAC[MESON[EXP; MULT_SYM] `B EXP n * B = B EXP SUC n`] THEN
  ASM_SIMP_TAC[DIGITSUM_MOD] THEN
  ASM_SIMP_TAC[DIGITSUM_DIV; FINITE_RESTRICT; IN_ELIM_THM] THEN
  REWRITE_TAC[GSYM CONJ_ASSOC; ARITH_RULE `i < SUC n /\ n <= i <=> i = n`] THEN
  REWRITE_TAC[MESON[] `i IN s /\ i = n <=> n IN s /\ i = n`] THEN
  ASM_CASES_TAC `(n:num) IN s` THEN
  ASM_REWRITE_TAC[EMPTY_GSPEC; NSUM_CLAUSES] THEN
  REWRITE_TAC[SING_GSPEC; NSUM_SING; SUB_REFL; MULT_CLAUSES; EXP]);;

let BITS_OF_NUM_NSUM = prove
 (`!s. FINITE s ==> bits_of_num (nsum s (\i. 2 EXP i)) = s`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[EXTENSION;IN_BITS_OF_NUM; ODD_MOD] THEN
  X_GEN_TAC `k:num` THEN MP_TAC(SPECL
    [`2`; `\i:num. 1`; `s:num->bool`; `k:num`] DIGITSUM_DIV_MOD) THEN
  ASM_SIMP_TAC[ARITH_RULE `1 < 2`; MULT_CLAUSES] THEN ARITH_TAC);;

let MOD_MULT_MOD = prove
 (`!m n p. m MOD (n * p) = n * (m DIV n) MOD p + m MOD n`,
  REPEAT GEN_TAC THEN ASM_CASES_TAC `n = 0` THEN
  ASM_REWRITE_TAC[MULT_CLAUSES; MOD_ZERO; ADD_CLAUSES] THEN
  ASM_CASES_TAC `p = 0` THENL
   [ASM_REWRITE_TAC[MULT_CLAUSES; MOD_ZERO] THEN
    ASM_METIS_TAC[DIVISION; MULT_SYM];ALL_TAC] THEN
MP_TAC(SPECL[`m DIV n DIV p * n * p`;`m MOD (n * p)`;`n * (m DIV n) MOD p + m MOD n`](GSYM EQ_ADD_LCANCEL))
THEN STRIP_TAC THEN ASM_SIMP_TAC[] THEN UNDISCH_TAC`~(p = 0)` THEN
UNDISCH_TAC`~(n = 0)` THEN SIMP_TAC[TAUT`p ==> q ==> r <=> p /\ q ==> r`]
  THEN SIMP_TAC[MULT_EQ_NOT_0;DIVISION_SIMP;DIV_DIV] THEN
  SIMP_TAC[ARITH_RULE`d * n * p:num = n * (d * p)`] THEN
  SIMP_TAC[GSYM LEFT_ADD_DISTRIB; ADD_ASSOC;GSYM DIV_DIV] THEN
  ABBREV_TAC`k = m DIV n` THEN SIMP_TAC[GSYM MULT_EQ_NOT_0] THEN
  POP_ASSUM MP_TAC THEN CONV_TAC(ONCE_DEPTH_CONV SYM_CONV)
  THEN SIMP_TAC[DIVISION_SIMP]);;

let DIGITSUM_WORKS_GEN = prove
 (`!B n k.
    nsum {i | i < k} (\i. B EXP i * n DIV (B EXP i) MOD B) = n MOD (B EXP k)`,
  GEN_TAC THEN GEN_TAC THEN MATCH_MP_TAC num_INDUCTION THEN
  SIMP_TAC[NUMSEG_CLAUSES_LT; NSUM_CLAUSES; MOD_1; EXP; FINITE_NUMSEG_LT] THEN
  X_GEN_TAC `k:num` THEN DISCH_TAC THEN REWRITE_TAC[IN_ELIM_THM; LT_REFL] THEN
  MESON_TAC[MOD_MULT_MOD; MULT_SYM]);;

let MOD_2_CASES = prove
 (`!n. n MOD 2 = if EVEN n then 0 else 1`,
  MESON_TAC[EVEN_MOD; ODD_MOD; NOT_ODD]);;

let NSUM_BITS_OF_NUM = prove
 (`!n. nsum (bits_of_num n) (\i. 2 EXP i) = n`,
  GEN_TAC THEN MP_TAC(SPECL [`2`; `n:num`; `n:num`] DIGITSUM_WORKS_GEN) THEN
  REWRITE_TAC[MOD_2_CASES; COND_RAND; MULT_CLAUSES] THEN
  REWRITE_TAC[GSYM NOT_ODD; COND_SWAP; GSYM NSUM_RESTRICT_SET] THEN
  SIMP_TAC[MOD_LT; LT_POW2_REFL] THEN MATCH_MP_TAC EQ_IMP THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  MP_TAC(SPEC `n:num` BITS_OF_NUM_SUBSET_NUMSEG_LT) THEN
  REWRITE_TAC[bits_of_num; numbit] THEN SET_TAC[]);;

let BITS_OF_NUM_GALOIS = prove
 (`!n s. bits_of_num n = s <=> FINITE s /\ nsum s (\i. 2 EXP i) = n`,
  MESON_TAC[FINITE_BITS_OF_NUM; BITS_OF_NUM_NSUM; NSUM_BITS_OF_NUM]);;

let BITS_OF_NUM_POW2 = prove
 (`!k. bits_of_num(2 EXP k) = {k}`,
  REWRITE_TAC[IN_BITS_OF_NUM; EXTENSION; IN_ELIM_THM; IN_SING] THEN
  REPEAT GEN_TAC THEN SIMP_TAC[DIV_EXP; ARITH_EQ] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[ODD_EXP; ARITH] THEN ASM_ARITH_TAC);;

let BITS_OF_NUM_ADD = prove
 (`!m n. DISJOINT (bits_of_num m) (bits_of_num n)
         ==> bits_of_num(m + n) = (bits_of_num m) UNION (bits_of_num n)`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[BITS_OF_NUM_GALOIS; FINITE_UNION; FINITE_BITS_OF_NUM] THEN
  ASM_SIMP_TAC[NSUM_UNION; FINITE_BITS_OF_NUM; NSUM_BITS_OF_NUM]);;

let NSUM_BITS_DIV = prove
 (`!s k. FINITE s
         ==> nsum s (\i. 2 EXP i) DIV 2 EXP k =
             nsum {i | i IN s /\ k <= i} (\i. 2 EXP (i - k))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`2`; `\i:num. 1`; `s:num->bool`; `k:num`] DIGITSUM_DIV) THEN
  ASM_REWRITE_TAC[ARITH_RULE `1 < 2`; MULT_CLAUSES]);;

let BITSUM_BOUND = prove
 (`!s k. FINITE s
         ==> (nsum s (\i. 2 EXP i) < 2 EXP k <=> s SUBSET {i | i < k})`,
  SIMP_TAC[CONV_RULE(RAND_CONV SYM_CONV) (SPEC_ALL DIV_EQ_0); FINITE_RESTRICT;
           EXP_EQ_0; ARITH_EQ; NSUM_BITS_DIV; NSUM_EQ_0_IFF] THEN
  REWRITE_TAC[GSYM NOT_LE] THEN SET_TAC[]);;

let BITS_OF_NUM_SUBSET_NUMSEG_EQ = prove
 (`!n k. bits_of_num n SUBSET {i | i < k} <=> n < 2 EXP k`,
  SIMP_TAC[GSYM BITSUM_BOUND; FINITE_BITS_OF_NUM; NSUM_BITS_OF_NUM]);;


(* ------------------------------------------------------------------------- *)
(* Next is my work                                                           *)
(* ------------------------------------------------------------------------- *)
let NUM_EXP_LE = prove
  (`!x y. 1 <= y ==> x <= x EXP y`,
    GEN_TAC THEN INDUCT_TAC THEN SIMP_TAC[EXP; ARITH] THEN
    SIMP_TAC[ARITH_RULE `1 <= SUC y <=> y = 0 \/ 1 <= y`] THEN
    STRIP_TAC THEN ASM_SIMP_TAC[ARITH;EXP] THENL [ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC LE_TRANS THEN EXISTS_TAC `x * x:num` THEN
    ASM_SIMP_TAC[LE_SQUARE_REFL;LE_MULT_LCANCEL]);;

let is_qstate = new_definition
  `is_qstate (q:complex^M) <=> cnorm2 q = &1`;;

let finite_pow_tybij =
  let th = prove
   (`?x. x IN 1..(dimindex(:A) EXP dimindex(:B))`,
     EXISTS_TAC `1` THEN REWRITE_TAC[IN_NUMSEG; LE_REFL] THEN
     MESON_TAC[LE_1; DIMINDEX_GE_1; EXP_1;NUM_EXP_LE; LE_TRANS]) in
  new_type_definition "finite_pow" ("mk_finite_pow","dest_finite_pow") th;;

let FINITE_POW_IMAGE = prove
 (`UNIV:(A,B)finite_pow->bool =
       IMAGE mk_finite_pow (1..(dimindex(:A) EXP dimindex(:B)))`,
  REWRITE_TAC[EXTENSION; IN_UNIV; IN_IMAGE] THEN
  MESON_TAC[finite_pow_tybij]);;

let DIMINDEX_HAS_SIZE_FINITE_POW = prove
 (`(UNIV:(M,N)finite_pow->bool) HAS_SIZE (dimindex(:M) EXP dimindex(:N))`,
  SIMP_TAC[FINITE_POW_IMAGE] THEN
  MATCH_MP_TAC HAS_SIZE_IMAGE_INJ THEN
  ONCE_REWRITE_TAC[DIMINDEX_UNIV] THEN REWRITE_TAC[HAS_SIZE_NUMSEG_1] THEN
  MESON_TAC[finite_pow_tybij]);;

let DIMINDEX_FINITE_POW = prove
    (`dimindex (:(M,N)finite_pow) = dimindex (:M) EXP dimindex (:N)`,
    GEN_REWRITE_TAC LAND_CONV [dimindex] THEN
  REWRITE_TAC[REWRITE_RULE[HAS_SIZE] DIMINDEX_HAS_SIZE_FINITE_POW]);;

let FINITE_INDEX_INRANGE2 = prove
 (`!i. ?k. 1 <= k /\ k <= dimindex(:(2,N)finite_pow) /\
           (!x:A^(2,N)finite_pow. x$i = x$k) /\ (!y:B^(2,N)finite_pow. y$i = y$k)`,
  REWRITE_TAC[finite_index] THEN MESON_TAC[FINITE_INDEX_WORKS]);;

let cbasis = new_definition
  `cbasis k = vector_to_cvector(basis k :real^N) `;;

let CBASIS_COMPONENT = prove
 (`!k i. 1 <= k /\ k <= dimindex (:(2,N)finite_pow)
         ==> ((cbasis i :complex^(2,N)finite_pow)$k = if k = i then Cx(&1) else Cx(&0))`,
  SIMP_TAC[cbasis; LAMBDA_BETA;vector_to_cvector;vector_map;basis;COND_RAND] THEN MESON_TAC[]);;

let qstate_tybij =
  let th = prove
   (`?q:complex^(2,N)finite_pow. is_qstate q`,
     EXISTS_TAC `cbasis 1:complex^(2,N)finite_pow` THEN
    SIMP_TAC[is_qstate;CNORM2_ALT;cbasis;cdot] THEN
    SIMP_TAC[VECTOR_TO_CVECTOR_COMPONENT;BASIS_COMPONENT] THEN
    REWRITE_TAC[COND_RAND;CNJ_CX] THEN
    REWRITE_TAC[COND_RATOR;COMPLEX_MUL_LZERO; COMPLEX_MUL_RZERO]
    THEN REWRITE_TAC[COMPLEX_MUL_LID; COMPLEX_MUL_RID]
    THEN SIMP_TAC[VSUM_DELTA] THEN
    REWRITE_TAC[GSYM COMPLEX_VEC_0;VSUM_DELTA] THEN
    SIMP_TAC[IN_NUMSEG;LE_REFL;DIMINDEX_GE_1] THEN
    SIMP_TAC[COMPLEX_NORM_CX] THEN REAL_ARITH_TAC) in
  new_type_definition "qstate" ("mk_qstate","dest_qstate") th;;

let QSTATE_NORM = prove
(`!q:(N)qstate.
    cnorm2(dest_qstate q) = &1`,
MESON_TAC[is_qstate;qstate_tybij]);;

let DEST_QSTATE_EQ = prove
 (`!x y. dest_qstate x = dest_qstate y <=> x = y`,
  MESON_TAC[qstate_tybij]);;

let DEST_OF_QSTATE = prove
 (`!q:complex^(2,N)finite_pow. is_qstate q
         ==> dest_qstate(mk_qstate q) = q`,
  REPEAT STRIP_TAC THEN GEN_REWRITE_TAC I [GSYM qstate_tybij] THEN
  ASM_REWRITE_TAC[]);;


(* ------------------------------------------------------------------------- *)
(* Operation Definitions of Complex Matrix                                   *)
(* ------------------------------------------------------------------------- *)

overload_interface ("**",`(cmatrix_qstate_mul):complex^((2,N)finite_pow)^((2,M)finite_pow)->(N)qstate->(M)qstate`);;

overload_interface ("**",`(cmatrix_mul):complex^(2,N)finite_pow^(2,M)finite_pow->complex^(2,P)finite_pow^(2,N)finite_pow->complex^(2,P)finite_pow^(2,M)finite_pow`);;

let cmatrix_qstate_mul = new_definition
  `!q:(N)qstate A:complex^((2,N)finite_pow)^((2,M)finite_pow). A ** q  =
   mk_qstate (lambda i. vsum (1..dimindex (:(2,N)finite_pow)) (\j. A$i$j * dest_qstate q$j))`;;

let ctransp = new_definition
  `(ctransp:complex^(2,N)finite_pow^(2,M)finite_pow->complex^(2,M)finite_pow^(2,N)finite_pow) A
        = lambda i j. A$j$i`;;

let cmatrix_cnj = new_definition
    `(cmatrix_cnj:complex^(2,N)finite_pow^(2,M)finite_pow->complex^(2,N)finite_pow^(2,M)finite_pow) A = lambda i j. cnj(A$i$j)`;;

let cmatrix_mul = new_definition
    `!A:complex^(2,N)finite_pow^(2,M)finite_pow B:complex^(2,P)finite_pow^(2,N)finite_pow. A ** B =
    lambda i j. vsum(1..dimindex(:(2,N)finite_pow)) (\k. A$i$k * B$k$j)`;;

let id_cmatrix = new_definition
`id_cmatrix:complex^(2,N)finite_pow^(2,N)finite_pow =
                lambda i j.if i = j then Cx(&1) else Cx(&0)`;;

let hermitian_matrix = new_definition
    `(hermitian_matrix:complex^(2,N)finite_pow^(2,M)finite_pow->complex^(2,M)finite_pow^(2,N)finite_pow) A
      = lambda i j. cnj(A$j$i)`;;

let diagonal_cmatrix = new_definition
 `diagonal_cmatrix(A:complex^(2,N)finite_pow^(2,N)finite_pow) <=>
        !i j. 1 <= i /\ i <= dimindex(:(2,N)finite_pow) /\
              1 <= j /\ j <= dimindex(:(2,N)finite_pow) /\
              ~(i = j) ==> A$i$j = Cx(&0)`;;

let COND_LMUL = prove
 (`!b x1 x2 y. (if b then x1 else x2) * y = (if b then x1 * y else x2 * y)`,
  REPEAT GEN_TAC THEN BOOL_CASES_TAC `b:bool` THEN REWRITE_TAC[]);;

let COND_RMUL = prove
 (`!b x1 x2 y. y * (if b then x1 else x2) = (if b then y * x1 else y * x2)`,
  REPEAT GEN_TAC THEN BOOL_CASES_TAC `b:bool` THEN REWRITE_TAC[]);;

let COND_LMUL_0 = prove
 (`!b x y. (if b then x else &0) * y = (if b then x * y else &0)`,
  REPEAT GEN_TAC THEN BOOL_CASES_TAC `b:bool` THEN REWRITE_TAC[REAL_MUL_LZERO]);;

let COND_RMUL_0 = prove
 (`!b x y. y * (if b then x else &0) = (if b then y * x else &0)`,
  REPEAT GEN_TAC THEN BOOL_CASES_TAC `b:bool` THEN REWRITE_TAC[REAL_MUL_RZERO]);;

let COND_CNJ = prove
 (`!b x1 x2:complex. cnj(if b then x1 else x2) = (if b then cnj x1 else cnj x2)`,
  REPEAT GEN_TAC THEN BOOL_CASES_TAC `b:bool` THEN REWRITE_TAC[] THEN REWRITE_TAC[]);;

let VSUM_RESTRICT_ZERO = prove
 (`!P s f. vsum {x | x IN s /\ P x} f =
           vsum s (\x. if P x then f x else Cx(&0))`,
  SIMP_TAC[vsum; CART_EQ; LAMBDA_BETA; VEC_COMPONENT; SUM_RESTRICT_SET;
           COND_COMPONENT] THEN
           SIMP_TAC[DIMINDEX_2;FORALL_2;CX_DEF;complex;VECTOR_2]);;

let VSUM_DELTA_ALT = prove
 (`!s a. vsum s (\x. if x = a then b else Cx(&0)) =
         if a IN s then b else Cx(&0)`,
  SIMP_TAC[CART_EQ; LAMBDA_BETA; VSUM_COMPONENT; COND_COMPONENT] THEN
  SIMP_TAC[DIMINDEX_2;FORALL_2;CX_DEF;complex;VECTOR_2;SUM_DELTA]);;


(* ------------------------------------------------------------------------- *)
(* Basic properties of complex matrix.                                       *)
(* ------------------------------------------------------------------------- *)

let IDCMAT = prove
 (`!i j.
        1 <= i /\ i <= dimindex(:(2,N)finite_pow) /\
        1 <= j /\ j <= dimindex(:(2,N)finite_pow)
        ==> (id_cmatrix:complex^(2,N)finite_pow^(2,N)finite_pow)$i$j =
        if i = j then Cx(&1) else Cx(&0)`,
  REPEAT GEN_TAC THEN CHOOSE_TAC (SPEC_ALL FINITE_INDEX_INRANGE)
  THEN ASM_SIMP_TAC[id_cmatrix;LAMBDA_BETA]);;

let IDCMAT_HERMITIAN = prove
(`id_cmatrix = hermitian_matrix (id_cmatrix :complex^(2,N)finite_pow^(2,N)finite_pow)`,
SIMP_TAC[hermitian_matrix;cmatrix_cnj;id_cmatrix] THEN
SIMP_TAC[CART_EQ;LAMBDA_BETA;COND_CNJ;CNJ_CX] THEN MESON_TAC[]);;

let IDCMAT_DIAGONAL = prove
(`diagonal_cmatrix (id_cmatrix:complex^(2,N)finite_pow^(2,N)finite_pow)`,
SIMP_TAC[diagonal_cmatrix;id_cmatrix;LAMBDA_BETA] THEN MESON_TAC[]);;

let IDCMAT_UNITARY = prove
(`unitary_matrix (id_cmatrix: complex^(2,N)finite_pow^(2,N)finite_pow)`,
SIMP_TAC[unitary_matrix;GSYM IDCMAT_HERMITIAN;IDCMAT_DIAGONAL;CMATRIX_MUL_DIAGONAL] THEN
SIMP_TAC[id_cmatrix;CART_EQ;LAMBDA_BETA;COND_RMUL;COND_LMUL] THEN
SIMP_TAC[COMPLEX_MUL_RID;COMPLEX_MUL_RZERO]);;

let DIAGONAL_CMATRIX = prove
 (`!A:complex^(2,N)finite_pow^(2,N)finite_pow.
     diagonal_cmatrix A <=> A = (lambda i j. if i = j then A$i$j else Cx(&0))`,
  SIMP_TAC[CART_EQ; LAMBDA_BETA; diagonal_cmatrix] THEN MESON_TAC[]);;

let CTRANSP_COMPONENT = prove
 (`!A:complex^(2,N)finite_pow^(2,M)finite_pow i j. (ctransp A)$i$j = A$j$i`,
  REPEAT GEN_TAC THEN
  SUBGOAL_THEN `?k. 1 <= k /\ k <= dimindex(:(2,N)finite_pow) /\
                    (!A:complex^(2,M)finite_pow^(2,N)finite_pow. A$i = A$k) /\ (!z:complex^(2,N)finite_pow. z$i = z$k)`
  CHOOSE_TAC THENL [REWRITE_TAC[FINITE_INDEX_INRANGE2]; ALL_TAC] THEN
  SUBGOAL_THEN `?l. 1 <= l /\ l <= dimindex(:(2,M)finite_pow) /\
                    (!A:complex^(2,N)finite_pow^(2,M)finite_pow. A$j = A$l) /\ (!z:complex^(2,M)finite_pow. z$j = z$l)`
  CHOOSE_TAC THENL [REWRITE_TAC[FINITE_INDEX_INRANGE2]; ALL_TAC] THEN
  ASM_SIMP_TAC[ctransp; LAMBDA_BETA]);;

let CTRANSP_DIAGONAL_CMATRIX = prove
 (`!A:complex^(2,N)finite_pow^(2,N)finite_pow. diagonal_cmatrix A ==> ctransp A = A`,
  GEN_TAC THEN REWRITE_TAC[diagonal_cmatrix; CART_EQ; CTRANSP_COMPONENT] THEN
  STRIP_TAC THEN X_GEN_TAC `i:num` THEN STRIP_TAC THEN X_GEN_TAC `j:num` THEN
  STRIP_TAC THEN ASM_CASES_TAC `i:num = j` THEN ASM_SIMP_TAC[]);;

let CMATRIX_MUL_DIAGONAL = prove
 (`!A B:complex^(2,N)finite_pow^(2,N)finite_pow.
        diagonal_cmatrix A /\ diagonal_cmatrix B
        ==> A ** B = lambda i j. A$i$j * B$i$j`,
  REPEAT STRIP_TAC THEN
  REPEAT(FIRST_X_ASSUM(SUBST1_TAC o GEN_REWRITE_RULE I [DIAGONAL_CMATRIX])) THEN
  SIMP_TAC[CART_EQ; cmatrix_mul; LAMBDA_BETA] THEN
  ONCE_REWRITE_TAC[MESON[COMPLEX_MUL_LZERO; COMPLEX_MUL_RZERO]
   `(if p then a else Cx(&0)) * (if q then b else Cx(&0)) =
    if q then (if p then a * b else Cx(&0)) else Cx(&0)`] THEN
  SIMP_TAC[VSUM_DELTA_ALT; IN_NUMSEG; COND_ID;]);;

let HERMITIAN = prove
(`!A:complex^(2,N)finite_pow^(2,M)finite_pow. hermitian_matrix A = cmatrix_cnj (ctransp A)`,
SIMP_TAC[hermitian_matrix;cmatrix_cnj] THEN
SUBGOAL_THEN `?k. 1 <= k /\ k <= dimindex(:(2,N)finite_pow) /\
                    (!A:complex^(2,M)finite_pow^(2,N)finite_pow. A$i = A$k) /\ (!z:complex^(2,N)finite_pow. z$i = z$k)`
  CHOOSE_TAC THENL [REWRITE_TAC[FINITE_INDEX_INRANGE2]; ALL_TAC] THEN
  SUBGOAL_THEN `?l. 1 <= l /\ l <= dimindex(:(2,M)finite_pow) /\
                    (!A:complex^(2,N)finite_pow^(2,M)finite_pow. A$j = A$l) /\ (!z:complex^(2,M)finite_pow. z$j = z$l)`
  CHOOSE_TAC THENL [REWRITE_TAC[FINITE_INDEX_INRANGE2]; ALL_TAC] THEN
  ASM_SIMP_TAC[ctransp;CART_EQ;LAMBDA_BETA]);;

(* ------------------------------------------------------------------------- *)
(* Unitary matrix.                                                           *)
(* ------------------------------------------------------------------------- *)

let unitary_matrix = new_definition
  `unitary_matrix (U:complex^(2,N)finite_pow^(2,N)finite_pow) <=>
     hermitian_matrix U ** U = id_cmatrix /\ U ** hermitian_matrix U = id_cmatrix`;;

let UNITARY_ORTHOGONAL_THM = prove
(`!A:complex^(2,N)finite_pow^(2,N)finite_pow.
unitary_matrix A ==> (!x y. 1 <= x /\ x <= dimindex(:(2,N)finite_pow)
/\ 1 <= y /\ y <= dimindex(:(2,N)finite_pow)
==> vsum(1..dimindex(:(2,N)finite_pow)) (\i. A$i$x * cnj (A$i$y)) =
if x = y then Cx(&1) else Cx(&0))`,
SIMP_TAC[CART_EQ;LAMBDA_BETA;unitary_matrix;hermitian_matrix;cmatrix_mul;LAMBDA_BETA;id_cmatrix]
THEN SIMP_TAC[COND_COMPONENT;CX_DEF;complex;DIMINDEX_2;FORALL_2;VECTOR_2]
THEN SIMP_TAC[SIMPLE_COMPLEX_ARITH`A$i$x * cnj (A$i$y) = cnj (A$i$y) * A$i$x`]
THEN ARITH_TAC);;

let UNITARITY = prove
(`!A:complex^(2,N)finite_pow^(2,N)finite_pow q:(N)qstate.
     unitary_matrix A ==>
     cnorm2((lambda i. vsum (1..dimindex (:(2,N)finite_pow))
                (\j. A$i$j * dest_qstate q$j)):complex^(2,N)finite_pow) = &1`,
REPEAT GEN_TAC THEN SIMP_TAC[cnorm2;REAL_CDOT_SELF;REAL_OF_COMPLEX_RE;cdot; LAMBDA_BETA] THEN
SIMP_TAC[FINITE_NUMSEG;CNJ_VSUM;CNJ_MUL] THEN SIMP_TAC[BILINEAR_COMPLEX_MUL;FINITE_NUMSEG;BILINEAR_VSUM] THEN
SIMP_TAC[SIMPLE_COMPLEX_ARITH`(a * b) * c * d = a * c * b * d:complex`] THEN SIMP_TAC[FORALL_UNPAIR_THM] THEN
SUBGOAL_THEN`FINITE(1..dimindex (:(2,N)finite_pow)) /\ FINITE
  ((1..dimindex (:(2,N)finite_pow)) CROSS
           (1..dimindex (:(2,N)finite_pow)))  `ASSUME_TAC THENL
[SIMP_TAC[FINITE_NUMSEG;FINITE_CROSS];ALL_TAC] THEN
FIRST_X_ASSUM(ASSUME_TAC o MATCH_MP (SPEC_ALL  VSUM_SWAP)) THEN ASM_SIMP_TAC[]
THEN SIMP_TAC[SIMPLE_COMPLEX_ARITH`a * b * c * d = (c * d) * a * b:complex`]
THEN SIMP_TAC[FINITE_NUMSEG;VSUM_COMPLEX_LMUL] THEN SIMP_TAC[LAMBDA_PAIR_THM] THEN
POP_ASSUM (K ALL_TAC) THEN STRIP_TAC THEN FIRST_X_ASSUM(ASSUME_TAC o MATCH_MP UNITARY_ORTHOGONAL_THM) THEN
RULE_ASSUM_TAC(SIMP_RULE[TAUT`a /\ b /\ c /\ d <=> (a /\ b) /\ c /\ d`]) THEN SIMP_TAC[IN_NUMSEG;CROSS] THEN
SUBGOAL_THEN `(Re(vsum
  {x,y | (1 <= x /\ x <= dimindex (:(2,N)finite_pow)) /\
         1 <= y /\ y <= dimindex (:(2,N)finite_pow)}
 (\(x,y). (dest_qstate (q:(N)qstate)$x * cnj (dest_qstate q$y)) *
          vsum (1..dimindex (:(2,N)finite_pow)) (\i. (A:complex^(2,N)finite_pow^(2,N)finite_pow)$i$x * cnj (A$i$y)))) = &1)  =
 (Re(vsum {x,y | (1 <= x /\ x <= dimindex (:(2,N)finite_pow)) /\
         1 <= y /\ y <= dimindex (:(2,N)finite_pow)}
 (\(x,y). (dest_qstate q$x * cnj (dest_qstate q$y)) *
        (if x = y then Cx (&1) else Cx (&0)))) = &1)` SUBST1_TAC THENL
[AP_THM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN RULE_ASSUM_TAC(SIMP_RULE[GSYM IN_NUMSEG]) THEN
SIMP_TAC[GSYM IN_NUMSEG;GSYM CROSS] THEN MATCH_MP_TAC VSUM_EQ
THEN ASM_SIMP_TAC[FORALL_IN_CROSS];ALL_TAC] THEN POP_ASSUM (K ALL_TAC) THEN ONCE_REWRITE_TAC[COND_RAND;COND_RATOR] THEN
SIMP_TAC[COMPLEX_MUL_RID;COMPLEX_MUL_RZERO] THEN ASSUME_TAC (SPEC_ALL QSTATE_NORM) THEN
RULE_ASSUM_TAC(SIMP_RULE[cnorm2;REAL_CDOT_SELF;REAL_OF_COMPLEX_RE;cdot]) THEN
SIMP_TAC[GSYM IN_NUMSEG;FINITE_NUMSEG;GSYM VSUM_VSUM_PRODUCT] THEN SIMP_TAC[GSYM VSUM_RESTRICT_ZERO]
THEN SIMP_TAC[SET_RULE`x IN 1.. dimindex(:(2,N)finite_pow) ==>
    {y | y IN 1..dimindex (:(2,N)finite_pow) /\ x = y} = {x}`] THEN ASM_SIMP_TAC[VSUM_SING]);;

let IDCMAT_MUL_QSTATE = prove
(`!q:(N)qstate. id_cmatrix:complex^(2,N)finite_pow^(2,N)finite_pow ** q = q`,
GEN_TAC THEN SIMP_TAC[cmatrix_qstate_mul] THEN REWRITE_TAC[GSYM DEST_QSTATE_EQ] THEN
ASSUME_TAC (SPEC_ALL IDCMAT_UNITARY) THEN FIRST_X_ASSUM(ASSUME_TAC o MATCH_MP (SPEC_ALL UNITARITY))
THEN RULE_ASSUM_TAC(SIMP_RULE[GSYM is_qstate]) THEN FIRST_X_ASSUM(ASSUME_TAC o MATCH_MP (SPEC_ALL DEST_OF_QSTATE))
THEN ASM_SIMP_TAC[CART_EQ;LAMBDA_BETA;IDCMAT] THEN SIMP_TAC[COND_LMUL;COMPLEX_MUL_LID;COMPLEX_MUL_LZERO]
THEN REPEAT STRIP_TAC THEN GEN_REWRITE_TAC(LAND_CONV o ONCE_DEPTH_CONV)[EQ_SYM_EQ]
THEN ASM_SIMP_TAC[VSUM_DELTA_ALT;IN_NUMSEG]);;

let IDCMAT_MUL_MAT = prove
(`!A:complex^(2,N)finite_pow^(2,N)finite_pow.
id_cmatrix:complex^(2,N)finite_pow^(2,N)finite_pow ** A = A`,
GEN_TAC THEN SIMP_TAC[cmatrix_mul;CART_EQ;LAMBDA_BETA;IDCMAT] THEN
SIMP_TAC[COND_LMUL;COMPLEX_MUL_LID;COMPLEX_MUL_LZERO] THEN REPEAT STRIP_TAC THEN
GEN_REWRITE_TAC(LAND_CONV o ONCE_DEPTH_CONV)[EQ_SYM_EQ]
THEN ASM_SIMP_TAC[VSUM_DELTA_ALT;IN_NUMSEG]);;


(* ------------------------------------------------------------------------- *)
(* Hadamard gate.                                                            *)
(* ------------------------------------------------------------------------- *)

let hadamard = new_definition
  `hadamard : complex^(2,1)finite_pow^(2,1)finite_pow = lambda i j.
     if i = 1 /\ j = 1 then Cx(&1 / sqrt(&2)) else
     if i = 1 /\ j = 2 then Cx(&1 / sqrt(&2)) else
     if i = 2 /\ j = 1 then Cx(&1 / sqrt(&2)) else
     if i = 2 /\ j = 2 then --Cx(&1 / sqrt(&2)) else Cx(&0)`;;

let HADAMARD_HERMITIAN = prove
(` hermitian_matrix hadamard = hadamard `,
SIMP_TAC[hermitian_matrix;hadamard] THEN
 SIMP_TAC[CART_EQ;LAMBDA_BETA] THEN
SIMP_TAC[COND_CNJ;GSYM CX_NEG;CNJ_CX] THEN MESON_TAC[]);;

let ONE_DIV_SQRT2 = prove
(`(&1 / sqrt (&2)) pow 2 = &1 / &2`,
GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV)[GSYM SQRT_1]
THEN SIMP_TAC[GSYM SQRT_DIV;REAL_SQRT_POW_2] THEN REAL_ARITH_TAC);;

let ONE_DIV_SQRTN = prove
(`!N. 1 <= N ==> (&1 / sqrt (&N)) pow 2 = &1 / &N`,
REPEAT STRIP_TAC THEN
GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV)[GSYM SQRT_1]
THEN SIMP_TAC[GSYM SQRT_DIV] THEN SIMP_TAC[REAL_SQRT_POW_2]
THEN SIMP_TAC[REAL_ABS_DIV] THEN SIMP_TAC[REAL_ARITH`abs(&1) = &1`]
THEN AP_TERM_TAC THEN REAL_ARITH_TAC);;

let HADAMARD_UNITARY = prove
(`unitary_matrix hadamard`,
SIMP_TAC[unitary_matrix;HADAMARD_HERMITIAN;cmatrix_mul;hadamard;id_cmatrix]
THEN SIMP_TAC[CART_EQ;LAMBDA_BETA;COND_LMUL;COND_RMUL] THEN
SIMP_TAC[COMPLEX_MUL_LZERO;COMPLEX_MUL_RZERO;COMPLEX_MUL_RNEG;COMPLEX_NEG_0;COMPLEX_MUL_LNEG;COMPLEX_NEG_MUL2]
THEN SIMP_TAC[COND_ID;GSYM CX_MUL;GSYM REAL_POW_2;ONE_DIV_SQRT2;SQRT_1] THEN
SIMP_TAC[REAL_ARITH`(&1 / &1) pow 1= &1`] THEN SIMP_TAC[REAL_ARITH`(&1 / &1) = &1`] THEN
SIMP_TAC[DIMINDEX_FINITE_POW;DIMINDEX_2;DIMINDEX_1;ARITH_RULE`2 EXP 1 = 2`;VSUM_2]
THEN ONCE_SIMP_TAC[FORALL_2;COND_CLAUSES] THEN ONCE_SIMP_TAC[FORALL_2;COND_CLAUSES]
THEN ONCE_SIMP_TAC[COND_T_F;COND_RIGHT_F] THEN SIMP_TAC[COND_T_F;COND_RIGHT_F]
THEN SIMP_TAC[COND_RAND;COND_RATOR] THEN SIMP_TAC[GSYM CX_ADD;REAL_ARITH`&1 / &2  + &1/ &2 = &1`]
THEN SIMP_TAC[REAL_ARITH`&1 / &1  + &1/ &1 = &2`] THEN
SIMP_TAC[GSYM CX_NEG;GSYM CX_ADD;REAL_ARITH`&1 / &2 + -- (&1/ &2) = &0`]
THEN MESON_TAC[]);;


(* ------------------------------------------------------------------------- *)
(* To inductively prove the unitary property of the N-fold Hadamard gate.    *)                                                         *)
(* ------------------------------------------------------------------------- *)

let OFFSET_IMAGE = prove
(`!c m:num. {k |k IN c + 1..c + m /\ P k}  = IMAGE(\x.x + c) {k | k IN 1..m /\ P (k + c)}`,
REPEAT GEN_TAC THEN
SIMP_TAC[IN_NUMSEG;ARITH_RULE`c+1 <= k /\ k <= c+m <=> 1 <= k - c /\ k - c <= m`]
THEN SIMP_TAC[IN_ELIM_THM;EXTENSION;IN_NUMSEG;IN_IMAGE] THEN
GEN_TAC THEN EQ_TAC THENL[REPEAT STRIP_TAC THEN EXISTS_TAC`x - c:num`
THEN ASM_SIMP_TAC[ARITH_RULE`1 <= x-c ==>x- c + c = x`];ALL_TAC]
THEN STRIP_TAC THEN ASM_SIMP_TAC[ARITH_RULE`(x' + c) - c:num  =  x'`]);;

let CARD_IMAGE_EQ = prove
(`!s c:num.FINITE s ==> CARD(IMAGE (\x. x + c) s) = CARD s`,
REPEAT STRIP_TAC THEN MATCH_MP_TAC CARD_IMAGE_INJ THEN
ASM_SIMP_TAC[] THEN MESON_TAC[ARITH_RULE`x + c:num = y + c ==> x = y`]);;

let POW_REFL = prove
(`&2 pow dimindex (:N) / &2 pow dimindex (:N) = &1`,
ASSUME_TAC REAL_POW_LT THEN
FIRST_X_ASSUM (ASSUME_TAC o SPECL[`&2`;`dimindex(:N)`]) THEN
RULE_ASSUM_TAC(SIMP_RULE[REAL_ARITH`&0 < &2`]) THEN
ASM_SIMP_TAC[REAL_FIELD`&0 < a ==> a / a = &1`]);;

let BITSET_ADD = prove
(`!k n:num. k < 2 EXP n ==> bitset (k + 2 EXP n) = bitset (k) UNION {n}`,
REPEAT GEN_TAC THEN STRIP_TAC THEN SIMP_TAC[BITSET_EQ_BITSNUM] THEN
ASSUME_TAC (SPEC`n:num` (GSYM BITS_OF_NUM_POW2)) THEN
SUBGOAL_THEN`DISJOINT (bits_of_num k) {n:num}` ASSUME_TAC
THENL [SIMP_TAC[DISJOINT_SING] THEN UNDISCH_TAC`k < 2 EXP n`
THEN SIMP_TAC[GSYM BITS_OF_NUM_SUBSET_NUMSEG_EQ] THEN
SIMP_TAC[SUBSET;IN_ELIM_THM] THEN MESON_TAC[LT_REFL];ALL_TAC]
THEN POP_ASSUM MP_TAC THEN ASM_SIMP_TAC[BITS_OF_NUM_ADD;BITSET_EQ_BITSNUM]);;

let BITS_OF_NUM_1 = prove
 (`bits_of_num 1 = {0}`,
  REWRITE_TAC[GSYM BITS_OF_NUM_POW2; EXP]);;

let bitand = new_definition
`!a b:num. bitand a b = (bitset a) INTER (bitset b)`;;

let BITAND_0 = prove
(`!a:num. CARD(bitand a 0) = 0 /\
CARD(bitand 0 a) = 0`,
SIMP_TAC[bitand;BITSET_0;INTER_EMPTY;CARD_CLAUSES]);;

let BITAND_SYM = prove
(`!a b:num. bitand a b = bitand b a`,
SIMP_TAC[bitand] THEN SET_TAC[]);;

let BITAND_ODD_CARD = prove
(`!N c:num.
  0 < c /\ c < 2 EXP N /\ 0 < N ==> CARD {k | k IN 1..2 EXP N /\
       ODD(CARD (bitand c (k - 1)))} = 2 EXP (N -1)`,
INDUCT_TAC THENL[ARITH_TAC;ALL_TAC]
 THEN REPEAT STRIP_TAC THEN POP_ASSUM MP_TAC
THEN SIMP_TAC[ARITH_RULE`0 < SUC N`] THEN
SIMP_TAC[EXP;bitand;ARITH_RULE`2 * 2 EXP N = 2 EXP N + 2 EXP N`]
THEN ASSUME_TAC(ARITH_RULE`1 <= (2 EXP N) + 1 /\ 2 EXP N <= 2 EXP N + 2 EXP N`)
THEN FIRST_X_ASSUM(ASSUME_TAC o MATCH_MP (SPECL[`1`;`2 EXP N`;`2 EXP N + 2 EXP N`] (GSYM NUMSEG_COMBINE_R)))
THEN ASM_SIMP_TAC[UNION_RESTRICT] THEN SUBGOAL_THEN`{k | k IN 1..2 EXP N /\ ODD (CARD (bitset c INTER bitset (k - 1)))}
  INTER {k | k IN 2 EXP N + 1..2 EXP N + 2 EXP N /\
             ODD (CARD (bitset c INTER bitset (k - 1)))} = {}`ASSUME_TAC
THENL[SUBGOAL_THEN`2 EXP N < 2 EXP N + 1 ==> DISJOINT(1..2 EXP N) (2 EXP N + 1..2 EXP N + 2 EXP N)`ASSUME_TAC
 THENL [MESON_TAC[GSYM DISJOINT_NUMSEG];ALL_TAC] THEN
RULE_ASSUM_TAC(SIMP_RULE[ARITH_RULE`2 EXP N < 2 EXP N +1`]) THEN
ASM_SIMP_TAC[GSYM DISJOINT;SET_RULE `DISJOINT s t ==> DISJOINT {x | x IN s /\ P x} {x | x IN t /\ P x}`];ALL_TAC]
THEN ASM_SIMP_TAC[FINITE_NUMSEG;FINITE_RESTRICT;CARD_UNION] THEN
SIMP_TAC[OFFSET_IMAGE;FINITE_NUMSEG;FINITE_RESTRICT;CARD_IMAGE_EQ] THEN
SIMP_TAC[IN_NUMSEG] THEN SUBGOAL_THEN `{k | (1 <= k /\ k <= 2 EXP N) /\
          ODD (CARD (bitset c INTER bitset ((k + 2 EXP N) - 1)))} =
          {k | (1 <= k /\ k <= 2 EXP N) /\
          ODD (CARD (bitset c INTER bitset ((k - 1) + 2 EXP N)))} `SUBST1_TAC
THENL[SIMP_TAC[EXTENSION;IN_ELIM_THM] THEN GEN_TAC THEN EQ_TAC THENL[STRIP_TAC THEN
POP_ASSUM MP_TAC THEN ASM_SIMP_TAC[ARITH_RULE`1 <= x ==> (x + 2 EXP N) - 1 = x - 1 + 2 EXP N`];
ALL_TAC] THEN STRIP_TAC THEN ASM_SIMP_TAC[ARITH_RULE`1 <= x ==> (x + 2 EXP N) - 1 = x - 1 + 2 EXP N`];
ALL_TAC] THEN SUBGOAL_THEN`{k | (1 <= k /\ k <= 2 EXP N) /\
      ODD (CARD (bitset c INTER bitset (k - 1 + 2 EXP N)))} = {k | (1 <= k /\ k <= 2 EXP N) /\
  ODD (CARD (bitset c INTER (bitset (k - 1) UNION {N})))}`SUBST1_TAC
THENL[SIMP_TAC[EXTENSION;IN_ELIM_THM] THEN GEN_TAC THEN EQ_TAC THENL [STRIP_TAC THEN ASM_SIMP_TAC[] THEN
MP_TAC (SPECL[`x-1`;`N:num`] BITSET_ADD) THEN ASM_SIMP_TAC[ARITH_RULE`1 <= x /\ x <= 2 EXP N ==> x - 1 < 2 EXP N`]
THEN STRIP_TAC THEN UNDISCH_TAC`ODD (CARD (bitset c INTER bitset (x - 1 + 2 EXP N)))` THEN
ASM_SIMP_TAC[];ALL_TAC] THEN STRIP_TAC THEN MP_TAC (SPECL[`x-1`;`N:num`] BITSET_ADD) THEN
ASM_SIMP_TAC[ARITH_RULE`1 <= x /\ x <= 2 EXP N ==> x - 1 < 2 EXP N`];ALL_TAC] THEN
SIMP_TAC[UNION_OVER_INTER;ARITH_RULE`SUC N - 1 = N`] THEN ASM_CASES_TAC` c < 2 EXP N /\0 < N`
THENL[FIRST_X_ASSUM(MP_TAC o SPEC`c:num`) THEN ASM_SIMP_TAC[IN_NUMSEG;bitand;BITSET_EQ_BITSNUM]
THEN ASSUME_TAC(SPEC`c:num` BITS_OF_NUM_SUBSET_NUMSEG_LT) THEN
SUBGOAL_THEN`bits_of_num c INTER {N} = {}`SUBST1_TAC THENL[POP_ASSUM MP_TAC
THEN UNDISCH_TAC`c < 2 EXP N /\ 0 < N` THEN REPEAT STRIP_TAC THEN ASSUME_TAC(SPEC`N:num` BITS_OF_NUM_POW2)
THEN SIMP_TAC[GSYM DISJOINT] THEN SIMP_TAC[DISJOINT_SING] THEN
MP_TAC(SPECL[`c:num`;`N:num`] (GSYM BITS_OF_NUM_SUBSET_NUMSEG_EQ))THEN ASM_SIMP_TAC[] THEN SET_TAC[LT_REFL];ALL_TAC] THEN SIMP_TAC[UNION_EMPTY;ARITH_RULE`(a:num) + a = 2 * a`] THEN
GEN_REWRITE_TAC(RAND_CONV o LAND_CONV o LAND_CONV o ONCE_DEPTH_CONV)[ARITH_RULE`2 = (2 EXP 1)`]
THEN ASM_SIMP_TAC[GSYM EXP_ADD;ARITH_RULE`0 < N ==> 1 + N - 1 = N`];ALL_TAC]
THEN UNDISCH_TAC`~(c < 2 EXP N /\ 0 < N)` THEN SIMP_TAC[DE_MORGAN_THM;ARITH_RULE`~(a < b:num) <=> b <= a`]
THEN ONCE_SIMP_TAC[TAUT`P \/ Q <=> Q \/ P`] THEN STRIP_TAC
THENL[RULE_ASSUM_TAC(SIMP_RULE[ARITH_RULE`N <= 0 <=> N = 0`])
THEN UNDISCH_TAC`c < 2 EXP SUC N` THEN ASM_SIMP_TAC[EXP;ARITH] THEN UNDISCH_TAC`0 < c`
THEN SIMP_TAC[GSYM IMP_CONJ;ARITH_RULE`0 < c /\ c < 2 <=> c = 1`] THEN
SIMP_TAC[GSYM IN_NUMSEG;NUMSEG_SING;IN_SING]
THEN ONCE_REWRITE_TAC[SET_RULE `{x | x = a /\ P x} = {x | x = a /\ P a}`]
THEN SIMP_TAC[ARITH;BITSET_0] THEN SIMP_TAC[BITSET_EQ_BITSNUM;BITS_OF_NUM_1;INTER_EMPTY]
THEN SIMP_TAC[INTER_IDEMPOT;CARD_SING;CARD_CLAUSES;UNION_EMPTY] THEN SIMP_TAC[ODD;ARITH_RULE`ODD 1 <=> T`]
THEN SIMP_TAC[SET_RULE `{k |k = a} = {a:num}`;CARD_SING;SET_RULE`{k | F} = {}`;CARD_CLAUSES;ARITH];ALL_TAC]
THEN FIRST_X_ASSUM(MP_TAC o SPEC`c - 2 EXP N `) THEN
SIMP_TAC[ARITH_RULE`0 < c - a <=> a < c`] THEN SIMP_TAC[ARITH_RULE`c - 2 EXP N  < 2 EXP N  <=> c < 2 EXP N + 2 EXP N`]
THEN SIMP_TAC[GSYM MULT_2;ARITH_RULE`2 * 2 EXP N = 2 EXP 1 * 2 EXP N `;GSYM EXP_ADD] THEN
ASM_SIMP_TAC[ARITH_RULE`1 + N = SUC N`;bitand;IN_NUMSEG] THEN
POP_ASSUM MP_TAC THEN SIMP_TAC[ARITH_RULE`2 EXP N <= c <=> 2 EXP N < c \/ 2 EXP N = c`]
THEN STRIP_TAC THENL[ASM_CASES_TAC`~(0 < N)` THENL[RULE_ASSUM_TAC(SIMP_RULE[ARITH_RULE`~(0 < N) <=> N = 0`])
THEN ASM_SIMP_TAC[ARITH;GSYM IN_NUMSEG;NUMSEG_SING;IN_SING] THEN UNDISCH_TAC`2 EXP N < c`
THEN UNDISCH_TAC`c < 2 EXP SUC N` THEN ASM_SIMP_TAC[EXP;ARITH] THEN SIMP_TAC[GSYM IMP_CONJ]
THEN SIMP_TAC[ARITH_RULE`c < 2 /\ 1 < c <=> F`];ALL_TAC]
THEN RULE_ASSUM_TAC(SIMP_RULE[TAUT`~ ~ P <=> P`])
THEN ASM_SIMP_TAC[] THEN ASSUME_TAC(SPECL[`c - 2 EXP N`;`N:num`] BITSET_ADD) THEN
RULE_ASSUM_TAC(SIMP_RULE[ARITH_RULE`c - 2 EXP N  < 2 EXP N  <=> c < 2 EXP N + 2 EXP N`]) THEN
RULE_ASSUM_TAC(SIMP_RULE[GSYM MULT_2;ARITH_RULE`2 * 2 EXP N = 2 EXP 1 * 2 EXP N `;GSYM EXP_ADD])
THEN RULE_ASSUM_TAC(SIMP_RULE[ARITH_RULE`1 + N = SUC N`]) THEN POP_ASSUM MP_TAC THEN
ASM_SIMP_TAC[] THEN REPEAT STRIP_TAC THEN UNDISCH_TAC`bitset (c - 2 EXP N + 2 EXP N) = bitset (c - 2 EXP N) UNION {N}`
THEN SUBGOAL_THEN`bitset (c - 2 EXP N + 2 EXP N) = bitset c`SUBST1_TAC THENL
[ASM_SIMP_TAC[ARITH_RULE`2 EXP N < c ==> c - 2 EXP N + 2 EXP N = c`];ALL_TAC] THEN
STRIP_TAC THEN SUBGOAL_THEN`bitset c INTER {N} = {N}`ASSUME_TAC THENL
[SIMP_TAC[INTER;IN_ELIM_THM;EXTENSION] THEN ASM_SIMP_TAC[IN_UNION] THEN
SET_TAC[];ALL_TAC] THEN POP_ASSUM MP_TAC THEN SIMP_TAC[] THEN STRIP_TAC THEN
SIMP_TAC[UNION_COMM;INTER_OVER_UNION] THEN ASM_SIMP_TAC[] THEN SIMP_TAC[UNION_COMM]
THEN SIMP_TAC[SET_RULE`s UNION s UNION t = s UNION t`] THEN
GEN_REWRITE_TAC(LAND_CONV o LAND_CONV o ONCE_DEPTH_CONV)[INTER_COMM]
THEN GEN_REWRITE_TAC(LAND_CONV o LAND_CONV o DEPTH_CONV)[UNION_OVER_INTER]
THEN SUBGOAL_THEN`{k | (1 <= k /\ k <= 2 EXP N) /\
      ODD(CARD
      (bitset (k - 1) INTER {N} UNION
       bitset (k - 1) INTER bitset (c - 2 EXP N)))} =
       {k | (1 <= k /\ k <= 2 EXP N) /\
      ODD(CARD(bitset (c - 2 EXP N) INTER bitset (k - 1)))}`SUBST1_TAC
THENL[SIMP_TAC[EXTENSION;IN_ELIM_THM] THEN GEN_TAC THEN EQ_TAC THENL[STRIP_TAC THEN ASM_SIMP_TAC[]
THEN POP_ASSUM MP_TAC THEN SUBGOAL_THEN`bitset (x - 1) INTER {N} = {}`ASSUME_TAC
THENL[ASSUME_TAC(SPEC`N:num` BITS_OF_NUM_POW2) THEN SIMP_TAC[BITSET_EQ_BITSNUM;GSYM DISJOINT]
THEN SIMP_TAC[DISJOINT_SING] THEN MP_TAC(SPECL[`x-1`;`N:num`] (GSYM BITS_OF_NUM_SUBSET_NUMSEG_EQ))
THEN UNDISCH_TAC`x <= 2 EXP N` THEN UNDISCH_TAC`1 <= x` THEN
SIMP_TAC[ARITH_RULE`1 <= x ==> x <= 2 EXP N ==> x - 1  < 2 EXP N`] THEN
SET_TAC[LT_REFL];ALL_TAC] THEN ASM_SIMP_TAC[UNION_EMPTY;INTER_COMM];ALL_TAC] THEN
SIMP_TAC[] THEN STRIP_TAC THEN SUBGOAL_THEN`bitset (x - 1) INTER {N} = {}`SUBST1_TAC THENL
[ASSUME_TAC(SPEC`N:num` BITS_OF_NUM_POW2) THEN SIMP_TAC[BITSET_EQ_BITSNUM;GSYM DISJOINT]
THEN SIMP_TAC[DISJOINT_SING] THEN MP_TAC(SPECL[`x-1`;`N:num`] (GSYM BITS_OF_NUM_SUBSET_NUMSEG_EQ))
THEN UNDISCH_TAC`x <= 2 EXP N` THEN UNDISCH_TAC`1 <= x` THEN
SIMP_TAC[ARITH_RULE`1 <= x ==> x <= 2 EXP N ==> x - 1  < 2 EXP N`] THEN
SET_TAC[LT_REFL];ALL_TAC] THEN ASM_SIMP_TAC[UNION_EMPTY;INTER_COMM];ALL_TAC]
THEN ASM_SIMP_TAC[] THEN UNDISCH_TAC`bitset c = bitset (c - 2 EXP N) UNION {N}` THEN
GEN_REWRITE_TAC(LAND_CONV o ONCE_DEPTH_CONV)[EQ_SYM_EQ] THEN SIMP_TAC[UNION_COMM]
THEN STRIP_TAC THEN ASM_SIMP_TAC[UNION_OVER_INTER] THEN
POP_ASSUM MP_TAC THEN GEN_REWRITE_TAC(LAND_CONV o ONCE_DEPTH_CONV)[EQ_SYM_EQ]
THEN SIMP_TAC[] THEN ONCE_REWRITE_TAC[INTER_COMM] THEN SIMP_TAC[UNION_OVER_INTER]
THEN STRIP_TAC THEN SUBGOAL_THEN`{k | (1 <= k /\ k <= 2 EXP N) /\
      ODD(CARD({N} UNION bitset (k - 1) INTER {N} UNION
       bitset (k - 1) INTER bitset (c - 2 EXP N)))} =
       {k | (1 <= k /\ k <= 2 EXP N) /\
      ODD(CARD({N} UNION bitset (k - 1) INTER bitset (c - 2 EXP N)))}`SUBST1_TAC
THENL[SIMP_TAC[EXTENSION;IN_ELIM_THM] THEN GEN_TAC THEN EQ_TAC THENL[STRIP_TAC THEN ASM_SIMP_TAC[]
THEN POP_ASSUM MP_TAC THEN SUBGOAL_THEN`bitset (x - 1) INTER {N} = {}`ASSUME_TAC
THENL[ASSUME_TAC(SPEC`N:num` BITS_OF_NUM_POW2) THEN SIMP_TAC[BITSET_EQ_BITSNUM;GSYM DISJOINT]
THEN SIMP_TAC[DISJOINT_SING] THEN MP_TAC(SPECL[`x-1`;`N:num`] (GSYM BITS_OF_NUM_SUBSET_NUMSEG_EQ))
THEN UNDISCH_TAC`x <= 2 EXP N` THEN UNDISCH_TAC`1 <= x` THEN
SIMP_TAC[ARITH_RULE`1 <= x ==> x <= 2 EXP N ==> x - 1  < 2 EXP N`] THEN
SET_TAC[LT_REFL];ALL_TAC] THEN ASM_SIMP_TAC[UNION_EMPTY;INTER_COMM];ALL_TAC] THEN
SIMP_TAC[] THEN STRIP_TAC THEN SUBGOAL_THEN`bitset (x - 1) INTER {N} = {}`SUBST1_TAC THENL
[ASSUME_TAC(SPEC`N:num` BITS_OF_NUM_POW2) THEN SIMP_TAC[BITSET_EQ_BITSNUM;GSYM DISJOINT]
THEN SIMP_TAC[DISJOINT_SING] THEN MP_TAC(SPECL[`x-1`;`N:num`] (GSYM BITS_OF_NUM_SUBSET_NUMSEG_EQ))
THEN UNDISCH_TAC`x <= 2 EXP N` THEN UNDISCH_TAC`1 <= x` THEN
SIMP_TAC[ARITH_RULE`1 <= x ==> x <= 2 EXP N ==> x - 1  < 2 EXP N`] THEN
SET_TAC[LT_REFL];ALL_TAC] THEN ASM_SIMP_TAC[UNION_EMPTY];ALL_TAC]
THEN SIMP_TAC[INTER_COMM] THEN SUBGOAL_THEN`{k | (1 <= k /\ k <= 2 EXP N) /\
      ODD (CARD ({N} UNION bitset (c - 2 EXP N) INTER bitset (k - 1)))}
  = {k | (1 <= k /\ k <= 2 EXP N) /\
  ODD(CARD {N}  + CARD(bitset (c - 2 EXP N) INTER bitset (k - 1)))}`SUBST1_TAC
THENL[SIMP_TAC[EXTENSION;IN_ELIM_THM] THEN GEN_TAC THEN REPEAT AP_TERM_TAC
THEN MATCH_MP_TAC CARD_UNION THEN SIMP_TAC[FINITE_BITSET;FINITE_INTER;FINITE_SING] THEN
ASSUME_TAC(SPEC`N:num` BITS_OF_NUM_POW2) THEN SIMP_TAC[BITSET_EQ_BITSNUM;GSYM DISJOINT]
THEN SIMP_TAC[DISJOINT_SING] THEN MP_TAC(SPECL[`c - 2 EXP N`;`N:num`] (GSYM BITS_OF_NUM_SUBSET_NUMSEG_EQ))
THEN UNDISCH_TAC`c < 2 EXP SUC N` THEN UNDISCH_TAC`2 EXP N < c` THEN
SIMP_TAC[ARITH_RULE`c - 2 EXP N  < 2 EXP N <=> c < 2 EXP N + 2 EXP N`]
THEN SIMP_TAC[ARITH_RULE`SUC N = 1 + N`;EXP_ADD;EXP_1;MULT_2] THEN
SET_TAC[LT_REFL];ALL_TAC] THEN SIMP_TAC[CARD_SING] THEN
SUBGOAL_THEN`{k | (1 <= k /\ k <= 2 EXP N) /\
      ODD (1 + CARD (bitset (c - 2 EXP N) INTER bitset (k - 1)))}  =
  {k | (1 <= k /\ k <= 2 EXP N) /\
      EVEN (CARD (bitset (c - 2 EXP N) INTER bitset (k - 1)))}`SUBST1_TAC
THENL[SIMP_TAC[EXTENSION;IN_ELIM_THM] THEN GEN_TAC THEN AP_TERM_TAC
THEN SIMP_TAC[ARITH_RULE`1 + a = SUC a`] THEN SIMP_TAC[ODD;NOT_ODD];ALL_TAC]
THEN SIMP_TAC[GSYM IN_NUMSEG] THEN RULE_ASSUM_TAC(SIMP_RULE[GSYM IN_NUMSEG])
THEN SUBGOAL_THEN `{k |k IN 1.. 2 EXP N /\ EVEN (CARD (bitset (c - 2 EXP N) INTER bitset (k - 1)))}
= (1..2 EXP N) DIFF {k |k IN 1..2 EXP N /\ ODD (CARD (bitset (c - 2 EXP N) INTER bitset (k - 1)))}`
SUBST1_TAC THENL[SET_TAC[NOT_ODD];ALL_TAC] THEN SIMP_TAC[CARD_DIFF;FINITE_NUMSEG;SUBSET;IN_ELIM_THM]
THEN SIMP_TAC[CARD_NUMSEG_1] THEN ASM_SIMP_TAC[] THEN SUBGOAL_THEN`2 EXP (N - 1) < 2 EXP N`ASSUME_TAC
THENL[SIMP_TAC[LT_EXP;ARITH] THEN ASM_SIMP_TAC[ARITH_RULE`0 < N ==> N - 1 < N`];ALL_TAC]
THEN  POP_ASSUM MP_TAC THEN SIMP_TAC[ARITH_RULE`2 EXP (N - 1) < 2 EXP N ==> 2 EXP (N - 1)
  + 2 EXP N - 2 EXP (N - 1) = 2 EXP N`];ALL_TAC] THEN
RULE_ASSUM_TAC(SIMP_RULE[EQ_SYM_EQ]) THEN POP_ASSUM MP_TAC THEN POP_ASSUM (K ALL_TAC)
THEN POP_ASSUM (K ALL_TAC) THEN SIMP_TAC[ARITH;LT_REFL] THEN
SIMP_TAC[BITSET_EQ_BITSNUM;BITS_OF_NUM_POW2] THEN STRIP_TAC THEN
SIMP_TAC[INTER_IDEMPOT;UNION_COMM] THEN
SUBGOAL_THEN`{k | (1 <= k /\ k <= 2 EXP N) /\
          ODD   (CARD ({N} INTER bits_of_num (k - 1)))}  =
    {k | (1 <= k /\ k <= 2 EXP N) /\
            ODD (CARD {})}`SUBST1_TAC
THENL[SIMP_TAC[EXTENSION;IN_ELIM_THM] THEN GEN_TAC THEN EQ_TAC THENL
[STRIP_TAC THEN ASM_SIMP_TAC[] THEN POP_ASSUM MP_TAC THEN
SUBGOAL_THEN`{N} INTER bitset (x - 1)  = {}`ASSUME_TAC THENL[ASSUME_TAC(SPEC`N:num` BITS_OF_NUM_POW2)
THEN SIMP_TAC[BITSET_EQ_BITSNUM;GSYM DISJOINT]
THEN SIMP_TAC[DISJOINT_SING] THEN MP_TAC(SPECL[`x-1`;`N:num`] (GSYM BITS_OF_NUM_SUBSET_NUMSEG_EQ))
THEN UNDISCH_TAC`x <= 2 EXP N` THEN UNDISCH_TAC`1 <= x` THEN
SIMP_TAC[ARITH_RULE`1 <= x ==> x <= 2 EXP N ==> x - 1  < 2 EXP N`] THEN
SET_TAC[LT_REFL];ALL_TAC] THEN ASM_SIMP_TAC[GSYM BITSET_EQ_BITSNUM;INTER_EMPTY]
THEN SIMP_TAC[CARD_CLAUSES];ALL_TAC] THEN STRIP_TAC THEN ASM_SIMP_TAC[]
THEN POP_ASSUM MP_TAC THEN SIMP_TAC[CARD_CLAUSES;ODD];ALL_TAC]
THEN SIMP_TAC[CARD_CLAUSES;ODD;SET_RULE`{k | F} = {}`]
 THEN SUBGOAL_THEN`{k | (1 <= k /\ k <= 2 EXP N) /\
      ODD (CARD ({N} UNION {N} INTER bits_of_num (k - 1)))} =
  {k | (1 <= k /\ k <= 2 EXP N) /\
      ODD (CARD ({N} UNION {}))}`SUBST1_TAC
THENL[SIMP_TAC[EXTENSION;IN_ELIM_THM] THEN GEN_TAC THEN EQ_TAC
THENL [STRIP_TAC THEN ASM_SIMP_TAC[] THEN SIMP_TAC[UNION_EMPTY;CARD_SING;ARITH];ALL_TAC]
THEN STRIP_TAC THEN ASM_SIMP_TAC[] THEN SUBGOAL_THEN`{N} INTER bits_of_num (x - 1) = {}`SUBST1_TAC
THENL[ASSUME_TAC(SPEC`N:num` BITS_OF_NUM_POW2) THEN SIMP_TAC[BITSET_EQ_BITSNUM;GSYM DISJOINT]
THEN SIMP_TAC[DISJOINT_SING] THEN MP_TAC(SPECL[`x-1`;`N:num`] (GSYM BITS_OF_NUM_SUBSET_NUMSEG_EQ))
THEN UNDISCH_TAC`x <= 2 EXP N` THEN UNDISCH_TAC`1 <= x` THEN
SIMP_TAC[ARITH_RULE`1 <= x ==> x <= 2 EXP N ==> x - 1  < 2 EXP N`] THEN
SET_TAC[LT_REFL];ALL_TAC] THEN SIMP_TAC[UNION_EMPTY;CARD_SING;ARITH];ALL_TAC]
THEN SIMP_TAC[UNION_EMPTY;CARD_SING;ARITH;GSYM IN_NUMSEG;CARD_NUMSEG_1]
THEN SIMP_TAC[ADD_SYM;ADD_0] THEN SIMP_TAC[IN_NUMSEG] THEN SUBGOAL_THEN`{k | 1 <= k /\ k <= 2 EXP N} =
  1..2 EXP N`SUBST1_TAC THENL[REWRITE_TAC[EXTENSION; IN_NUMSEG; IN_ELIM_THM];ALL_TAC]
THEN SIMP_TAC[CARD_NUMSEG_1]);;

let BITAND_CARD_ODD_EQ_EVEN = prove
(`!N c:num.
  0 < c /\ c < 2 EXP N /\ 0 < N ==> CARD {k | k IN 1..2 EXP N /\
       ODD (CARD (bitand c (k - 1)))} =
       CARD {k | k IN 1..2 EXP N /\ EVEN (CARD (bitand c (k - 1)))}`,
SIMP_TAC[BITAND_ODD_CARD] THEN REPEAT STRIP_TAC THEN
SUBGOAL_THEN `{k |k IN 1.. 2 EXP N /\ EVEN (CARD (bitand c (k - 1)))}
= (1..2 EXP N) DIFF {k |k IN 1..2 EXP N /\ ODD (CARD (bitand c (k - 1)))}`SUBST1_TAC
THENL[SET_TAC[NOT_ODD];ALL_TAC] THEN SIMP_TAC[CARD_DIFF;FINITE_NUMSEG;SUBSET;IN_ELIM_THM;CARD_NUMSEG_1]
THEN ASM_SIMP_TAC[BITAND_ODD_CARD] THEN SIMP_TAC[ARITH_RULE`a:num = b - a <=> a + a = b`;GSYM MULT_2]
THEN SIMP_TAC[GSYM (SPECL[`2`;`N - 1`](CONJUNCT2 EXP))] THEN AP_TERM_TAC THEN ASM_ARITH_TAC);;

let BITSET_3 = prove
(`bits_of_num 3 = {0,1}`,
SIMP_TAC[ARITH_RULE`3 = 1 + 2`;SET_RULE`{0,1} = {0} UNION {1}`] THEN
SIMP_TAC[GSYM BITS_OF_NUM_POW2;EXP;ARITH_RULE`2 EXP 1 = 2`] THEN
 MATCH_MP_TAC BITS_OF_NUM_ADD THEN SIMP_TAC[BITS_OF_NUM_1] THEN
 ONCE_REWRITE_TAC[ARITH_RULE`2 = 2 EXP 1`] THEN REWRITE_TAC[BITS_OF_NUM_POW2] THEN
 SIMP_TAC[DISJOINT;INTER;IN_ELIM_THM;EXTENSION;IN_SING] THEN SET_TAC[ARITH_RULE`~(0 = 1)`]);;

let INTER_EMPTY_0_1 = prove
(`{0} INTER {1} = {}`,
SIMP_TAC[INTER;EXTENSION;IN_ELIM_THM;IN_SING] THEN SET_TAC[ARITH_RULE`~(0 = 1)`]);;

let CARD_2 = prove
(`CARD{0,1} = 2`,
ASSUME_TAC(SET_RULE`{0} UNION {1} = {0,1}`) THEN ASSUME_TAC INTER_EMPTY_0_1 THEN
SUBGOAL_THEN`CARD{0,1} = CARD{0} + CARD{1}`SUBST1_TAC THENL[MATCH_MP_TAC (GSYM CARD_UNION_EQ) THEN
ASM_SIMP_TAC[] THEN ASSUME_TAC(SPECL[`0`;`1`] numseg) THEN RULE_ASSUM_TAC(SIMP_RULE[ARITH_RULE`0 <= x /\ x <= 1 <=> x = 0 \/ x = 1`])
THEN RULE_ASSUM_TAC(SIMP_RULE[SET_RULE`{x |x = 0 \/ x = 1} = {0} UNION {1}`]) THEN SIMP_TAC[SET_RULE`{0,1} = {0} UNION {1}`]
THEN POP_ASSUM MP_TAC THEN GEN_REWRITE_TAC(LAND_CONV o ONCE_DEPTH_CONV)[EQ_SYM_EQ] THEN SIMP_TAC[FINITE_NUMSEG];ALL_TAC]
THEN SIMP_TAC[CARD_SING;ARITH]);;

let BITAND_ODD_ODD_CARD = prove
(`!N c d:num.
  0 < d /\ d < 2 EXP N /\ 0 < c /\ c < 2 EXP N /\ 1 < N /\ ~(c = d) ==> CARD {k | k IN 1..2 EXP N /\
       ODD(CARD (bitand c (k - 1))) /\ ODD(CARD (bitand d (k - 1)))} = 2 EXP (N - 2)`,
INDUCT_TAC THENL[ARITH_TAC;ALL_TAC] THEN REPEAT STRIP_TAC THEN
UNDISCH_TAC`!c d.
          0 < d /\ d < 2 EXP N /\ 0 < c /\ c < 2 EXP N /\ 1 < N /\ ~(c = d)
          ==> CARD
              {k | k IN 1..2 EXP N /\
                   ODD (CARD (bitand c (k - 1))) /\
                   ODD (CARD (bitand d (k - 1)))} = 2 EXP (N - 2)`
 THEN SIMP_TAC[GSYM ODD_MULT] THEN
ASSUME_TAC(ARITH_RULE`1 <= (2 EXP N) + 1 /\ 2 EXP N <= 2 EXP N + 2 EXP N`)
THEN FIRST_X_ASSUM(ASSUME_TAC o MATCH_MP (SPECL[`1`;`2 EXP N`;`2 EXP N + 2 EXP N`] (GSYM NUMSEG_COMBINE_R)))
THEN ASM_SIMP_TAC[UNION_RESTRICT;EXP;MULT_2] THEN POP_ASSUM (K ALL_TAC) THEN
SUBGOAL_THEN`DISJOINT {k | k IN 1..2 EXP N /\
               ODD (CARD (bitand c (k - 1)) * CARD (bitand d (k - 1)))}
   {k | k IN 2 EXP N + 1..2 EXP N + 2 EXP N /\
           ODD (CARD (bitand c (k - 1)) * CARD (bitand d (k - 1)))}`ASSUME_TAC
THENL[SUBGOAL_THEN`2 EXP N < 2 EXP N + 1 ==> DISJOINT(1..2 EXP N) (2 EXP N + 1..2 EXP N + 2 EXP N)`ASSUME_TAC
THENL[MESON_TAC[GSYM DISJOINT_NUMSEG];ALL_TAC] THEN RULE_ASSUM_TAC(SIMP_RULE[ARITH_RULE`2 EXP N < 2 EXP N +1`])
THEN ASM_SIMP_TAC[GSYM DISJOINT;SET_RULE `DISJOINT s t ==> DISJOINT {x | x IN s /\ P x} {x | x IN t /\ P x}`];ALL_TAC]
THEN RULE_ASSUM_TAC(SIMP_RULE[DISJOINT]) THEN ASM_SIMP_TAC[FINITE_NUMSEG;FINITE_RESTRICT;CARD_UNION] THEN
SIMP_TAC[OFFSET_IMAGE;FINITE_NUMSEG;FINITE_RESTRICT;CARD_IMAGE_EQ] THEN SIMP_TAC[IN_NUMSEG] THEN STRIP_TAC THEN
SUBGOAL_THEN `{k | (1 <= k /\ k <= 2 EXP N) /\ ODD(CARD (bitand c ((k + 2 EXP N) - 1)) *
       CARD (bitand d ((k + 2 EXP N) - 1)))} =
          {k | (1 <= k /\ k <= 2 EXP N) /\ ODD(CARD (bitand c (k - 1 + 2 EXP N )) *
       CARD (bitand d (k - 1 + 2 EXP N )))} `SUBST1_TAC THENL
[SIMP_TAC[EXTENSION;IN_ELIM_THM] THEN GEN_TAC THEN EQ_TAC THENL
[STRIP_TAC THEN
POP_ASSUM MP_TAC THEN ASM_SIMP_TAC[ARITH_RULE`1 <= x ==> (x + 2 EXP N) - 1 = x - 1 + 2 EXP N`];ALL_TAC]
THEN STRIP_TAC THEN ASM_SIMP_TAC[ARITH_RULE`1 <= x ==> (x + 2 EXP N) - 1 = x - 1 + 2 EXP N`];ALL_TAC]
THEN SIMP_TAC[bitand] THEN SUBGOAL_THEN`{k | (1 <= k /\ k <= 2 EXP N) /\
      ODD(CARD (bitset c INTER bitset (k - 1 + 2 EXP N)) *
       CARD (bitset d INTER bitset (k - 1 + 2 EXP N)))} = {k | (1 <= k /\ k <= 2 EXP N) /\
      ODD(CARD (bitset c INTER (bitset (k - 1) UNION {N})) *
       CARD (bitset d INTER (bitset (k - 1) UNION {N})))}`SUBST1_TAC
THENL[SIMP_TAC[EXTENSION;IN_ELIM_THM] THEN GEN_TAC THEN EQ_TAC THENL[STRIP_TAC THEN ASM_SIMP_TAC[]
THEN MP_TAC (SPECL[`x-1`;`N:num`] BITSET_ADD) THEN ASM_SIMP_TAC[ARITH_RULE`1 <= x /\ x <= 2 EXP N ==> x - 1 < 2 EXP N`]
THEN STRIP_TAC THEN UNDISCH_TAC`ODD
      (CARD   (bitset c INTER bitset (x - 1 + 2 EXP N)) *
         CARD (bitset d INTER bitset (x - 1 + 2 EXP N)))`
THEN ASM_SIMP_TAC[];ALL_TAC] THEN STRIP_TAC THEN MP_TAC (SPECL[`x-1`;`N:num`] BITSET_ADD) THEN
ASM_SIMP_TAC[ARITH_RULE`1 <= x /\ x <= 2 EXP N ==> x - 1 < 2 EXP N`];ALL_TAC] THEN
SIMP_TAC[UNION_OVER_INTER;ARITH_RULE`SUC N - 2 = N - 1`] THEN ASM_CASES_TAC` c < 2 EXP N /\ 1 < N /\ d < 2 EXP N`
THENL[FIRST_X_ASSUM(MP_TAC o SPECL[`c:num`;`d:num`]) THEN ASM_SIMP_TAC[bitand;BITSET_EQ_BITSNUM]
THEN ASSUME_TAC(SPEC`c:num` BITS_OF_NUM_SUBSET_NUMSEG_LT) THEN ASSUME_TAC(SPEC`d:num` BITS_OF_NUM_SUBSET_NUMSEG_LT)
THEN SUBGOAL_THEN`bits_of_num c INTER {N} = {}`SUBST1_TAC THENL[POP_ASSUM MP_TAC THEN
UNDISCH_TAC`c < 2 EXP N /\ 1 < N /\ d < 2 EXP N` THEN REPEAT STRIP_TAC THEN ASSUME_TAC(SPEC`N:num` BITS_OF_NUM_POW2)
THEN SIMP_TAC[GSYM DISJOINT] THEN MP_TAC(SPECL[`c:num`;`N:num`] (GSYM BITS_OF_NUM_SUBSET_NUMSEG_EQ))
THEN ASM_SIMP_TAC[] THEN SET_TAC[LT_REFL];ALL_TAC] THEN SUBGOAL_THEN`bits_of_num d INTER {N} = {}`SUBST1_TAC
THENL[POP_ASSUM MP_TAC THEN UNDISCH_TAC`c < 2 EXP N /\ 1 < N /\ d < 2 EXP N` THEN REPEAT STRIP_TAC
THEN ASSUME_TAC(SPEC`N:num` BITS_OF_NUM_POW2) THEN SIMP_TAC[GSYM DISJOINT] THEN
MP_TAC(SPECL[`d:num`;`N:num`] (GSYM BITS_OF_NUM_SUBSET_NUMSEG_EQ))
THEN ASM_SIMP_TAC[] THEN SET_TAC[LT_REFL];ALL_TAC] THEN SIMP_TAC[UNION_EMPTY;GSYM MULT_2]
THEN GEN_REWRITE_TAC(RAND_CONV o LAND_CONV o LAND_CONV o ONCE_DEPTH_CONV)[ARITH_RULE`2 = (2 EXP 1)`]
THEN ASM_SIMP_TAC[GSYM EXP_ADD] THEN UNDISCH_TAC`1 < SUC N` THEN
SIMP_TAC[ARITH_RULE`1 < SUC N <=> 0 < N`;ARITH_RULE`1 + N - 2 = 1 + N - 1 - 1`] THEN REPEAT STRIP_TAC THEN
AP_TERM_TAC THEN ASM_ARITH_TAC;ALL_TAC] THEN UNDISCH_TAC`~(c < 2 EXP N /\ 1 < N /\ d < 2 EXP N)` THEN
SIMP_TAC[DE_MORGAN_THM;ARITH_RULE`~(a < b:num) <=> b <= a`] THEN ASM_CASES_TAC`N <= 1` THENL[
ASM_SIMP_TAC[] THEN RULE_ASSUM_TAC(SIMP_RULE[ARITH_RULE`1 < SUC N <=> 0 < N `]) THEN
RULE_ASSUM_TAC(SIMP_RULE[ARITH_RULE`N <= 1 <=> N = 0 \/ N = 1`]) THEN POP_ASSUM MP_TAC THEN
ASM_SIMP_TAC[ARITH_RULE`0 < N ==> ~(N = 0)`;ARITH] THEN STRIP_TAC THEN
SIMP_TAC[ARITH_RULE`1 <= k /\ k <= 2 <=> k = 1 \/ k = 2`] THEN
SIMP_TAC[SET_RULE `{x | (x = a \/ x = b) /\ P x} = {x | x = a /\ P a \/  x = b /\ P b}`]
THEN SIMP_TAC[ARITH;BITSET_0] THEN SIMP_TAC[BITSET_EQ_BITSNUM;BITS_OF_NUM_1;INTER_EMPTY;CARD_CLAUSES;UNION_EMPTY]
THEN SIMP_TAC[ODD;MULT_0] THEN UNDISCH_TAC`c < 2 EXP SUC N` THEN UNDISCH_TAC`d < 2 EXP SUC N` THEN
ASM_SIMP_TAC[ARITH] THEN REPEAT STRIP_TAC THEN
MP_TAC (ARITH_RULE `0 < c /\ c < 4 ==> (c = 1 \/ c = 2 \/ c = 3)`) THEN
MP_TAC (ARITH_RULE `0 < d /\ d < 4 ==> (d = 1 \/ d = 2 \/ d = 3)`) THEN ASM_SIMP_TAC[] THEN
ASM_CASES_TAC`d = 1` THENL[ASM_SIMP_TAC[BITS_OF_NUM_1] THEN SIMP_TAC[INTER_IDEMPOT;CARD_SING] THEN
MP_TAC (ARITH_RULE`~(c = d) /\ d = 1 ==> ~(c = 1)`) THEN ASM_SIMP_TAC[] THEN STRIP_TAC THEN
SIMP_TAC[INTER_OVER_UNION;UNION_IDEMPOT;SET_RULE`{0} UNION {1} = {0,1}`;SET_RULE`{0} INTER {0,1} = {0}`;CARD_SING]
THEN ASM_CASES_TAC`c = 2` THENL[ASM_SIMP_TAC[] THEN ONCE_REWRITE_TAC[ARITH_RULE`2 = 2 EXP 1`] THEN SIMP_TAC[BITS_OF_NUM_POW2]
THEN SIMP_TAC[SET_RULE`{1} INTER {0} UNION {1} = {1} UNION {1} INTER {0}`;INTER_IDEMPOT;INTER_OVER_UNION;UNION_IDEMPOT]
THEN SIMP_TAC[SET_RULE`{1} UNION {0} = {0,1}`;SET_RULE`{1} INTER {0,1} = {1}`;CARD_SING;ARITH] THEN
SUBGOAL_THEN`{0} INTER {1} = {}`ASSUME_TAC THENL[SET_TAC[ARITH_RULE`~( 0 = 1)`];ALL_TAC] THEN
GEN_REWRITE_TAC(LAND_CONV o LAND_CONV o ONCE_DEPTH_CONV) [INTER_COMM] THEN ASM_SIMP_TAC[CARD_CLAUSES;ARITH]
THEN SIMP_TAC[SET_RULE`{k |F} = {}`;CARD_CLAUSES] THEN SIMP_TAC[SET_RULE`{k |k = 2} = {2}`;CARD_SING;ARITH];ALL_TAC]
THEN ASM_SIMP_TAC[BITSET_3] THEN SIMP_TAC[SET_RULE`{0,1} INTER {0} = {0}`;SET_RULE`{0} UNION {0,1} = {0,1}`]
THEN SIMP_TAC[SET_RULE`{0,1} INTER {1} = {1}`;SET_RULE`{0} UNION {1} = {0,1}`] THEN SIMP_TAC[INTER_IDEMPOT;CARD_SING;ARITH] THEN
SIMP_TAC[CARD_2;INTER_EMPTY_0_1;CARD_CLAUSES;ARITH;SET_RULE`{k |F} = {}`;SET_RULE`{k | k = 2} = {2}`;CARD_SING];ALL_TAC] THEN
ASM_SIMP_TAC[] THEN ASM_CASES_TAC`d = 2` THENL[ASM_SIMP_TAC[] THEN MP_TAC(ARITH_RULE`~(c = d) /\ d = 2 ==> ~(c = 2)`) THEN
ASM_SIMP_TAC[] THEN STRIP_TAC THEN ASM_CASES_TAC`c = 1` THENL[ASM_SIMP_TAC[] THEN ONCE_REWRITE_TAC[ARITH_RULE`2 = 2 EXP 1`]
THEN SIMP_TAC[BITS_OF_NUM_POW2;BITS_OF_NUM_1;INTER_IDEMPOT;INTER_EMPTY_0_1] THEN ONCE_REWRITE_TAC[INTER_COMM] THEN
SIMP_TAC[INTER_EMPTY_0_1;UNION_EMPTY;CARD_SING;CARD_CLAUSES;ARITH] THEN SIMP_TAC[SET_RULE`{k | F} = {}`;SET_RULE`{k | k = 2} = {2}`;CARD_SING;CARD_CLAUSES;ARITH];ALL_TAC] THEN ASM_SIMP_TAC[BITSET_3] THEN
SIMP_TAC[SET_RULE`{0,1} INTER {0} = {0}`;SET_RULE`{0,1} INTER {1} = {1}`] THEN ONCE_REWRITE_TAC[ARITH_RULE`2 = 2 EXP 1`]
THEN REWRITE_TAC[BITS_OF_NUM_POW2] THEN ONCE_REWRITE_TAC[INTER_COMM] THEN
SIMP_TAC[INTER_EMPTY_0_1;INTER_IDEMPOT;SET_RULE`{0} UNION {1} = {0,1}`;CARD_2;CARD_SING;CARD_CLAUSES;ARITH;UNION_EMPTY]
THEN SIMP_TAC[SET_RULE`{k |F} = {}`;SET_RULE`{k |k = 1} = {1}`;CARD_SING;CARD_CLAUSES;ARITH];ALL_TAC] THEN
ASM_SIMP_TAC[BITSET_3] THEN MP_TAC(ARITH_RULE`~(c = d) /\ d = 3 ==> ~(c = 3)`) THEN ASM_SIMP_TAC[] THEN
ASM_CASES_TAC`c = 1` THENL[ASM_SIMP_TAC[BITS_OF_NUM_1] THEN
SIMP_TAC[INTER_IDEMPOT;INTER_EMPTY_0_1;SET_RULE`{0,1} INTER {0} = {0}`;SET_RULE`{0,1} INTER {1} = {1}`;UNION_EMPTY] THEN
SIMP_TAC[SET_RULE`{0} UNION {1} = {0,1}`;CARD_2;CARD_SING;CARD_CLAUSES;SET_RULE`{k |F} = {}`;SET_RULE`{k |k = 2} = {2}`;ARITH];ALL_TAC ]
THEN ASM_SIMP_TAC[] THEN ONCE_REWRITE_TAC[ARITH_RULE`2 = 2 EXP 1`] THEN SIMP_TAC[BITS_OF_NUM_POW2;INTER_IDEMPOT] THEN
ONCE_REWRITE_TAC[INTER_COMM] THEN SIMP_TAC[INTER_EMPTY_0_1;UNION_EMPTY;SET_RULE`{0} INTER {0,1} = {0}`;SET_RULE`{1} INTER {0,1} = {1}`]
THEN SIMP_TAC[SET_RULE`{0} UNION {1} = {0,1}`;CARD_SING;CARD_2;CARD_CLAUSES;ARITH;SET_RULE`{k |F} = {}`;SET_RULE`{k |k = 1} = {1}`];ALL_TAC]
THEN ASM_SIMP_TAC[] THEN RULE_ASSUM_TAC(SIMP_RULE[ARITH_RULE`~(N <= 1) <=> 1 < N`]) THEN STRIP_TAC THENL[
RULE_ASSUM_TAC(SIMP_RULE[ARITH_RULE`2 EXP N <= c <=> 2 EXP N < c \/ c = 2 EXP N`]) THEN MP_TAC(SPECL[`c - 2 EXP N`;`N:num`] BITSET_ADD)
THEN MP_TAC(SPECL[`d - 2 EXP N`;`N:num`] BITSET_ADD) THEN SIMP_TAC[ARITH_RULE`n - 2 EXP N  < 2 EXP N  <=> n < 2 EXP N + 2 EXP N`]
THEN SIMP_TAC[GSYM MULT_2;ARITH_RULE`2 * 2 EXP N = 2 EXP 1 * 2 EXP N `;GSYM EXP_ADD] THEN ASM_SIMP_TAC[ARITH_RULE`1 + N = SUC N`]
THEN REPEAT STRIP_TAC THEN UNDISCH_TAC`2 EXP N < c \/ c = 2 EXP N` THEN
STRIP_TAC THENL[FIRST_X_ASSUM(MP_TAC o SPECL[`c - 2 EXP N `;`d - 2 EXP N`])
THEN SIMP_TAC[ARITH_RULE`0 < c - a <=> a < c`] THEN SIMP_TAC[ARITH_RULE`n - 2 EXP N  < 2 EXP N  <=> n < 2 EXP N + 2 EXP N`] THEN
SIMP_TAC[GSYM MULT_2;ARITH_RULE`2 * 2 EXP N = 2 EXP 1 * 2 EXP N `;GSYM EXP_ADD] THEN ASM_SIMP_TAC[ARITH_RULE`1 + N = SUC N`]
THEN ASM_CASES_TAC`2 EXP N < d`
THENL[ASM_SIMP_TAC[ARITH_RULE`2 EXP N < c /\ 2 EXP N < d /\ ~(c = d) ==> ~(c - 2 EXP N = d - 2 EXP N)`]
THEN UNDISCH_TAC`bitset (d - 2 EXP N + 2 EXP N) = bitset (d - 2 EXP N) UNION {N}` THEN
SUBGOAL_THEN`bitset (d - 2 EXP N + 2 EXP N) = bitset d`SUBST1_TAC THENL[
ASM_SIMP_TAC[ARITH_RULE`2 EXP N < n ==> n - 2 EXP N + 2 EXP N = n`];ALL_TAC] THEN STRIP_TAC THEN
UNDISCH_TAC`bitset (c - 2 EXP N + 2 EXP N) = bitset (c - 2 EXP N) UNION {N}` THEN
SUBGOAL_THEN`bitset (c - 2 EXP N + 2 EXP N) = bitset c`SUBST1_TAC THENL[
ASM_SIMP_TAC[ARITH_RULE`2 EXP N < n ==> n - 2 EXP N + 2 EXP N = n`];ALL_TAC] THEN STRIP_TAC
THEN SUBGOAL_THEN`bitset c INTER {N} = {N}`ASSUME_TAC THENL[SIMP_TAC[INTER;IN_ELIM_THM;EXTENSION] THEN ASM_SIMP_TAC[IN_UNION] THEN
SET_TAC[];ALL_TAC] THEN SUBGOAL_THEN`bitset d INTER {N} = {N}`ASSUME_TAC THENL[SIMP_TAC[INTER;IN_ELIM_THM;EXTENSION] THEN ASM_SIMP_TAC[IN_UNION] THEN
SET_TAC[];ALL_TAC] THEN POP_ASSUM MP_TAC THEN POP_ASSUM MP_TAC THEN SIMP_TAC[] THEN REPEAT STRIP_TAC THEN SIMP_TAC[UNION_COMM;INTER_OVER_UNION]
THEN ASM_SIMP_TAC[] THEN SIMP_TAC[UNION_COMM] THEN SIMP_TAC[SET_RULE`s UNION s UNION t = s UNION t`] THEN
RULE_ASSUM_TAC(SIMP_RULE[EQ_SYM_EQ;UNION_COMM]) THEN UNDISCH_TAC`{N} UNION bitset (d - 2 EXP N) = bitset d` THEN
UNDISCH_TAC`{N} UNION bitset (c - 2 EXP N) = bitset c` THEN SIMP_TAC[] THEN REPEAT STRIP_TAC THEN RULE_ASSUM_TAC(ONCE_REWRITE_RULE[EQ_SYM_EQ])
THEN RULE_ASSUM_TAC(SIMP_RULE[bitand]) THEN
ASM_SIMP_TAC[SET_RULE`(s UNION t) INTER u = s INTER u UNION t INTER u`]
THEN SUBGOAL_THEN`{k | (1 <= k /\ k <= 2 EXP N) /\
      ODD(CARD({N} INTER bitset (k - 1) UNION
bitset (c - 2 EXP N) INTER bitset (k - 1)) * CARD({N} INTER bitset (k - 1) UNION
            bitset (d - 2 EXP N) INTER bitset (k - 1)))} =
    {k | (1 <= k /\ k <= 2 EXP N) /\ ODD(CARD(bitset (c - 2 EXP N) INTER bitset (k - 1)) *
    CARD( bitset (d - 2 EXP N) INTER bitset (k - 1)))}`SUBST1_TAC THENL[SIMP_TAC[EXTENSION;IN_ELIM_THM] THEN GEN_TAC THEN EQ_TAC
    THENL [STRIP_TAC THEN ASM_SIMP_TAC[] THEN POP_ASSUM MP_TAC THEN SUBGOAL_THEN`{N} INTER bitset (x - 1) = {}`SUBST1_TAC
    THENL[ASSUME_TAC(SPEC`N:num` BITS_OF_NUM_POW2) THEN SIMP_TAC[BITSET_EQ_BITSNUM;GSYM DISJOINT]
THEN SIMP_TAC[DISJOINT_SING] THEN MP_TAC(SPECL[`x-1`;`N:num`] (GSYM BITS_OF_NUM_SUBSET_NUMSEG_EQ))
THEN UNDISCH_TAC`x <= 2 EXP N` THEN UNDISCH_TAC`1 <= x` THEN
SIMP_TAC[ARITH_RULE`1 <= x ==> x <= 2 EXP N ==> x - 1  < 2 EXP N`] THEN
SET_TAC[LT_REFL];ALL_TAC] THEN ASM_SIMP_TAC[UNION_EMPTY;INTER_COMM];ALL_TAC] THEN SIMP_TAC[] THEN STRIP_TAC
THEN SUBGOAL_THEN`{N} INTER bitset (x - 1) = {}`SUBST1_TAC THENL[ASSUME_TAC(SPEC`N:num` BITS_OF_NUM_POW2) THEN SIMP_TAC[BITSET_EQ_BITSNUM;GSYM DISJOINT]
THEN SIMP_TAC[DISJOINT_SING] THEN MP_TAC(SPECL[`x-1`;`N:num`] (GSYM BITS_OF_NUM_SUBSET_NUMSEG_EQ))
THEN UNDISCH_TAC`x <= 2 EXP N` THEN UNDISCH_TAC`1 <= x` THEN
SIMP_TAC[ARITH_RULE`1 <= x ==> x <= 2 EXP N ==> x - 1  < 2 EXP N`] THEN
SET_TAC[LT_REFL];ALL_TAC] THEN ASM_SIMP_TAC[UNION_EMPTY;INTER_COMM];ALL_TAC] THEN UNDISCH_TAC`2 EXP (N - 2) =
      CARD
      {  k   | (1 <= k /\ k <= 2 EXP N) /\
             ODD
             (CARD (bitset (c - 2 EXP N) INTER bitset (k - 1)) *
              CARD (bitset (d - 2 EXP N) INTER bitset (k - 1)))}`
THEN GEN_REWRITE_TAC(LAND_CONV o ONCE_DEPTH_CONV) [EQ_SYM_EQ] THEN SIMP_TAC[]
THEN SIMP_TAC[UNION_OVER_INTER;INTER_IDEMPOT]
THEN ONCE_REWRITE_TAC[SET_RULE`(s UNION t) UNION u UNION v = (s UNION u) UNION t UNION v`] THEN STRIP_TAC THEN
SUBGOAL_THEN`{k | (1 <= k /\ k <= 2 EXP N) /\
      ODD(CARD(({N} UNION bitset (c - 2 EXP N) INTER {N}) UNION
        {N} INTER bitset (k - 1) UNION  bitset (c - 2 EXP N) INTER bitset (k - 1)) *
       CARD(({N} UNION bitset (d - 2 EXP N) INTER {N}) UNION
        {N} INTER bitset (k - 1) UNION  bitset (d - 2 EXP N) INTER bitset (k - 1)))} =
        {k | (1 <= k /\ k <= 2 EXP N) /\
      ODD(CARD ({N} UNION bitset (c - 2 EXP N) INTER bitset (k - 1) ) *
       CARD({N} UNION bitset (d - 2 EXP N) INTER bitset (k - 1)))}`SUBST1_TAC
THENL[SIMP_TAC[EXTENSION;IN_ELIM_THM] THEN GEN_TAC THEN EQ_TAC THENL[STRIP_TAC THEN ASM_SIMP_TAC[] THEN
POP_ASSUM MP_TAC THEN SUBGOAL_THEN`{N} INTER bitset (x - 1) = {}`SUBST1_TAC
    THENL[ASSUME_TAC(SPEC`N:num` BITS_OF_NUM_POW2) THEN SIMP_TAC[BITSET_EQ_BITSNUM;GSYM DISJOINT]
THEN SIMP_TAC[DISJOINT_SING] THEN MP_TAC(SPECL[`x-1`;`N:num`] (GSYM BITS_OF_NUM_SUBSET_NUMSEG_EQ))
THEN UNDISCH_TAC`x <= 2 EXP N` THEN UNDISCH_TAC`1 <= x` THEN
SIMP_TAC[ARITH_RULE`1 <= x ==> x <= 2 EXP N ==> x - 1  < 2 EXP N`] THEN
SET_TAC[LT_REFL];ALL_TAC] THEN ASM_SIMP_TAC[UNION_EMPTY] THEN UNDISCH_TAC`bitset c INTER {N} = {N}`
THEN UNDISCH_TAC`bitset d INTER {N} = {N}` THEN ASM_SIMP_TAC[] THEN
SIMP_TAC[SET_RULE`s UNION t INTER s = (s UNION t) INTER s`];ALL_TAC] THEN SIMP_TAC[] THEN STRIP_TAC THEN
SUBGOAL_THEN`{N} INTER bitset (x - 1) = {}`SUBST1_TAC THENL[ASSUME_TAC(SPEC`N:num` BITS_OF_NUM_POW2) THEN SIMP_TAC[BITSET_EQ_BITSNUM;GSYM DISJOINT]
THEN SIMP_TAC[DISJOINT_SING] THEN MP_TAC(SPECL[`x-1`;`N:num`] (GSYM BITS_OF_NUM_SUBSET_NUMSEG_EQ))
THEN UNDISCH_TAC`x <= 2 EXP N` THEN UNDISCH_TAC`1 <= x` THEN
SIMP_TAC[ARITH_RULE`1 <= x ==> x <= 2 EXP N ==> x - 1  < 2 EXP N`] THEN
SET_TAC[LT_REFL];ALL_TAC] THEN ASM_SIMP_TAC[UNION_EMPTY] THEN UNDISCH_TAC`bitset c INTER {N} = {N}`
THEN UNDISCH_TAC`bitset d INTER {N} = {N}` THEN ASM_SIMP_TAC[SET_RULE`s UNION t INTER s = (s UNION t) INTER s`];ALL_TAC]
THEN SUBGOAL_THEN `{k | (1 <= k /\ k <= 2 EXP N) /\
      ODD(CARD ({N} UNION bitset (c - 2 EXP N) INTER bitset (k - 1)) *
       CARD ({N} UNION bitset (d - 2 EXP N) INTER bitset (k - 1)))} =
 {k | (1 <= k /\ k <= 2 EXP N) /\
      ODD((CARD {N} + CARD (bitset (c - 2 EXP N) INTER bitset (k - 1))) *
       (CARD {N} + CARD (bitset (d - 2 EXP N) INTER bitset (k - 1))))}`SUBST1_TAC
THENL[SIMP_TAC[EXTENSION;IN_ELIM_THM] THEN GEN_TAC THEN REPEAT AP_TERM_TAC THEN
SUBGOAL_THEN`CARD ({N} UNION bitset (c - 2 EXP N) INTER bitset (x - 1))
  = CARD {N} + CARD (bitset (c - 2 EXP N) INTER bitset (x - 1))`SUBST1_TAC
  THENL[MATCH_MP_TAC CARD_UNION THEN SIMP_TAC[FINITE_BITSET;FINITE_INTER;FINITE_SING] THEN
ASSUME_TAC(SPEC`N:num` BITS_OF_NUM_POW2) THEN SIMP_TAC[BITSET_EQ_BITSNUM;GSYM DISJOINT] THEN
SIMP_TAC[DISJOINT_SING] THEN MP_TAC(SPECL[`c - 2 EXP N`;`N:num`] (GSYM BITS_OF_NUM_SUBSET_NUMSEG_EQ)) THEN
UNDISCH_TAC`c < 2 EXP SUC N` THEN UNDISCH_TAC`2 EXP N < c` THEN SIMP_TAC[ARITH_RULE`c - 2 EXP N  < 2 EXP N <=> c < 2 EXP N + 2 EXP N`]
THEN SIMP_TAC[ARITH_RULE`SUC N = 1 + N`;EXP_ADD;EXP_1;MULT_2] THEN
SET_TAC[LT_REFL];ALL_TAC] THEN SUBGOAL_THEN`CARD ({N} UNION bitset (d - 2 EXP N) INTER bitset (x - 1))
  = CARD {N} + CARD (bitset (d - 2 EXP N) INTER bitset (x - 1))`SUBST1_TAC THENL[MATCH_MP_TAC CARD_UNION THEN
  SIMP_TAC[FINITE_BITSET;FINITE_INTER;FINITE_SING] THEN
ASSUME_TAC(SPEC`N:num` BITS_OF_NUM_POW2) THEN SIMP_TAC[BITSET_EQ_BITSNUM;GSYM DISJOINT] THEN
SIMP_TAC[DISJOINT_SING] THEN MP_TAC(SPECL[`d - 2 EXP N`;`N:num`] (GSYM BITS_OF_NUM_SUBSET_NUMSEG_EQ)) THEN
UNDISCH_TAC`d < 2 EXP SUC N` THEN UNDISCH_TAC`2 EXP N < d` THEN SIMP_TAC[ARITH_RULE`d - 2 EXP N  < 2 EXP N <=> d < 2 EXP N + 2 EXP N`]
THEN SIMP_TAC[ARITH_RULE`SUC N = 1 + N`;EXP_ADD;EXP_1;MULT_2] THEN
SET_TAC[LT_REFL];ALL_TAC] THEN SIMP_TAC[CARD_SING];ALL_TAC]
THEN SIMP_TAC[CARD_SING] THEN
SIMP_TAC[ARITH_RULE`1 + a = SUC a`;ODD_MULT;ODD;NOT_ODD] THEN RULE_ASSUM_TAC(SIMP_RULE[ODD_MULT]) THEN
MP_TAC(SPECL[`N:num`;`c - 2 EXP N`] BITAND_ODD_CARD) THEN SIMP_TAC[ARITH_RULE`0 < c - a <=> a < c`] THEN
SIMP_TAC[ARITH_RULE`n - 2 EXP N  < 2 EXP N  <=> n < 2 EXP N + 2 EXP N`] THEN
SIMP_TAC[GSYM MULT_2;ARITH_RULE`2 * 2 EXP N = 2 EXP 1 * 2 EXP N `;GSYM EXP_ADD] THEN
ASM_SIMP_TAC[ARITH_RULE`1 + N = SUC N`;ARITH_RULE`1 < N ==> 0 < N`] THEN STRIP_TAC THEN
MP_TAC(SPECL[`N:num`;`c - 2 EXP N`] BITAND_CARD_ODD_EQ_EVEN) THEN SIMP_TAC[ARITH_RULE`0 < c - a <=> a < c`] THEN
SIMP_TAC[ARITH_RULE`n - 2 EXP N  < 2 EXP N  <=> n < 2 EXP N + 2 EXP N`] THEN
SIMP_TAC[GSYM MULT_2;ARITH_RULE`2 * 2 EXP N = 2 EXP 1 * 2 EXP N `;GSYM EXP_ADD] THEN
ASM_SIMP_TAC[ARITH_RULE`1 + N = SUC N`;ARITH_RULE`1 < N ==> 0 < N`] THEN GEN_REWRITE_TAC(LAND_CONV o ONCE_DEPTH_CONV)[EQ_SYM_EQ]
THEN STRIP_TAC THEN ASM_SIMP_TAC[] THEN MP_TAC(SPECL[`N:num`;`d - 2 EXP N`] BITAND_ODD_CARD) THEN SIMP_TAC[ARITH_RULE`0 < c - a <=> a < c`] THEN
SIMP_TAC[ARITH_RULE`n - 2 EXP N  < 2 EXP N  <=> n < 2 EXP N + 2 EXP N`] THEN
SIMP_TAC[GSYM MULT_2;ARITH_RULE`2 * 2 EXP N = 2 EXP 1 * 2 EXP N `;GSYM EXP_ADD] THEN
ASM_SIMP_TAC[ARITH_RULE`1 + N = SUC N`;ARITH_RULE`1 < N ==> 0 < N`] THEN STRIP_TAC THEN
MP_TAC(SPECL[`N:num`;`d - 2 EXP N`] (GSYM BITAND_CARD_ODD_EQ_EVEN)) THEN SIMP_TAC[ARITH_RULE`0 < c - a <=> a < c`] THEN
SIMP_TAC[ARITH_RULE`n - 2 EXP N  < 2 EXP N  <=> n < 2 EXP N + 2 EXP N`] THEN
SIMP_TAC[GSYM MULT_2;ARITH_RULE`2 * 2 EXP N = 2 EXP 1 * 2 EXP N `;GSYM EXP_ADD] THEN
ASM_SIMP_TAC[ARITH_RULE`1 + N = SUC N`;ARITH_RULE`1 < N ==> 0 < N`] THEN STRIP_TAC THEN
SIMP_TAC[GSYM IN_NUMSEG] THEN
ONCE_SIMP_TAC[SET_RULE`{x | x IN s /\ p x /\ q x} = {x | x IN s /\ p x} DIFF {x |x IN s /\ p x /\ ~q x}`]
THEN SIMP_TAC[NOT_EVEN] THEN
SIMP_TAC[FINITE_NUMSEG;FINITE_RESTRICT;SET_RULE`{x |x IN s /\ p x /\ q x } SUBSET {x |x IN s /\ p x}`;CARD_DIFF]
THEN ASM_SIMP_TAC[GSYM bitand] THEN ONCE_REWRITE_TAC[TAUT`P /\ Q /\ R <=> P /\ R /\ Q`] THEN
ONCE_SIMP_TAC[SET_RULE`{x | x IN s /\ p x /\ q x} = {x | x IN s /\ p x} DIFF {x |x IN s /\ p x /\ ~q x}`]
THEN SIMP_TAC[NOT_EVEN] THEN
SIMP_TAC[FINITE_NUMSEG;FINITE_RESTRICT;SET_RULE`{x |x IN s /\ p x /\ q x } SUBSET {x |x IN s /\ p x}`;CARD_DIFF]
THEN ASM_SIMP_TAC[] THEN ONCE_REWRITE_TAC[TAUT`P /\ Q /\ R <=> P /\ R /\ Q`] THEN
ASM_SIMP_TAC[bitand;IN_NUMSEG] THEN
SUBGOAL_THEN`2 EXP (N - 2) < 2 EXP (N - 1)`ASSUME_TAC THENL[SIMP_TAC[LT_EXP;ARITH]
THEN ASM_SIMP_TAC[ARITH_RULE`1 < N ==> N - 2 < N - 1`];ALL_TAC] THEN ASM_SIMP_TAC[ARITH_RULE`2 EXP (N - 2) < 2 EXP (N - 1) ==>
2 EXP (N - 2) + 2 EXP (N - 1) -(2 EXP (N - 1) - 2 EXP (N - 2)) = 2 EXP (N - 2) + 2 EXP (N - 2)`] THEN
SIMP_TAC[GSYM MULT_2] THEN ASM_SIMP_TAC[ARITH_RULE`1 < N ==> N - 1 = SUC (N - 2)`;EXP];ALL_TAC ] THEN
ASM_SIMP_TAC[] THEN RULE_ASSUM_TAC(SIMP_RULE[NOT_LT]) THEN POP_ASSUM MP_TAC THEN  SIMP_TAC[ARITH_RULE`d <= 2 EXP N <=> d < 2 EXP N \/ d = 2 EXP N `]
THEN STRIP_TAC THENL[MP_TAC(SPECL[`N:num`;`d:num`] BITAND_ODD_CARD) THEN ASM_SIMP_TAC[ARITH_RULE`1 + N = SUC N`;ARITH_RULE`1 < N ==> 0 < N`]
THEN STRIP_TAC THEN SIMP_TAC[ODD_MULT] THEN SUBGOAL_THEN`{k | (1 <= k /\ (k < 2 EXP N \/ k = 2 EXP N)) /\
      ODD (CARD (bitset c INTER bitset (k - 1) UNION bitset c INTER {N})) /\
     ODD (CARD (bitset d INTER bitset (k - 1) UNION bitset d INTER {N}))} =
  {k | (1 <= k /\ (k < 2 EXP N \/ k = 2 EXP N)) /\
        EVEN (CARD (bitset c INTER bitset (k - 1))) /\
  ODD (CARD (bitset d INTER bitset (k - 1)))}`SUBST1_TAC THENL[SUBGOAL_THEN`bitset c INTER {N} = {N}`SUBST1_TAC
  THENL[SIMP_TAC[EXTENSION;IN_ELIM_THM;INTER] THEN UNDISCH_TAC`bitset (c - 2 EXP N + 2 EXP N) = bitset (c - 2 EXP N) UNION {N}`
THEN SUBGOAL_THEN`bitset (c - 2 EXP N + 2 EXP N) = bitset c`SUBST1_TAC THENL
[ASM_SIMP_TAC[ARITH_RULE`2 EXP N < c ==> c - 2 EXP N + 2 EXP N = c`];ALL_TAC] THEN SET_TAC[IN_UNION];ALL_TAC]
THEN SUBGOAL_THEN`bitset d INTER {N} = {}`SUBST1_TAC THENL[SIMP_TAC[BITSET_EQ_BITSNUM] THEN
MP_TAC(SPECL[`d:num`;`N:num`] (GSYM BITS_OF_NUM_SUBSET_NUMSEG_EQ)) THEN ASM_SIMP_TAC[] THEN SET_TAC[LT_REFL];ALL_TAC]
THEN SIMP_TAC[UNION_EMPTY] THEN SIMP_TAC[ARITH_RULE`k < 2 EXP N \/ k = 2 EXP N <=> k <= 2 EXP N`] THEN
SUBGOAL_THEN`{k | (1 <= k /\ k <= 2 EXP N ) /\
      ODD (CARD (bitset c INTER bitset (k - 1) UNION {N})) /\
      ODD (CARD (bitset d INTER bitset (k - 1)))}    =
  {k | (1 <= k /\ k <= 2 EXP N) /\
        ODD (CARD (bitset c INTER bitset (k - 1)) + CARD {N}) /\
  ODD (CARD (bitset d INTER bitset (k - 1)))}`SUBST1_TAC
THENL[SIMP_TAC[EXTENSION;IN_ELIM_THM] THEN GEN_TAC THEN EQ_TAC THENL [SIMP_TAC[] THEN STRIP_TAC THEN
SUBGOAL_THEN`bitset (x - 1) INTER {N} = {}`ASSUME_TAC THENL[SIMP_TAC[BITSET_EQ_BITSNUM] THEN
MP_TAC(SPECL[`x-1`;`N:num`] (GSYM BITS_OF_NUM_SUBSET_NUMSEG_EQ)) THEN ASM_SIMP_TAC[ARITH_RULE`1 <= x ==> x <= a ==> x - 1 < a`]
THEN SET_TAC[LT_REFL];ALL_TAC] THEN SUBGOAL_THEN`(bitset c INTER bitset (x - 1)) INTER {N} = {}`ASSUME_TAC
THENL[ASM_SIMP_TAC[SET_RULE`(s INTER t) INTER u = s INTER (t INTER u)`;INTER_EMPTY];ALL_TAC] THEN
ASM_SIMP_TAC[FINITE_INTER;FINITE_BITSET;GSYM CARD_UNION;FINITE_SING];ALL_TAC] THEN SIMP_TAC[] THEN STRIP_TAC
THEN SUBGOAL_THEN`bitset (x - 1) INTER {N} = {}`ASSUME_TAC THENL[SIMP_TAC[BITSET_EQ_BITSNUM] THEN
MP_TAC(SPECL[`x-1`;`N:num`] (GSYM BITS_OF_NUM_SUBSET_NUMSEG_EQ)) THEN ASM_SIMP_TAC[ARITH_RULE`1 <= x ==> x <= a ==> x - 1 < a`]
THEN SET_TAC[LT_REFL];ALL_TAC] THEN SUBGOAL_THEN`(bitset c INTER bitset (x - 1)) INTER {N} = {}`ASSUME_TAC
THENL[ASM_SIMP_TAC[SET_RULE`(s INTER t) INTER u = s INTER (t INTER u)`;INTER_EMPTY];ALL_TAC] THEN
ASM_SIMP_TAC[FINITE_INTER;FINITE_BITSET;CARD_UNION;FINITE_SING];ALL_TAC] THEN
SIMP_TAC[CARD_SING;ARITH_RULE`N + 1 = SUC N`;ODD;NOT_ODD];ALL_TAC] THEN SIMP_TAC[GSYM NOT_ODD] THEN
SIMP_TAC[ARITH_RULE`k < 2 EXP N \/ k = 2 EXP N <=> k <= 2 EXP N`;GSYM IN_NUMSEG] THEN
SIMP_TAC[FINITE_NUMSEG;FINITE_RESTRICT;SET_RULE`{x |x IN s /\ p x /\ q x} INTER {x |x IN s /\ ~p x /\ q x} = {}`;GSYM CARD_UNION]
THEN SIMP_TAC[SET_RULE`{x |x IN s /\ p x /\ q x } UNION {x |x IN s /\ ~p x /\ q x} = {x |x IN s /\ q x}`]
THEN ASM_SIMP_TAC[GSYM bitand];ALL_TAC] THEN
ASM_SIMP_TAC[BITSET_EQ_BITSNUM;BITS_OF_NUM_POW2] THEN
SIMP_TAC[ARITH_RULE`k < 2 EXP N \/ k = 2 EXP N <=> k <= 2 EXP N`;INTER_IDEMPOT] THEN
SUBGOAL_THEN`CARD
 {k | (1 <= k /\ k <= 2 EXP N) /\
      ODD(CARD (bits_of_num c INTER bits_of_num (k - 1)) *
       CARD ({N} INTER bits_of_num (k - 1)))} = 0`SUBST1_TAC THENL[SIMP_TAC[GSYM IN_NUMSEG;FINITE_NUMSEG;FINITE_RESTRICT;CARD_EQ_0]
THEN SIMP_TAC[EXTENSION;IN_ELIM_THM] THEN GEN_TAC THEN SIMP_TAC[IN_NUMSEG] THEN EQ_TAC THENL[STRIP_TAC THEN POP_ASSUM MP_TAC THEN
SUBGOAL_THEN`{N} INTER bits_of_num (x- 1) = {}`SUBST1_TAC THENL[MP_TAC(SPECL[`x-1`;`N:num`] (GSYM BITS_OF_NUM_SUBSET_NUMSEG_EQ))
THEN ASM_SIMP_TAC[ARITH_RULE`1 <= x ==> x <= a ==> x - 1 < a`]
THEN SET_TAC[LT_REFL];ALL_TAC] THEN SIMP_TAC[CARD_CLAUSES;MULT_0;ODD];ALL_TAC] THEN SET_TAC[];ALL_TAC]
THEN SUBGOAL_THEN`{k | (1 <= k /\ k <= 2 EXP N) /\
      ODD(CARD(bits_of_num c INTER bits_of_num (k - 1) UNION
          bits_of_num c INTER {N}) * CARD ({N} INTER bits_of_num (k - 1) UNION {N}))} =
  {k | (1 <= k /\ k <= 2 EXP N) /\
        ODD(CARD (bits_of_num c INTER bits_of_num (k - 1) UNION
          bits_of_num c INTER {N}))}`SUBST1_TAC THENL[SIMP_TAC[EXTENSION;IN_ELIM_THM] THEN GEN_TAC THEN
EQ_TAC THENL[SIMP_TAC[] THEN STRIP_TAC THEN SUBGOAL_THEN`{N} INTER bits_of_num (x - 1) = {}`SUBST1_TAC
THENL[MP_TAC(SPECL[`x-1`;`N:num`] (GSYM BITS_OF_NUM_SUBSET_NUMSEG_EQ))
THEN ASM_SIMP_TAC[ARITH_RULE`1 <= x ==> x <= a ==> x - 1 < a`]
THEN SET_TAC[LT_REFL];ALL_TAC] THEN POP_ASSUM MP_TAC THEN SUBGOAL_THEN`{N} INTER bits_of_num (x - 1) = {}`SUBST1_TAC
THENL[MP_TAC(SPECL[`x-1`;`N:num`] (GSYM BITS_OF_NUM_SUBSET_NUMSEG_EQ))
THEN ASM_SIMP_TAC[ARITH_RULE`1 <= x ==> x <= a ==> x - 1 < a`]
THEN SET_TAC[LT_REFL];ALL_TAC] THEN SIMP_TAC[UNION_EMPTY;CARD_SING;MULT_CLAUSES];ALL_TAC] THEN SIMP_TAC[]
THEN STRIP_TAC THEN SUBGOAL_THEN`{N} INTER bits_of_num (x - 1) = {}`SUBST1_TAC
THENL[MP_TAC(SPECL[`x-1`;`N:num`] (GSYM BITS_OF_NUM_SUBSET_NUMSEG_EQ))
THEN ASM_SIMP_TAC[ARITH_RULE`1 <= x ==> x <= a ==> x - 1 < a`]
THEN SET_TAC[LT_REFL];ALL_TAC] THEN ASM_SIMP_TAC[UNION_EMPTY;CARD_SING;MULT_CLAUSES];ALL_TAC] THEN
SUBGOAL_THEN`bits_of_num c INTER {N} = {N}`SUBST1_TAC THENL[SIMP_TAC[EXTENSION;IN_ELIM_THM;INTER] THEN
UNDISCH_TAC`bitset (c - 2 EXP N + 2 EXP N) = bitset (c - 2 EXP N) UNION {N}` THEN
SUBGOAL_THEN`bitset (c - 2 EXP N + 2 EXP N) = bitset c`SUBST1_TAC THENL[UNDISCH_TAC`2 EXP N < c`
THEN SIMP_TAC[ARITH_RULE`2 EXP N < c ==> c - 2 EXP N + 2 EXP N = c`];ALL_TAC] THEN STRIP_TAC THEN GEN_TAC
THEN ASM_SIMP_TAC[GSYM BITSET_EQ_BITSNUM;IN_UNION] THEN SET_TAC[];ALL_TAC] THEN SIMP_TAC[UNION_COMM;INTER_OVER_UNION]
THEN SIMP_TAC[GSYM BITSET_EQ_BITSNUM] THEN ONCE_REWRITE_TAC[UNION_COMM] THEN UNDISCH_TAC`bitset (c - 2 EXP N + 2 EXP N) = bitset (c - 2 EXP N) UNION {N}`
THEN ASM_SIMP_TAC[ARITH_RULE`2 EXP N < c ==> c - 2 EXP N + 2 EXP N = c`] THEN SIMP_TAC[SET_RULE`(s UNION t) UNION t = s UNION t`]
THEN STRIP_TAC THEN SIMP_TAC[SET_RULE`(s UNION t) INTER (u UNION t) = (s INTER u) UNION t`] THEN
SUBGOAL_THEN`{k | (1 <= k /\ k <= 2 EXP N) /\
        ODD (CARD (bitset (c - 2 EXP N) INTER bitset (k - 1) UNION {N}))} =
  {k | (1 <= k /\ k <= 2 EXP N) /\
          ODD (CARD (bitset (c - 2 EXP N) INTER bitset (k - 1)) + CARD {N})}`SUBST1_TAC THENL[
SIMP_TAC[EXTENSION;IN_ELIM_THM] THEN GEN_TAC THEN REPEAT AP_TERM_TAC
THEN MATCH_MP_TAC CARD_UNION THEN SIMP_TAC[FINITE_BITSET;FINITE_INTER;FINITE_SING] THEN
ASSUME_TAC(SPEC`N:num` BITS_OF_NUM_POW2) THEN SIMP_TAC[BITSET_EQ_BITSNUM;GSYM DISJOINT]
THEN SIMP_TAC[DISJOINT_SING] THEN MP_TAC(SPECL[`c - 2 EXP N`;`N:num`] (GSYM BITS_OF_NUM_SUBSET_NUMSEG_EQ))
THEN UNDISCH_TAC`c < 2 EXP SUC N` THEN UNDISCH_TAC`2 EXP N < c` THEN
SIMP_TAC[ARITH_RULE`c - 2 EXP N  < 2 EXP N <=> c < 2 EXP N + 2 EXP N`]
THEN SIMP_TAC[ARITH_RULE`SUC N = 1 + N`;EXP_ADD;EXP_1;MULT_2] THEN
SET_TAC[LT_REFL];ALL_TAC] THEN
SIMP_TAC[CARD_SING] THEN SIMP_TAC[ARITH_RULE`N + 1 = SUC N`;ODD;NOT_ODD]
THEN MP_TAC(SPECL[`N:num`;`c - 2 EXP N`] BITAND_ODD_CARD) THEN SIMP_TAC[ARITH_RULE`0 < c - a <=> a < c`]
THEN SIMP_TAC[ARITH_RULE`n - 2 EXP N  < 2 EXP N  <=> n < 2 EXP N + 2 EXP N`] THEN
SIMP_TAC[GSYM MULT_2;ARITH_RULE`2 * 2 EXP N = 2 EXP 1 * 2 EXP N `;GSYM EXP_ADD] THEN
ASM_SIMP_TAC[ARITH_RULE`1 + N = SUC N`;ARITH_RULE`1 < N ==> 0 < N`] THEN
MP_TAC(SPECL[`N:num`;`c - 2 EXP N`] (GSYM BITAND_CARD_ODD_EQ_EVEN)) THEN
SIMP_TAC[ARITH_RULE`0 < c - a <=> a < c`]
THEN SIMP_TAC[ARITH_RULE`n - 2 EXP N  < 2 EXP N  <=> n < 2 EXP N + 2 EXP N`] THEN
SIMP_TAC[GSYM MULT_2;ARITH_RULE`2 * 2 EXP N = 2 EXP 1 * 2 EXP N `;GSYM EXP_ADD] THEN
ASM_SIMP_TAC[ARITH_RULE`1 + N = SUC N`;ARITH_RULE`1 < N ==> 0 < N`] THEN SIMP_TAC[bitand;IN_NUMSEG;ADD_CLAUSES];ALL_TAC]
THEN ASM_SIMP_TAC[BITSET_EQ_BITSNUM;BITS_OF_NUM_POW2;INTER_IDEMPOT] THEN
SUBGOAL_THEN`CARD {k | (1 <= k /\ k <= 2 EXP N) /\
      ODD
      (CARD ({N} INTER bits_of_num (k - 1)) *
       CARD (bits_of_num d INTER bits_of_num (k - 1)))} = 0`SUBST1_TAC THENL[SIMP_TAC[GSYM IN_NUMSEG;FINITE_NUMSEG;FINITE_RESTRICT;CARD_EQ_0]
THEN SIMP_TAC[EXTENSION;IN_ELIM_THM] THEN GEN_TAC THEN SIMP_TAC[IN_NUMSEG] THEN EQ_TAC THENL[STRIP_TAC THEN
POP_ASSUM MP_TAC THEN SUBGOAL_THEN`{N} INTER bits_of_num (x- 1) = {}`SUBST1_TAC THENL[MP_TAC(SPECL[`x-1`;`N:num`] (GSYM BITS_OF_NUM_SUBSET_NUMSEG_EQ))
THEN ASM_SIMP_TAC[ARITH_RULE`1 <= x ==> x <= a ==> x - 1 < a`]
THEN SET_TAC[LT_REFL];ALL_TAC] THEN SIMP_TAC[CARD_CLAUSES;MULT_CLAUSES;ODD];ALL_TAC] THEN SET_TAC[];ALL_TAC]
THEN SUBGOAL_THEN`{k | (1 <= k /\ k <= 2 EXP N) /\
      ODD
      (CARD ({N} INTER bits_of_num (k - 1) UNION {N}) *
       CARD
       (bits_of_num d INTER bits_of_num (k - 1) UNION
        bits_of_num d INTER {N}))}          =
  {k | (1 <= k /\ k <= 2 EXP N) /\
      ODD  (CARD
       (bits_of_num d INTER bits_of_num (k - 1) UNION
        bits_of_num d INTER {N}))}    `SUBST1_TAC THENL[SIMP_TAC[EXTENSION;IN_ELIM_THM] THEN GEN_TAC THEN
EQ_TAC THENL[SIMP_TAC[] THEN STRIP_TAC THEN SUBGOAL_THEN`{N} INTER bits_of_num (x - 1) = {}`SUBST1_TAC
THENL[MP_TAC(SPECL[`x-1`;`N:num`] (GSYM BITS_OF_NUM_SUBSET_NUMSEG_EQ))
THEN ASM_SIMP_TAC[ARITH_RULE`1 <= x ==> x <= a ==> x - 1 < a`]
THEN SET_TAC[LT_REFL];ALL_TAC] THEN POP_ASSUM MP_TAC THEN SUBGOAL_THEN`{N} INTER bits_of_num (x - 1) = {}`SUBST1_TAC
THENL[MP_TAC(SPECL[`x-1`;`N:num`] (GSYM BITS_OF_NUM_SUBSET_NUMSEG_EQ))
THEN ASM_SIMP_TAC[ARITH_RULE`1 <= x ==> x <= a ==> x - 1 < a`]
THEN SET_TAC[LT_REFL];ALL_TAC] THEN SIMP_TAC[UNION_EMPTY;CARD_SING;MULT_CLAUSES];ALL_TAC] THEN SIMP_TAC[]
THEN STRIP_TAC THEN SUBGOAL_THEN`{N} INTER bits_of_num (x - 1) = {}`SUBST1_TAC
THENL[MP_TAC(SPECL[`x-1`;`N:num`] (GSYM BITS_OF_NUM_SUBSET_NUMSEG_EQ))
THEN ASM_SIMP_TAC[ARITH_RULE`1 <= x ==> x <= a ==> x - 1 < a`]
THEN SET_TAC[LT_REFL];ALL_TAC] THEN ASM_SIMP_TAC[UNION_EMPTY;CARD_SING;MULT_CLAUSES];ALL_TAC] THEN
ASM_CASES_TAC`d < 2 EXP N ` THENL[SUBGOAL_THEN`bits_of_num d INTER {N} = {}`SUBST1_TAC THENL[
MP_TAC(SPECL[`d:num`;`N:num`] (GSYM BITS_OF_NUM_SUBSET_NUMSEG_EQ)) THEN ASM_SIMP_TAC[] THEN SET_TAC[LT_REFL];ALL_TAC]
THEN SIMP_TAC[UNION_EMPTY] THEN MP_TAC(SPECL[`N:num`;`d:num`] BITAND_ODD_CARD) THEN
ASM_SIMP_TAC[ARITH_RULE`1 < N ==> 0 < N`;bitand;BITSET_EQ_BITSNUM;IN_NUMSEG;ADD_CLAUSES];ALL_TAC]
THEN POP_ASSUM MP_TAC THEN SIMP_TAC[ARITH_RULE`~(d < 2 EXP N) <=> 2 EXP N <= d`] THEN
GEN_REWRITE_TAC(LAND_CONV o ONCE_DEPTH_CONV)[ARITH_RULE`2 EXP N <= d <=> d =  2 EXP N \/ 2 EXP N < d`] THEN
STRIP_TAC THENL[UNDISCH_TAC`d = 2 EXP N` THEN ASM_ARITH_TAC;ALL_TAC] THEN
UNDISCH_TAC`bitset (d - 2 EXP N + 2 EXP N) = bitset (d - 2 EXP N) UNION {N}` THEN
ASM_SIMP_TAC[ARITH_RULE`2 EXP N < d ==> d - 2 EXP N + 2 EXP N = d`] THEN SIMP_TAC[BITSET_EQ_BITSNUM]
THEN SIMP_TAC[SET_RULE`(s UNION t) INTER t = s INTER t UNION t`] THEN SIMP_TAC[ SET_RULE`s INTER t UNION t = t`]
THEN SIMP_TAC[SET_RULE`(s UNION t) INTER  u = s INTER u UNION t INTER u`] THEN
SUBGOAL_THEN`{k | (1 <= k /\ k <= 2 EXP N) /\
ODD(CARD((bits_of_num (d - 2 EXP N) INTER bits_of_num (k - 1) UNION
    {N} INTER bits_of_num (k - 1)) UNION {N}))} = {k | (1 <= k /\ k <= 2 EXP N) /\
ODD(CARD ((bits_of_num (d - 2 EXP N) INTER bits_of_num (k - 1)) UNION {N} ))}`SUBST1_TAC THENL[
SIMP_TAC[IN_ELIM_THM;EXTENSION] THEN GEN_TAC THEN EQ_TAC THENL[STRIP_TAC THEN ASM_SIMP_TAC[]
THEN POP_ASSUM MP_TAC THEN SUBGOAL_THEN`{N} INTER bits_of_num (x - 1) = {}`SUBST1_TAC THENL[
MP_TAC(SPECL[`x-1`;`N:num`] (GSYM BITS_OF_NUM_SUBSET_NUMSEG_EQ))
THEN ASM_SIMP_TAC[ARITH_RULE`1 <= x ==> x <= a ==> x - 1 < a`]
THEN SET_TAC[LT_REFL];ALL_TAC] THEN SIMP_TAC[UNION_EMPTY];ALL_TAC] THEN SIMP_TAC[] THEN STRIP_TAC
THEN SUBGOAL_THEN`{N} INTER bits_of_num (x - 1) = {}`SUBST1_TAC THENL[
MP_TAC(SPECL[`x-1`;`N:num`] (GSYM BITS_OF_NUM_SUBSET_NUMSEG_EQ))
THEN ASM_SIMP_TAC[ARITH_RULE`1 <= x ==> x <= a ==> x - 1 < a`]
THEN SET_TAC[LT_REFL];ALL_TAC] THEN SUBGOAL_THEN`{N} INTER bits_of_num (x - 1) = {}`SUBST1_TAC THENL[
MP_TAC(SPECL[`x-1`;`N:num`] (GSYM BITS_OF_NUM_SUBSET_NUMSEG_EQ))
THEN ASM_SIMP_TAC[ARITH_RULE`1 <= x ==> x <= a ==> x - 1 < a`] THEN SET_TAC[LT_REFL];ALL_TAC] THEN
ASM_SIMP_TAC[UNION_EMPTY];ALL_TAC] THEN STRIP_TAC THEN SUBGOAL_THEN`{k | (1 <= k /\ k <= 2 EXP N) /\
      ODD(CARD (bits_of_num (d - 2 EXP N) INTER bits_of_num (k - 1) UNION {N}))} =
  {k | (1 <= k /\ k <= 2 EXP N) /\ ODD  (CARD (bits_of_num (d - 2 EXP N) INTER bits_of_num (k - 1))
  + CARD {N})}`SUBST1_TAC THENL[SIMP_TAC[EXTENSION;IN_ELIM_THM] THEN GEN_TAC THEN
REPEAT AP_TERM_TAC THEN MATCH_MP_TAC CARD_UNION THEN SIMP_TAC[FINITE_BITS_OF_NUM;FINITE_INTER;FINITE_SING]
THEN ASSUME_TAC(SPEC`N:num` BITS_OF_NUM_POW2) THEN SIMP_TAC[BITSET_EQ_BITSNUM;GSYM DISJOINT] THEN
SIMP_TAC[DISJOINT_SING] THEN MP_TAC(SPECL[`d - 2 EXP N`;`N:num`] (GSYM BITS_OF_NUM_SUBSET_NUMSEG_EQ))
THEN UNDISCH_TAC`d < 2 EXP SUC N` THEN UNDISCH_TAC`2 EXP N < d` THEN SIMP_TAC[ARITH_RULE`d - 2 EXP N  < 2 EXP N <=> d < 2 EXP N + 2 EXP N`]
THEN SIMP_TAC[ARITH_RULE`SUC N = 1 + N`;EXP_ADD;EXP_1;MULT_2] THEN SET_TAC[LT_REFL];ALL_TAC] THEN
SIMP_TAC[CARD_SING;ARITH_RULE`N + 1 = SUC N`;ODD;NOT_ODD;GSYM IN_NUMSEG] THEN MP_TAC(SPECL[`N:num`;`d - 2 EXP N`] BITAND_ODD_CARD)
THEN SIMP_TAC[ARITH_RULE`0 < c - a <=> a < c`] THEN
SIMP_TAC[ARITH_RULE`n - 2 EXP N  < 2 EXP N  <=> n < 2 EXP N + 2 EXP N`] THEN
SIMP_TAC[GSYM MULT_2;ARITH_RULE`2 * 2 EXP N = 2 EXP 1 * 2 EXP N `;GSYM EXP_ADD] THEN
ASM_SIMP_TAC[ARITH_RULE`1 + N = SUC N`;ARITH_RULE`1 < N ==> 0 < N`] THEN STRIP_TAC THEN
MP_TAC(SPECL[`N:num`;`d - 2 EXP N`] (GSYM BITAND_CARD_ODD_EQ_EVEN)) THEN SIMP_TAC[ARITH_RULE`0 < c - a <=> a < c`] THEN
SIMP_TAC[ARITH_RULE`n - 2 EXP N  < 2 EXP N  <=> n < 2 EXP N + 2 EXP N`] THEN
SIMP_TAC[GSYM MULT_2;ARITH_RULE`2 * 2 EXP N = 2 EXP 1 * 2 EXP N `;GSYM EXP_ADD] THEN
ASM_SIMP_TAC[ARITH_RULE`1 + N = SUC N`;ARITH_RULE`1 < N ==> 0 < N`] THEN SIMP_TAC[bitand;BITSET_EQ_BITSNUM;ADD_CLAUSES];ALL_TAC]
THEN RULE_ASSUM_TAC(SIMP_RULE[ARITH_RULE`2 EXP N <= d <=> d = 2 EXP N \/ 2 EXP N < d`]) THEN POP_ASSUM MP_TAC
THEN STRIP_TAC THENL
[ASM_SIMP_TAC[BITSET_EQ_BITSNUM;BITS_OF_NUM_POW2;INTER_IDEMPOT] THEN
SIMP_TAC[SET_RULE`s INTER t UNION s = s`;CARD_SING;MULT_CLAUSES] THEN SUBGOAL_THEN`CARD {k | (1 <= k /\ k <= 2 EXP N) /\
      ODD
          (CARD (bits_of_num c INTER bits_of_num (k - 1)) *
         CARD ({N} INTER bits_of_num (k - 1)))} = 0`SUBST1_TAC
THENL[SIMP_TAC[GSYM IN_NUMSEG;FINITE_NUMSEG;FINITE_RESTRICT;CARD_EQ_0]
THEN SIMP_TAC[EXTENSION;IN_ELIM_THM] THEN GEN_TAC THEN SIMP_TAC[IN_NUMSEG] THEN EQ_TAC THENL[STRIP_TAC THEN POP_ASSUM MP_TAC THEN
SUBGOAL_THEN`{N} INTER bits_of_num (x- 1) = {}`SUBST1_TAC THENL[MP_TAC(SPECL[`x-1`;`N:num`] (GSYM BITS_OF_NUM_SUBSET_NUMSEG_EQ))
THEN ASM_SIMP_TAC[ARITH_RULE`1 <= x ==> x <= a ==> x - 1 < a`]
THEN SET_TAC[LT_REFL];ALL_TAC] THEN SIMP_TAC[CARD_CLAUSES;MULT_0;ODD];ALL_TAC] THEN SET_TAC[];ALL_TAC] THEN
ASM_CASES_TAC`2 EXP N < c` THENL[MP_TAC(SPECL[`c - 2 EXP N`;`N:num`]BITSET_ADD) THEN
ASM_SIMP_TAC[ARITH_RULE`n - 2 EXP N  < 2 EXP N  <=> n < 2 EXP N + 2 EXP N`] THEN
RULE_ASSUM_TAC(SIMP_RULE[ARITH_RULE`SUC N = 1 + N`;EXP_ADD;EXP_1;MULT_2]) THEN
ASM_SIMP_TAC[ARITH_RULE`2 EXP N < c ==> c - 2 EXP N + 2 EXP N = c`] THEN STRIP_TAC THEN
ASM_SIMP_TAC[GSYM BITSET_EQ_BITSNUM;IN_UNION] THEN SIMP_TAC[SET_RULE`(s UNION t) INTER t = t`]
THEN SIMP_TAC[SET_RULE`(s UNION t) INTER u = s INTER u UNION t INTER u`] THEN SUBGOAL_THEN`{k | (1 <= k /\ k <= 2 EXP N) /\
      ODD(CARD ((bitset (c - 2 EXP N) INTER bitset (k - 1) UNION
{N} INTER bitset (k - 1)) UNION {N}))} = {k | (1 <= k /\ k <= 2 EXP N) /\
      ODD(CARD (bitset (c - 2 EXP N) INTER bitset (k - 1) UNION {N}))}`SUBST1_TAC THENL[SIMP_TAC[EXTENSION;IN_ELIM_THM] THEN GEN_TAC
THEN EQ_TAC THENL[SIMP_TAC[] THEN STRIP_TAC THEN SUBGOAL_THEN`{N} INTER bits_of_num (x - 1) = {}`SUBST1_TAC
THENL[MP_TAC(SPECL[`x-1`;`N:num`] (GSYM BITS_OF_NUM_SUBSET_NUMSEG_EQ))
THEN ASM_SIMP_TAC[ARITH_RULE`1 <= x ==> x <= a ==> x - 1 < a`]
THEN SET_TAC[LT_REFL];ALL_TAC] THEN POP_ASSUM MP_TAC THEN SUBGOAL_THEN`{N} INTER bits_of_num (x - 1) = {}`SUBST1_TAC
THENL[MP_TAC(SPECL[`x-1`;`N:num`] (GSYM BITS_OF_NUM_SUBSET_NUMSEG_EQ))
THEN ASM_SIMP_TAC[ARITH_RULE`1 <= x ==> x <= a ==> x - 1 < a`]
THEN SET_TAC[LT_REFL];ALL_TAC]
THEN SIMP_TAC[BITSET_EQ_BITSNUM]
THEN SUBGOAL_THEN`{N} INTER bits_of_num (x - 1) = {}`SUBST1_TAC
THENL[MP_TAC(SPECL[`x-1`;`N:num`] (GSYM BITS_OF_NUM_SUBSET_NUMSEG_EQ))
THEN ASM_SIMP_TAC[ARITH_RULE`1 <= x ==> x <= a ==> x - 1 < a`]
THEN SET_TAC[LT_REFL];ALL_TAC] THEN SIMP_TAC[UNION_EMPTY;CARD_SING;MULT_CLAUSES];ALL_TAC] THEN
SIMP_TAC[BITSET_EQ_BITSNUM] THEN STRIP_TAC THEN SUBGOAL_THEN`{N} INTER bits_of_num (x - 1) = {}`SUBST1_TAC
THENL[MP_TAC(SPECL[`x-1`;`N:num`] (GSYM BITS_OF_NUM_SUBSET_NUMSEG_EQ))
THEN ASM_SIMP_TAC[ARITH_RULE`1 <= x ==> x <= a ==> x - 1 < a`]
THEN SET_TAC[LT_REFL];ALL_TAC] THEN ASM_SIMP_TAC[UNION_EMPTY;CARD_SING;MULT_CLAUSES];ALL_TAC]
THEN SIMP_TAC[BITSET_EQ_BITSNUM] THEN SUBGOAL_THEN`{k | (1 <= k /\ k <= 2 EXP N) /\
      ODD(CARD (bits_of_num (c - 2 EXP N) INTER bits_of_num (k - 1) UNION {N}))} =
  {k | (1 <= k /\ k <= 2 EXP N) /\ ODD  (CARD (bits_of_num (c - 2 EXP N) INTER bits_of_num (k - 1))
  + CARD {N})}`SUBST1_TAC THENL[SIMP_TAC[EXTENSION;IN_ELIM_THM] THEN GEN_TAC THEN
REPEAT AP_TERM_TAC THEN MATCH_MP_TAC CARD_UNION THEN SIMP_TAC[FINITE_BITS_OF_NUM;FINITE_INTER;FINITE_SING]
THEN ASSUME_TAC(SPEC`N:num` BITS_OF_NUM_POW2) THEN SIMP_TAC[BITSET_EQ_BITSNUM;GSYM DISJOINT] THEN
SIMP_TAC[DISJOINT_SING] THEN MP_TAC(SPECL[`c - 2 EXP N`;`N:num`] (GSYM BITS_OF_NUM_SUBSET_NUMSEG_EQ))
THEN UNDISCH_TAC`c < 2 EXP N + 2 EXP N` THEN UNDISCH_TAC`2 EXP N < c` THEN SIMP_TAC[ARITH_RULE`c < 2 EXP N + 2 EXP N <=> c - 2 EXP N  < 2 EXP N`]
THEN SET_TAC[LT_REFL];ALL_TAC] THEN
SIMP_TAC[CARD_SING] THEN SIMP_TAC[ARITH_RULE`N + 1 = SUC N`;ODD;NOT_ODD;GSYM IN_NUMSEG]
THEN MP_TAC(SPECL[`N:num`;`c - 2 EXP N`] BITAND_ODD_CARD) THEN
SIMP_TAC[ARITH_RULE`0 < c - a <=> a < c`;ARITH_RULE`n - 2 EXP N  < 2 EXP N  <=> n < 2 EXP N + 2 EXP N`]
THEN ASM_SIMP_TAC[bitand;ARITH_RULE`0 < N <=> 1 < 1 + N`;ADD] THEN STRIP_TAC THEN
MP_TAC(SPECL[`N:num`;`c - 2 EXP N`] (GSYM BITAND_CARD_ODD_EQ_EVEN)) THEN SIMP_TAC[ARITH_RULE`0 < c - a <=> a < c`]
THEN ASM_SIMP_TAC[ARITH_RULE`n - 2 EXP N  < 2 EXP N  <=> n < 2 EXP N + 2 EXP N`;ARITH_RULE`0 < N <=> 1 < 1 + N`;bitand;GSYM BITSET_EQ_BITSNUM];ALL_TAC]
THEN RULE_ASSUM_TAC(SIMP_RULE[NOT_LT;LE_LT]) THEN POP_ASSUM MP_TAC THEN MP_TAC(ARITH_RULE`~(c = d:num) /\ d = 2 EXP N ==> ~(c = 2 EXP N)`)
THEN ASM_SIMP_TAC[] THEN REPEAT STRIP_TAC THEN SIMP_TAC[GSYM BITSET_EQ_BITSNUM] THEN
SUBGOAL_THEN`bitset c INTER {N} = {}`SUBST1_TAC THENL[SIMP_TAC[BITSET_EQ_BITSNUM] THEN
MP_TAC(SPECL[`c:num`;`N:num`] (GSYM BITS_OF_NUM_SUBSET_NUMSEG_EQ)) THEN ASM_SIMP_TAC[] THEN SET_TAC[LT_REFL];ALL_TAC]
THEN SIMP_TAC[UNION_EMPTY;GSYM bitand;ADD;GSYM IN_NUMSEG] THEN MP_TAC(SPECL[`N:num`;`c:num`] BITAND_ODD_CARD)
THEN ASM_SIMP_TAC[ARITH_RULE`0 < N <=> 1 < SUC N`];ALL_TAC] THEN
MP_TAC(SPECL[`d - 2 EXP N`;`N:num`] BITSET_ADD) THEN SIMP_TAC[ARITH_RULE`n - 2 EXP N  < 2 EXP N  <=> n < 2 EXP N + 2 EXP N`]
THEN SIMP_TAC[GSYM MULT_2;ARITH_RULE`2 * 2 EXP N = 2 EXP 1 * 2 EXP N `;GSYM EXP_ADD] THEN ASM_SIMP_TAC[ARITH_RULE`1 + N = SUC N`]
THEN SUBGOAL_THEN`bitset (d - 2 EXP N + 2 EXP N) = bitset d`SUBST1_TAC THENL[ASM_SIMP_TAC[ARITH_RULE`2 EXP N < d ==> d - 2 EXP N + 2 EXP N = d`];ALL_TAC]
THEN STRIP_TAC THEN SUBGOAL_THEN`bitset d INTER {N} = {N}`SUBST1_TAC THENL[SIMP_TAC[INTER;IN_ELIM_THM;EXTENSION] THEN ASM_SIMP_TAC[IN_UNION] THEN
SET_TAC[];ALL_TAC] THEN
ASM_CASES_TAC`c < 2 EXP N` THENL[SIMP_TAC[BITSET_EQ_BITSNUM] THEN SUBGOAL_THEN`bits_of_num c INTER {N} = {}`SUBST1_TAC THENL[
MP_TAC(SPECL[`c:num`;`N:num`] (GSYM BITS_OF_NUM_SUBSET_NUMSEG_EQ)) THEN ASM_SIMP_TAC[] THEN SET_TAC[LT_REFL];ALL_TAC] THEN
SIMP_TAC[UNION_EMPTY] THEN ASM_SIMP_TAC[] THEN SUBGOAL_THEN`{k | (1 <= k /\ k <= 2 EXP N) /\
      ODD
      (CARD (bits_of_num c INTER bits_of_num (k - 1)) *
       CARD (bits_of_num d INTER bits_of_num (k - 1)))} =
       {k | (1 <= k /\ k <= 2 EXP N) /\
      ODD
      (CARD (bits_of_num c INTER bits_of_num (k - 1)) *
       CARD (bitset (d - 2 EXP N) INTER bits_of_num (k - 1)))}`SUBST1_TAC THENL[SIMP_TAC[EXTENSION;IN_ELIM_THM] THEN GEN_TAC THEN EQ_TAC
THENL[SIMP_TAC[GSYM BITSET_EQ_BITSNUM] THEN ASM_SIMP_TAC[] THEN SIMP_TAC[SET_RULE`(s UNION t) INTER u = s INTER u UNION t INTER u`]
THEN STRIP_TAC THEN POP_ASSUM MP_TAC THEN SUBGOAL_THEN`{N} INTER bitset (x- 1) = {}`SUBST1_TAC THENL[ASSUME_TAC(SPEC`N:num` BITS_OF_NUM_POW2) THEN SIMP_TAC[BITSET_EQ_BITSNUM;GSYM DISJOINT]
THEN SIMP_TAC[DISJOINT_SING] THEN MP_TAC(SPECL[`x-1`;`N:num`] (GSYM BITS_OF_NUM_SUBSET_NUMSEG_EQ))
THEN UNDISCH_TAC`x <= 2 EXP N` THEN UNDISCH_TAC`1 <= x` THEN
SIMP_TAC[ARITH_RULE`1 <= x ==> x <= 2 EXP N ==> x - 1  < 2 EXP N`] THEN
SET_TAC[LT_REFL];ALL_TAC] THEN SIMP_TAC[UNION_EMPTY];ALL_TAC] THEN ASM_SIMP_TAC[GSYM BITSET_EQ_BITSNUM] THEN
SIMP_TAC[SET_RULE`(s UNION t) INTER u = s INTER u UNION t INTER u`] THEN STRIP_TAC THEN POP_ASSUM MP_TAC THEN
SUBGOAL_THEN`{N} INTER bitset (x- 1) = {}`SUBST1_TAC THENL[ASSUME_TAC(SPEC`N:num` BITS_OF_NUM_POW2) THEN SIMP_TAC[BITSET_EQ_BITSNUM;GSYM DISJOINT]
THEN SIMP_TAC[DISJOINT_SING] THEN MP_TAC(SPECL[`x-1`;`N:num`] (GSYM BITS_OF_NUM_SUBSET_NUMSEG_EQ))
THEN UNDISCH_TAC`x <= 2 EXP N` THEN UNDISCH_TAC`1 <= x` THEN
SIMP_TAC[ARITH_RULE`1 <= x ==> x <= 2 EXP N ==> x - 1  < 2 EXP N`] THEN
SET_TAC[LT_REFL];ALL_TAC] THEN SIMP_TAC[UNION_EMPTY];ALL_TAC] THEN
ASM_SIMP_TAC[GSYM BITSET_EQ_BITSNUM] THEN
SIMP_TAC[SET_RULE`(s UNION t) INTER u = s INTER u UNION t INTER u`] THEN
SIMP_TAC[SET_RULE`(s UNION t) UNION u = s UNION t UNION u`;SET_RULE`s INTER u UNION s = s`] THEN
SUBGOAL_THEN`{k | (1 <= k /\ k <= 2 EXP N) /\
      ODD(CARD (bitset c INTER bitset (k - 1)) *
       CARD (bitset (d - 2 EXP N) INTER bitset (k - 1) UNION {N}))} =
       {k | (1 <= k /\ k <= 2 EXP N) /\
      ODD(CARD (bitset c INTER bitset (k - 1)) *
       (CARD (bitset (d - 2 EXP N) INTER bitset (k - 1)) + CARD{N}))}`SUBST1_TAC THENL[SIMP_TAC[EXTENSION;IN_ELIM_THM] THEN GEN_TAC THEN
REPEAT AP_TERM_TAC THEN MATCH_MP_TAC CARD_UNION THEN SIMP_TAC[FINITE_BITSET;FINITE_INTER;FINITE_SING] THEN
SIMP_TAC[BITSET_EQ_BITSNUM;GSYM DISJOINT] THEN SIMP_TAC[DISJOINT_SING] THEN MP_TAC(SPECL[`d - 2 EXP N`;`N:num`] (GSYM BITS_OF_NUM_SUBSET_NUMSEG_EQ))
THEN RULE_ASSUM_TAC(SIMP_RULE[ARITH_RULE`SUC N = 1 + N`;EXP_ADD;EXP_1;MULT_2]) THEN UNDISCH_TAC`d < 2 EXP N + 2 EXP N` THEN UNDISCH_TAC`2 EXP N < d` THEN SIMP_TAC[ARITH_RULE`c < 2 EXP N + 2 EXP N <=> c - 2 EXP N  < 2 EXP N`] THEN SET_TAC[LT_REFL];ALL_TAC] THEN
SIMP_TAC[CARD_SING;ODD_MULT;ARITH_RULE`N + 1 = SUC N`;ODD;NOT_ODD;GSYM IN_NUMSEG] THEN MP_TAC(SPECL[`N:num`;`c:num`] BITAND_ODD_CARD)
THEN ASM_SIMP_TAC[ARITH_RULE`1 < N ==> 0 < N`] THEN
SIMP_TAC[FINITE_NUMSEG;FINITE_RESTRICT;SET_RULE`{x |x IN s /\ p x /\ q x} INTER {x |x IN s /\ p x /\ ~q x} = {}`;GSYM CARD_UNION;GSYM NOT_ODD]
THEN SIMP_TAC[SET_RULE`{x |x IN s /\ p x /\ q x} UNION {x |x IN s /\ p x /\ ~q x} = {x |x IN s /\ p x}`;bitand];ALL_TAC]
THEN RULE_ASSUM_TAC(SIMP_RULE[ARITH_RULE`~(c < 2 EXP N) <=> c = 2 EXP N \/ 2 EXP N < c `]) THEN POP_ASSUM MP_TAC THEN
STRIP_TAC THENL[
ASM_SIMP_TAC[BITSET_EQ_BITSNUM;BITS_OF_NUM_POW2;INTER_IDEMPOT] THEN SIMP_TAC[SET_RULE`s INTER u UNION s = s`;SET_RULE`(s UNION {N}) INTER u UNION {N} = s INTER u UNION {N}`;CARD_SING;MULT_CLAUSES] THEN SUBGOAL_THEN`CARD
 {k | (1 <= k /\ k <= 2 EXP N) /\
      ODD
      (CARD ({N} INTER bits_of_num (k - 1)) *
       CARD ((bits_of_num (d - 2 EXP N) UNION {N}) INTER bits_of_num (k - 1)))} = 0`SUBST1_TAC THENL[SIMP_TAC[GSYM IN_NUMSEG;FINITE_NUMSEG;FINITE_RESTRICT;CARD_EQ_0]
THEN SIMP_TAC[EXTENSION;IN_ELIM_THM] THEN GEN_TAC THEN SIMP_TAC[IN_NUMSEG] THEN EQ_TAC THENL[STRIP_TAC THEN
POP_ASSUM MP_TAC THEN SUBGOAL_THEN`{N} INTER bits_of_num (x- 1) = {}`SUBST1_TAC THENL[MP_TAC(SPECL[`x-1`;`N:num`] (GSYM BITS_OF_NUM_SUBSET_NUMSEG_EQ))
THEN ASM_SIMP_TAC[ARITH_RULE`1 <= x ==> x <= a ==> x - 1 < a`]
THEN SET_TAC[LT_REFL];ALL_TAC] THEN SIMP_TAC[CARD_CLAUSES;MULT_CLAUSES;ODD];ALL_TAC] THEN SET_TAC[];ALL_TAC] THEN
SUBGOAL_THEN`{k | (1 <= k /\ k <= 2 EXP N) /\
      ODD(CARD (bits_of_num (d - 2 EXP N) INTER bits_of_num (k - 1) UNION {N}))} =
      {k | (1 <= k /\ k <= 2 EXP N) /\
      ODD(CARD (bits_of_num (d - 2 EXP N) INTER bits_of_num (k - 1)) + CARD {N})}`SUBST1_TAC THENL[RULE_ASSUM_TAC(SIMP_RULE[ARITH_RULE`SUC N = 1 + N`;EXP_ADD;EXP_1;MULT_2]) THEN SIMP_TAC[EXTENSION;IN_ELIM_THM] THEN GEN_TAC THEN
REPEAT AP_TERM_TAC THEN MATCH_MP_TAC CARD_UNION THEN SIMP_TAC[FINITE_BITS_OF_NUM;FINITE_INTER;FINITE_SING]
THEN ASSUME_TAC(SPEC`N:num` BITS_OF_NUM_POW2) THEN SIMP_TAC[BITSET_EQ_BITSNUM;GSYM DISJOINT] THEN
SIMP_TAC[DISJOINT_SING] THEN MP_TAC(SPECL[`d - 2 EXP N`;`N:num`] (GSYM BITS_OF_NUM_SUBSET_NUMSEG_EQ))
THEN UNDISCH_TAC`d < 2 EXP N + 2 EXP N` THEN UNDISCH_TAC`2 EXP N < d` THEN SIMP_TAC[ARITH_RULE`c < 2 EXP N + 2 EXP N <=> c - 2 EXP N  < 2 EXP N`]
THEN SET_TAC[LT_REFL];ALL_TAC] THEN
SIMP_TAC[CARD_SING;ARITH_RULE`N + 1 = SUC N`;ODD;NOT_ODD;GSYM IN_NUMSEG;GSYM BITSET_EQ_BITSNUM;GSYM bitand] THEN
 MP_TAC(SPECL[`N:num`;`d - 2 EXP N`] BITAND_ODD_CARD) THEN SIMP_TAC[ARITH_RULE`0 < c - a <=> a < c`;ARITH_RULE`n - 2 EXP N  < 2 EXP N  <=> n < 2 EXP N + 2 EXP N`] THEN SIMP_TAC[GSYM MULT_2;ARITH_RULE`2 * 2 EXP N = 2 EXP 1 * 2 EXP N `;GSYM EXP_ADD] THEN
ASM_SIMP_TAC[ARITH_RULE`1 + N = SUC N`;ARITH_RULE`1 < N ==> 0 < N`] THEN STRIP_TAC THEN
MP_TAC(SPECL[`N:num`;`d - 2 EXP N`] (GSYM BITAND_CARD_ODD_EQ_EVEN)) THEN SIMP_TAC[ARITH_RULE`0 < c - a <=> a < c`] THEN
SIMP_TAC[ARITH_RULE`n - 2 EXP N  < 2 EXP N  <=> n < 2 EXP N + 2 EXP N`] THEN
SIMP_TAC[GSYM MULT_2;ARITH_RULE`2 * 2 EXP N = 2 EXP 1 * 2 EXP N `;GSYM EXP_ADD] THEN
ASM_SIMP_TAC[ARITH_RULE`1 + N = SUC N`;ARITH_RULE`1 < N ==> 0 < N`;ADD];ALL_TAC] THEN
MP_TAC (SPECL[`c - 2 EXP N`;`N:num`] BITSET_ADD) THEN SIMP_TAC[ARITH_RULE`n - 2 EXP N  < 2 EXP N  <=> n < 2 EXP N + 2 EXP N`]
THEN SIMP_TAC[GSYM MULT_2;ARITH_RULE`2 * 2 EXP N = 2 EXP 1 * 2 EXP N `;GSYM EXP_ADD] THEN ASM_SIMP_TAC[ARITH_RULE`1 + N = SUC N`] THEN
ASM_SIMP_TAC[ARITH_RULE`2 EXP N < c ==> c - 2 EXP N + 2 EXP N = c`] THEN STRIP_TAC THEN SIMP_TAC[SET_RULE`(s UNION t) INTER t = t`]
THEN SUBGOAL_THEN`{k | (1 <= k /\ k <= 2 EXP N) /\
      ODD
      (  CARD ((bitset (c - 2 EXP N) UNION {N}) INTER bitset (k - 1)) *
         CARD ((bitset (d - 2 EXP N) UNION {N}) INTER bitset (k - 1)))} =
  {k | (1 <= k /\ k <= 2 EXP N) /\
        ODD(CARD(bitset (c - 2 EXP N) INTER bitset (k - 1)) *
  CARD(bitset (d - 2 EXP N) INTER bitset (k - 1)))}`SUBST1_TAC THENL[SIMP_TAC[SET_RULE`(s UNION t) INTER u = s INTER u UNION t INTER u`]
THEN SIMP_TAC[EXTENSION;IN_ELIM_THM] THEN GEN_TAC THEN EQ_TAC THENL[SIMP_TAC[] THEN STRIP_TAC THEN POP_ASSUM MP_TAC THEN
SIMP_TAC[BITSET_EQ_BITSNUM] THEN SUBGOAL_THEN`{N} INTER bits_of_num (x - 1) = {}`SUBST1_TAC
THENL[MP_TAC(SPECL[`x-1`;`N:num`] (GSYM BITS_OF_NUM_SUBSET_NUMSEG_EQ))
THEN ASM_SIMP_TAC[ARITH_RULE`1 <= x ==> x <= a ==> x - 1 < a`]
THEN SET_TAC[LT_REFL];ALL_TAC] THEN SIMP_TAC[UNION_EMPTY];ALL_TAC] THEN SIMP_TAC[] THEN STRIP_TAC THEN POP_ASSUM MP_TAC
THEN SIMP_TAC[BITSET_EQ_BITSNUM] THEN SUBGOAL_THEN`{N} INTER bits_of_num (x - 1) = {}`SUBST1_TAC
THENL[MP_TAC(SPECL[`x-1`;`N:num`] (GSYM BITS_OF_NUM_SUBSET_NUMSEG_EQ))
THEN ASM_SIMP_TAC[ARITH_RULE`1 <= x ==> x <= a ==> x - 1 < a`]
THEN SET_TAC[LT_REFL];ALL_TAC] THEN SIMP_TAC[UNION_EMPTY];ALL_TAC] THEN
SUBGOAL_THEN`{k | (1 <= k /\ k <= 2 EXP N) /\
      ODD(CARD ((bitset (c - 2 EXP N) UNION {N}) INTER bitset (k - 1) UNION {N}) *
       CARD ((bitset (d - 2 EXP N) UNION {N}) INTER bitset (k - 1) UNION {N}))} =
       {k | (1 <= k /\ k <= 2 EXP N) /\
      ODD(CARD (bitset (c - 2 EXP N) INTER bitset (k - 1) UNION {N}) *
       CARD (bitset (d - 2 EXP N) INTER bitset (k - 1) UNION {N}))}`SUBST1_TAC THENL[SIMP_TAC[SET_RULE`(s UNION t) INTER u = s INTER u UNION t INTER u`]
       THEN SIMP_TAC[EXTENSION;IN_ELIM_THM] THEN GEN_TAC
THEN EQ_TAC THENL[SIMP_TAC[] THEN STRIP_TAC THEN POP_ASSUM MP_TAC THEN SIMP_TAC[BITSET_EQ_BITSNUM] THEN SUBGOAL_THEN`{N} INTER bits_of_num (x - 1) = {}`SUBST1_TAC
THENL[MP_TAC(SPECL[`x-1`;`N:num`] (GSYM BITS_OF_NUM_SUBSET_NUMSEG_EQ))
THEN ASM_SIMP_TAC[ARITH_RULE`1 <= x ==> x <= a ==> x - 1 < a`]
THEN SET_TAC[LT_REFL];ALL_TAC] THEN SIMP_TAC[UNION_EMPTY];ALL_TAC] THEN SIMP_TAC[] THEN STRIP_TAC THEN POP_ASSUM MP_TAC
THEN SIMP_TAC[BITSET_EQ_BITSNUM] THEN SUBGOAL_THEN`{N} INTER bits_of_num (x - 1) = {}`SUBST1_TAC
THENL[MP_TAC(SPECL[`x-1`;`N:num`] (GSYM BITS_OF_NUM_SUBSET_NUMSEG_EQ))
THEN ASM_SIMP_TAC[ARITH_RULE`1 <= x ==> x <= a ==> x - 1 < a`]
THEN SET_TAC[LT_REFL];ALL_TAC] THEN SIMP_TAC[UNION_EMPTY];ALL_TAC] THEN
SUBGOAL_THEN`{k | (1 <= k /\ k <= 2 EXP N) /\
      ODD(CARD (bitset (c - 2 EXP N) INTER bitset (k - 1) UNION {N}) *
       CARD (bitset (d - 2 EXP N) INTER bitset (k - 1) UNION {N}))} =
       {k | (1 <= k /\ k <= 2 EXP N) /\
      ODD((CARD (bitset (c - 2 EXP N) INTER bitset (k - 1)) + CARD {N}) *
      (CARD (bitset (d - 2 EXP N) INTER bitset (k - 1)) + CARD {N}))}`SUBST1_TAC THENL[SIMP_TAC[EXTENSION;IN_ELIM_THM] THEN GEN_TAC THEN
REPEAT AP_TERM_TAC THEN SUBGOAL_THEN`CARD (bitset (c - 2 EXP N) INTER bitset (x - 1) UNION {N})
  = CARD (bitset (c - 2 EXP N) INTER bitset (x - 1)) + CARD {N}`SUBST1_TAC
  THENL[MATCH_MP_TAC CARD_UNION THEN SIMP_TAC[FINITE_BITSET;FINITE_INTER;FINITE_SING] THEN
ASSUME_TAC(SPEC`N:num` BITS_OF_NUM_POW2) THEN SIMP_TAC[BITSET_EQ_BITSNUM;GSYM DISJOINT] THEN
SIMP_TAC[DISJOINT_SING] THEN MP_TAC(SPECL[`c - 2 EXP N`;`N:num`] (GSYM BITS_OF_NUM_SUBSET_NUMSEG_EQ)) THEN
UNDISCH_TAC`c < 2 EXP SUC N` THEN UNDISCH_TAC`2 EXP N < c` THEN SIMP_TAC[ARITH_RULE`c - 2 EXP N  < 2 EXP N <=> c < 2 EXP N + 2 EXP N`]
THEN SIMP_TAC[ARITH_RULE`SUC N = 1 + N`;EXP_ADD;EXP_1;MULT_2] THEN
SET_TAC[LT_REFL];ALL_TAC] THEN SUBGOAL_THEN`CARD (bitset (d - 2 EXP N) INTER bitset (x - 1) UNION {N})
  = CARD (bitset (d - 2 EXP N) INTER bitset (x - 1)) + CARD {N}`SUBST1_TAC THENL[MATCH_MP_TAC CARD_UNION THEN
  SIMP_TAC[FINITE_BITSET;FINITE_INTER;FINITE_SING] THEN
ASSUME_TAC(SPEC`N:num` BITS_OF_NUM_POW2) THEN SIMP_TAC[BITSET_EQ_BITSNUM;GSYM DISJOINT] THEN
SIMP_TAC[DISJOINT_SING] THEN MP_TAC(SPECL[`d - 2 EXP N`;`N:num`] (GSYM BITS_OF_NUM_SUBSET_NUMSEG_EQ)) THEN
UNDISCH_TAC`d < 2 EXP SUC N` THEN UNDISCH_TAC`2 EXP N < d` THEN SIMP_TAC[ARITH_RULE`d - 2 EXP N  < 2 EXP N <=> d < 2 EXP N + 2 EXP N`]
THEN SIMP_TAC[ARITH_RULE`SUC N = 1 + N`;EXP_ADD;EXP_1;MULT_2] THEN
SET_TAC[LT_REFL];ALL_TAC] THEN SIMP_TAC[CARD_SING];ALL_TAC] THEN
SIMP_TAC[CARD_SING;ARITH_RULE`a + 1 = SUC a`;ODD_MULT;ODD] THEN RULE_ASSUM_TAC(SIMP_RULE[ODD_MULT]) THEN
MP_TAC(SPECL[`N:num`;`d - 2 EXP N`] BITAND_ODD_CARD) THEN
MP_TAC(SPECL[`N:num`;`c - 2 EXP N`] BITAND_ODD_CARD) THEN
SIMP_TAC[ARITH_RULE`0 < c - a <=> a < c`] THEN
SIMP_TAC[ARITH_RULE`n - 2 EXP N  < 2 EXP N  <=> n < 2 EXP N + 2 EXP N`] THEN
SIMP_TAC[GSYM MULT_2;ARITH_RULE`2 * 2 EXP N = 2 EXP 1 * 2 EXP N `;GSYM EXP_ADD] THEN
ASM_SIMP_TAC[ARITH_RULE`1 + N = SUC N`;ARITH_RULE`1 < N ==> 0 < N`] THEN REPEAT STRIP_TAC THEN
MP_TAC(SPECL[`N:num`;`c - 2 EXP N`] (GSYM BITAND_CARD_ODD_EQ_EVEN)) THEN SIMP_TAC[ARITH_RULE`0 < c - a <=> a < c`] THEN
SIMP_TAC[ARITH_RULE`n - 2 EXP N  < 2 EXP N  <=> n < 2 EXP N + 2 EXP N`] THEN
SIMP_TAC[GSYM MULT_2;ARITH_RULE`2 * 2 EXP N = 2 EXP 1 * 2 EXP N `;GSYM EXP_ADD] THEN
ASM_SIMP_TAC[ARITH_RULE`1 + N = SUC N`;ARITH_RULE`1 < N ==> 0 < N`] THEN STRIP_TAC THEN
FIRST_X_ASSUM(MP_TAC o SPECL[`c - 2 EXP N `;`d - 2 EXP N`]) THEN RULE_ASSUM_TAC(SIMP_RULE[ARITH_RULE`SUC N = 1 + N`;EXP_ADD;EXP_1;MULT_2])
THEN ASM_SIMP_TAC[ARITH_RULE`0 < c - a <=> a < c`;ARITH_RULE`n - 2 EXP N  < 2 EXP N  <=> n < 2 EXP N + 2 EXP N`;ARITH_RULE`2 EXP N < c /\ 2 EXP N < d /\ ~(c = d) ==> ~(c - 2 EXP N = d - 2 EXP N)`;bitand] THEN STRIP_TAC THEN SIMP_TAC[NOT_ODD;GSYM IN_NUMSEG] THEN
ONCE_SIMP_TAC[SET_RULE`{x | x IN s /\ p x /\ q x} = {x | x IN s /\ p x} DIFF {x |x IN s /\ p x /\ ~q x}`] THEN
SIMP_TAC[NOT_EVEN] THEN SIMP_TAC[FINITE_NUMSEG;FINITE_RESTRICT;SET_RULE`{x |x IN s /\ p x /\ q x } SUBSET {x |x IN s /\ p x}`;CARD_DIFF]
THEN ASM_SIMP_TAC[GSYM bitand] THEN ONCE_REWRITE_TAC[TAUT`P /\ Q /\ R <=> P /\ R /\ Q`] THEN
ONCE_SIMP_TAC[SET_RULE`{x | x IN s /\ p x /\ q x} = {x | x IN s /\ p x} DIFF {x |x IN s /\ p x /\ ~q x}`] THEN
SIMP_TAC[NOT_EVEN] THEN SIMP_TAC[FINITE_NUMSEG;FINITE_RESTRICT;SET_RULE`{x |x IN s /\ p x /\ q x } SUBSET {x |x IN s /\ p x}`;CARD_DIFF]
THEN ONCE_REWRITE_TAC[TAUT`P /\ Q /\ R <=> P /\ R /\ Q`] THEN ASM_SIMP_TAC[bitand;IN_NUMSEG] THEN
SUBGOAL_THEN`2 EXP (N - 2) < 2 EXP (N - 1)`ASSUME_TAC THENL[SIMP_TAC[LT_EXP;ARITH] THEN
ASM_SIMP_TAC[ARITH_RULE`1 < N ==> N - 2 < N - 1`];ALL_TAC] THEN ASM_SIMP_TAC[ARITH_RULE`2 EXP (N - 2) < 2 EXP (N - 1) ==>
2 EXP (N - 2) + 2 EXP (N - 1) -(2 EXP (N - 1) - 2 EXP (N - 2)) = 2 EXP (N - 2) + 2 EXP (N - 2)`] THEN
SIMP_TAC[GSYM MULT_2] THEN ASM_SIMP_TAC[ARITH_RULE`1 < N ==> N - 1 = SUC (N - 2)`;EXP]);;

let BITAND_ODD_EVEN_CARD = prove
(`!N c d:num.
  0 < d /\ d < 2 EXP N /\ 0 < c /\ c < 2 EXP N /\ 1 < N /\ ~(c = d) ==> CARD {k | k IN 1..2 EXP N /\
       ODD(CARD (bitand c (k - 1))) /\ EVEN(CARD (bitand d (k - 1)))} = 2 EXP (N - 2)`,
REPEAT STRIP_TAC THEN MP_TAC (SPECL[`N:num`;`c:num`;`d:num`] BITAND_ODD_ODD_CARD) THEN ASM_SIMP_TAC[]
THEN MP_TAC (SPECL[`N:num`;`c:num`] BITAND_ODD_CARD) THEN ASM_SIMP_TAC[ARITH_RULE`1 < N ==> 0 < N`] THEN REPEAT STRIP_TAC THEN
ONCE_REWRITE_TAC[SET_RULE`{x |x IN s /\ p x /\ q x} = {x |x IN s /\ p x} DIFF {x |x IN s /\ p x /\ ~q x}`] THEN
ASM_SIMP_TAC[NOT_EVEN;FINITE_NUMSEG;FINITE_RESTRICT;CARD_DIFF;SET_RULE`{x |x IN s /\ p x /\ q x} SUBSET {x |x IN s /\ p x}`]
THEN SIMP_TAC[ARITH_RULE`a - b = b:num <=> a = b + b`] THEN ASM_SIMP_TAC[ARITH_RULE`1 < N ==> N - 1 = SUC (N - 2)`;EXP;MULT_2] );;

let BITAND_EVEN_EVEN_CARD = prove
(`!N c d:num.
  0 < d /\ d < 2 EXP N /\ 0 < c /\ c < 2 EXP N /\ 1 < N /\ ~(c = d) ==> CARD {k | k IN 1..2 EXP N /\
       EVEN(CARD (bitand c (k - 1))) /\ EVEN(CARD (bitand d (k - 1)))} = 2 EXP (N - 2)`,
REPEAT STRIP_TAC THEN MP_TAC (SPECL[`N:num`;`c:num`;`d:num`] BITAND_ODD_EVEN_CARD) THEN ASM_SIMP_TAC[]
THEN STRIP_TAC THEN ONCE_REWRITE_TAC[SET_RULE`{x |x IN s /\ p x /\ q x} = {x |x IN s /\ q x} DIFF {x |x IN s /\ ~p x /\ q x}`]
THEN ASM_SIMP_TAC[NOT_EVEN;FINITE_NUMSEG;FINITE_RESTRICT;CARD_DIFF;SET_RULE`{x |x IN s /\ p x /\ q x} SUBSET {x |x IN s /\ q x}`]
THEN MP_TAC(SPECL[`N:num`;`d:num`] (GSYM BITAND_CARD_ODD_EQ_EVEN)) THEN ASM_SIMP_TAC[ARITH_RULE`1 < N ==> 0 < N`] THEN
MP_TAC (SPECL[`N:num`;`d:num`] BITAND_ODD_CARD) THEN ASM_SIMP_TAC[ARITH_RULE`1 < N ==> 0 < N`] THEN
SIMP_TAC[ARITH_RULE`a - b = b:num <=> a = b + b`] THEN ASM_SIMP_TAC[ARITH_RULE`1 < N ==> N - 1 = SUC (N - 2)`;EXP;MULT_2]);;

let BITAND_EVEN_ODD_CARD = prove
(`!N c d:num.
  0 < d /\ d < 2 EXP N /\ 0 < c /\ c < 2 EXP N /\ 1 < N /\ ~(c = d) ==> CARD {k | k IN 1..2 EXP N /\
       EVEN(CARD (bitand c (k - 1))) /\ ODD(CARD (bitand d (k - 1)))} = 2 EXP (N - 2)`,
REPEAT STRIP_TAC THEN MP_TAC(SPECL[`N:num`;`d:num`;`c:num`] BITAND_ODD_EVEN_CARD) THEN
ASM_SIMP_TAC[] THEN REWRITE_TAC[TAUT`P /\ Q /\ R <=> P /\ R /\ Q`]);;

let BITAND_CARD_EVEN2_EQ_ODD2 = prove
(`!N c d:num.
  0 < d /\ d < 2 EXP N /\ 0 < c /\ c < 2 EXP N /\ 1 < N /\ ~(c = d) ==> CARD {k | k IN 1..2 EXP N /\
       EVEN(CARD (bitand c (k - 1))) /\ EVEN(CARD (bitand d (k - 1)))} = CARD {k | k IN 1..2 EXP N /\
       ODD(CARD (bitand c (k - 1))) /\ ODD(CARD (bitand d (k - 1)))}`,
REPEAT STRIP_TAC THEN MP_TAC(SPECL[`N:num`;`c:num`;`d:num`] BITAND_EVEN_EVEN_CARD) THEN
MP_TAC(SPECL[`N:num`;`c:num`;`d:num`] BITAND_ODD_ODD_CARD) THEN ASM_SIMP_TAC[]);;

let BITAND_CARD_EVEN_ODD_EQ_ODD2 = prove
(`!N c d:num.
  0 < d /\ d < 2 EXP N /\ 0 < c /\ c < 2 EXP N /\ 1 < N /\ ~(c = d) ==> CARD {k | k IN 1..2 EXP N /\
       EVEN(CARD (bitand c (k - 1))) /\ ODD(CARD (bitand d (k - 1)))} = CARD {k | k IN 1..2 EXP N /\
       ODD(CARD (bitand c (k - 1))) /\ ODD(CARD (bitand d (k - 1)))}`,
REPEAT STRIP_TAC THEN MP_TAC(SPECL[`N:num`;`c:num`;`d:num`] BITAND_EVEN_ODD_CARD) THEN
MP_TAC(SPECL[`N:num`;`c:num`;`d:num`] BITAND_ODD_ODD_CARD) THEN ASM_SIMP_TAC[]);;

let BITAND_CARD_ODD_EVEN_EQ_ODD2 = prove
(`!N c d:num.
  0 < d /\ d < 2 EXP N /\ 0 < c /\ c < 2 EXP N /\ 1 < N /\ ~(c = d) ==> CARD {k | k IN 1..2 EXP N /\
       ODD(CARD (bitand c (k - 1))) /\ EVEN(CARD (bitand d (k - 1)))} = CARD {k | k IN 1..2 EXP N /\
       ODD(CARD (bitand c (k - 1))) /\ ODD(CARD (bitand d (k - 1)))}`,
REPEAT STRIP_TAC THEN MP_TAC(SPECL[`N:num`;`c:num`;`d:num`] BITAND_ODD_EVEN_CARD) THEN
MP_TAC(SPECL[`N:num`;`c:num`;`d:num`] BITAND_ODD_ODD_CARD) THEN ASM_SIMP_TAC[]);;


(* ------------------------------------------------------------------------- *)
(* N_qubit Hadamard gates.                                                   *)
(* ------------------------------------------------------------------------- *)

let hadamard_n = new_definition
  `hadamard_n:complex^(2,N)finite_pow^(2,N)finite_pow = lambda i j.
     if EVEN (CARD(bitand (i-1)(j-1)))
     then Cx(&1 / sqrt(&(dimindex(:(2,N)finite_pow))))
     else --Cx(&1 / sqrt(&(dimindex(:(2,N)finite_pow))))`;;

let NHADAMARD_MAT = prove
 (`!i j.
        1 <= i /\ i <= dimindex(:(2,N)finite_pow) /\
        1 <= j /\ j <= dimindex(:(2,N)finite_pow)
        ==> (hadamard_n:complex^(2,N)finite_pow^(2,N)finite_pow)$i$j = if EVEN (CARD(bitand (i-1)(j-1)))
        then Cx(&1 / sqrt(&(dimindex(:(2,N)finite_pow))))
                   else --Cx(&1 / sqrt(&(dimindex(:(2,N)finite_pow))))`,
  REPEAT GEN_TAC THEN CHOOSE_TAC (SPEC_ALL FINITE_INDEX_INRANGE)
  THEN ASM_SIMP_TAC[hadamard_n;LAMBDA_BETA]);;

let NHADAMARD_HERMITIAN = prove
(` hermitian_matrix hadamard_n = hadamard_n:complex^(2,N)finite_pow^(2,N)finite_pow `,
SIMP_TAC[hermitian_matrix;hadamard_n] THEN
 SIMP_TAC[CART_EQ;LAMBDA_BETA] THEN
SIMP_TAC[COND_CNJ;GSYM CX_NEG;CNJ_CX;BITAND_SYM]);;

let NHADAMARD_UNITARY = prove
(`unitary_matrix (hadamard_n:complex^(2,N)finite_pow^(2,N)finite_pow) `,
SIMP_TAC[unitary_matrix;cmatrix_mul;id_cmatrix] THEN
SIMP_TAC[CART_EQ;LAMBDA_BETA] THEN SIMP_TAC[hermitian_matrix;LAMBDA_BETA;NHADAMARD_MAT]
THEN SIMP_TAC[COND_CNJ;CNJ_NEG;CNJ_CX;COND_LMUL;COND_RMUL] THEN
SIMP_TAC[GSYM CX_MUL;COMPLEX_MUL_RNEG;COMPLEX_MUL_LNEG;COMPLEX_NEG_MUL2]
THEN SIMP_TAC[GSYM REAL_POW_2;DIMINDEX_GE_1;ONE_DIV_SQRTN] THEN
REPEAT STRIP_TAC THENL [ASM_CASES_TAC`i = i':num` THENL [ASM_SIMP_TAC[]
THEN SIMP_TAC[COND_ID;VSUM_CONST_NUMSEG;ARITH_RULE`(a+1)-1 = a`;COMPLEX_CMUL;GSYM CX_MUL]
THEN AP_THM_TAC THEN AP_TERM_TAC THEN SIMP_TAC[DIMINDEX_FINITE_POW;DIMINDEX_2] THEN
SIMP_TAC[REAL_ARITH`a * &1 / a  =a / a`;GSYM REAL_OF_NUM_POW;POW_REFL]
;ALL_TAC] THEN ASM_SIMP_TAC[] THEN SIMP_TAC[FINITE_NUMSEG;VSUM_CASES;NOT_EVEN]
THEN SIMP_TAC[DIMINDEX_FINITE_POW;DIMINDEX_2]
THEN SIMP_TAC[FINITE_NUMSEG;FINITE_RESTRICT;VSUM_CASES;VSUM_CONST] THEN
SIMP_TAC[SET_RULE`{k | k IN {k | k IN s /\ P k} /\ Q k} = {k | k IN s /\  P k /\ Q k}`]
THEN AP_THM_TAC THEN AP_TERM_TAC THEN SIMP_TAC[NOT_EVEN] THEN
SIMP_TAC[COMPLEX_CMUL;GSYM CX_MUL;GSYM CX_ADD;GSYM CX_SUB;GSYM CX_NEG] THEN
AP_TERM_TAC THEN SIMP_TAC[REAL_ARITH`a * b + c * --b = b * (a - c)`] THEN
SIMP_TAC[REAL_ARITH`a * --b + c * b = b * (c - a)`] THEN
SIMP_TAC[REAL_ARITH`a * b + a * c = a * (b + c)`;REAL_ENTIRE] THEN
SUBGOAL_THEN`~(&1 / &(2 EXP dimindex (:N)) = &0)`ASSUME_TAC THENL
[MATCH_MP_TAC REAL_LT_IMP_NZ THEN SIMP_TAC[real_div;REAL_ARITH`&0 < &1 * a <=> &0 < a`]
THEN MATCH_MP_TAC REAL_INV_POS THEN SIMP_TAC[REAL_OF_NUM_LT;SPECL[`dimindex(:N)`;`2`] EXP_LT_0]
THEN ARITH_TAC;ALL_TAC] THEN ASM_SIMP_TAC[] THEN ONCE_REWRITE_TAC[BITAND_SYM] THEN
MP_TAC(SPECL[`dimindex(:N)`;`i' - 1`;`i - 1`]BITAND_CARD_EVEN2_EQ_ODD2) THEN
MP_TAC(SPECL[`dimindex(:N)`;`i' - 1`;`i - 1`]BITAND_CARD_EVEN_ODD_EQ_ODD2)
THEN MP_TAC(SPECL[`dimindex(:N)`;`i' - 1`;`i - 1`]BITAND_CARD_ODD_EVEN_EQ_ODD2) THEN RULE_ASSUM_TAC(SIMP_RULE[DIMINDEX_FINITE_POW;DIMINDEX_2])
THEN ASM_SIMP_TAC[ARITH_RULE`1 <= i /\ i <= n ==> i - 1 < n`] THEN ASM_SIMP_TAC[ ARITH_RULE`1 <= a /\ 1 <= b /\  ~(a = b) ==> ~(a - 1 = b - 1)`]
THEN ASM_CASES_TAC`i = 1` THENL[ASM_SIMP_TAC[ARITH;BITAND_0;EVEN;ODD;SET_RULE`{x |F} = {}`;CARD_CLAUSES] THEN
MP_TAC(SPECL[`dimindex(:N)`;`i'-1`]BITAND_CARD_ODD_EQ_EVEN) THEN MP_TAC(ARITH_RULE`~(i = i') /\ i = 1 ==> ~(i' = 1)`) THEN
ASM_SIMP_TAC[ARITH_RULE`1 <= i /\ ~(i=1) ==> 0 < i - 1`;ARITH_RULE`1 <= i /\ i <= n ==> i - 1 < n`] THEN
SIMP_TAC[DIMINDEX_GE_1;ARITH_RULE`1 <= i  ==> 0 < i `;REAL_ARITH`a - &0 + &0 - a = &0`];ALL_TAC] THEN
ASM_SIMP_TAC[ARITH_RULE`1 <= i /\ ~(i=1) ==> 0 < i - 1`] THEN
ASM_CASES_TAC`i' = 1` THENL[ASM_SIMP_TAC[ARITH;BITAND_0;EVEN;ODD;SET_RULE`{x |F} = {}`;CARD_CLAUSES] THEN
MP_TAC(SPECL[`dimindex(:N)`;`i-1`]BITAND_CARD_ODD_EQ_EVEN) THEN MP_TAC(ARITH_RULE`~(i = i') /\ i' = 1 ==> ~(i = 1)`) THEN
ASM_SIMP_TAC[ARITH_RULE`1 <= i /\ ~(i=1) ==> 0 < i - 1`;ARITH_RULE`1 <= i /\ i <= n ==> i - 1 < n`] THEN
SIMP_TAC[DIMINDEX_GE_1;ARITH_RULE`1 <= i  ==> 0 < i `;REAL_ARITH`a - a + &0 - &0  = &0`];ALL_TAC] THEN
ASM_SIMP_TAC[ARITH_RULE`1 <= i /\ ~(i=1) ==> 0 < i - 1`] THEN ASM_CASES_TAC`dimindex(:N) = 1`
THENL[UNDISCH_TAC`i <= 2 EXP dimindex (:N)` THEN UNDISCH_TAC`i' <= 2 EXP dimindex (:N)` THEN
ASM_SIMP_TAC[EXP_1] THEN
REPEAT STRIP_TAC THEN MP_TAC(ARITH_RULE`1 <= i /\ i <= 2 <=> i = 1 \/ i = 2`) THEN
MP_TAC(ARITH_RULE`1 <= i' /\ i' <= 2 <=> i' = 1 \/ i' = 2`) THEN ASM_SIMP_TAC[] THEN ASM_ARITH_TAC;ALL_TAC]
THEN MP_TAC(ARITH_RULE`1 <= dimindex(:N) /\ ~(dimindex(:N) = 1) <=> 1 < dimindex(:N)`) THEN
ASM_SIMP_TAC[DIMINDEX_GE_1] THEN REPEAT STRIP_TAC THEN SIMP_TAC[REAL_ARITH`a - a + a - a = &0`];ALL_TAC] THEN
ASM_CASES_TAC`i = i':num` THENL[ASM_SIMP_TAC[]
THEN SIMP_TAC[COND_ID;VSUM_CONST_NUMSEG;ARITH_RULE`(a+1)-1 = a`;COMPLEX_CMUL;GSYM CX_MUL]
THEN AP_THM_TAC THEN AP_TERM_TAC THEN SIMP_TAC[DIMINDEX_FINITE_POW;DIMINDEX_2] THEN
SIMP_TAC[REAL_ARITH`a * &1 / a  =a / a`;GSYM REAL_OF_NUM_POW;POW_REFL];ALL_TAC
] THEN ASM_SIMP_TAC[] THEN SIMP_TAC[FINITE_NUMSEG;VSUM_CASES;NOT_EVEN]
THEN SIMP_TAC[DIMINDEX_FINITE_POW;DIMINDEX_2]
THEN SIMP_TAC[FINITE_NUMSEG;FINITE_RESTRICT;VSUM_CASES;VSUM_CONST] THEN
SIMP_TAC[SET_RULE`{k | k IN {k | k IN s /\ P k} /\ Q k} = {k | k IN s /\  P k /\ Q k}`]
THEN AP_THM_TAC THEN AP_TERM_TAC THEN SIMP_TAC[NOT_EVEN] THEN
SIMP_TAC[COMPLEX_CMUL;GSYM CX_MUL;GSYM CX_ADD;GSYM CX_SUB;GSYM CX_NEG] THEN
AP_TERM_TAC THEN SIMP_TAC[REAL_ARITH`a * b + c * --b = b * (a - c)`] THEN
SIMP_TAC[REAL_ARITH`a * --b + c * b = b * (c - a)`] THEN
SIMP_TAC[REAL_ARITH`a * b + a * c = a * (b + c)`;REAL_ENTIRE] THEN
SUBGOAL_THEN`~(&1 / &(2 EXP dimindex (:N)) = &0)`ASSUME_TAC THENL
[MATCH_MP_TAC REAL_LT_IMP_NZ THEN SIMP_TAC[real_div;REAL_ARITH`&0 < &1 * a <=> &0 < a`]
THEN MATCH_MP_TAC REAL_INV_POS THEN SIMP_TAC[REAL_OF_NUM_LT;SPECL[`dimindex(:N)`;`2`] EXP_LT_0]
THEN ARITH_TAC;ALL_TAC] THEN ASM_SIMP_TAC[] THEN
MP_TAC(SPECL[`dimindex(:N)`;`i - 1`;`i' - 1`]BITAND_CARD_EVEN2_EQ_ODD2) THEN
MP_TAC(SPECL[`dimindex(:N)`;`i - 1`;`i' - 1`]BITAND_CARD_EVEN_ODD_EQ_ODD2)
THEN MP_TAC(SPECL[`dimindex(:N)`;`i - 1`;`i' - 1`]BITAND_CARD_ODD_EVEN_EQ_ODD2) THEN RULE_ASSUM_TAC(SIMP_RULE[DIMINDEX_FINITE_POW;DIMINDEX_2])
THEN ASM_SIMP_TAC[ARITH_RULE`1 <= i /\ i <= n ==> i - 1 < n`] THEN ASM_SIMP_TAC[ ARITH_RULE`1 <= a /\ 1 <= b /\  ~(a = b) ==> ~(a - 1 = b - 1)`]
THEN ASM_CASES_TAC`i = 1` THENL[ASM_SIMP_TAC[ARITH;BITAND_0;EVEN;ODD;SET_RULE`{x |F} = {}`;CARD_CLAUSES] THEN
MP_TAC(SPECL[`dimindex(:N)`;`i'-1`]BITAND_CARD_ODD_EQ_EVEN) THEN MP_TAC(ARITH_RULE`~(i = i') /\ i = 1 ==> ~(i' = 1)`)
THEN ASM_SIMP_TAC[ARITH_RULE`1 <= i /\ ~(i=1) ==> 0 < i - 1`;ARITH_RULE`1 <= i /\ i <= n ==> i - 1 < n`]
THEN SIMP_TAC[DIMINDEX_GE_1;ARITH_RULE`1 <= i  ==> 0 < i `;REAL_ARITH`a - a + &0 - &0 = &0`];ALL_TAC] THEN
ASM_SIMP_TAC[ARITH_RULE`1 <= i /\ ~(i=1) ==> 0 < i - 1`] THEN ASM_CASES_TAC`i' = 1` THENL[
ASM_SIMP_TAC[ARITH;BITAND_0;EVEN;ODD;SET_RULE`{x |F} = {}`;CARD_CLAUSES] THEN MP_TAC(SPECL[`dimindex(:N)`;`i-1`]BITAND_CARD_ODD_EQ_EVEN) THEN MP_TAC(ARITH_RULE`~(i = i') /\ i' = 1 ==> ~(i = 1)`) THEN
ASM_SIMP_TAC[ARITH_RULE`1 <= i /\ ~(i=1) ==> 0 < i - 1`;ARITH_RULE`1 <= i /\ i <= n ==> i - 1 < n`] THEN
SIMP_TAC[DIMINDEX_GE_1;ARITH_RULE`1 <= i  ==> 0 < i `;REAL_ARITH`a - &0 + &0 - a = &0`];ALL_TAC] THEN
ASM_SIMP_TAC[ARITH_RULE`1 <= i' /\ ~(i' =1) ==> 0 < i' - 1`] THEN ASM_CASES_TAC`dimindex(:N) = 1` THENL[
UNDISCH_TAC`i <= 2 EXP dimindex (:N)` THEN UNDISCH_TAC`i' <= 2 EXP dimindex (:N)` THEN ASM_SIMP_TAC[EXP_1] THEN
REPEAT STRIP_TAC THEN MP_TAC(ARITH_RULE`1 <= i /\ i <= 2 <=> i = 1 \/ i = 2`) THEN
MP_TAC(ARITH_RULE`1 <= i' /\ i' <= 2 <=> i' = 1 \/ i' = 2`) THEN ASM_SIMP_TAC[] THEN ASM_ARITH_TAC;ALL_TAC]
THEN MP_TAC(ARITH_RULE`1 <= dimindex(:N) /\ ~(dimindex(:N) = 1) <=> 1 < dimindex(:N)`) THEN
ASM_SIMP_TAC[DIMINDEX_GE_1] THEN REPEAT STRIP_TAC THEN SIMP_TAC[REAL_ARITH`a - a + a - a = &0`]);;

(* ------------------------------------------------------------------------- *)
(* `tensor_n2` denotes the n-fold tensor product of 2-dimensional matrices.  *)
(* ------------------------------------------------------------------------- *)

let tensor_n2 = new_definition
`!m:(complex^(2,1)finite_pow^(2,1)finite_pow)list.
  tensor_n2 m =
    lambda i j. cproduct (0..LENGTH m - 1)
      (\k. EL k (REVERSE m) $(((i-1) DIV (2 EXP k)) MOD 2 + 1)
                   $(((j-1) DIV (2 EXP k)) MOD 2 + 1))`;;

(* ------------------------------------------------------------------------- *)
(* `list_of_seq (\k. k) n` produces the integer sequence 0, 1, …, n−1.
`MAP f (list_of_seq (\k. k) n)` then applies the function f to each element of this list, yielding a list of matrices.  *)
(* ------------------------------------------------------------------------- *)

let cmatrix_list = new_definition
`!n:num f:num -> complex^(2,1)finite_pow^(2,1)finite_pow.
  (cmatrix_list f n):(complex^(2,1)finite_pow^(2,1)finite_pow)list = MAP f (list_of_seq (\k. k) n)`;;

(* ------------------------------------------------------------------------- *)
(* The n-fold tensor product of Hadamard gates is realized by a list of n identical Hadamard matrices. *)
(* ------------------------------------------------------------------------- *)

let n_hadamard = new_definition
`n_hadamard:complex^(2,N)finite_pow^(2,N)finite_pow =
 tensor_n2 (cmatrix_list (\k. hadamard) (dimindex(:N)))`;;

let N_HADAMARD_EQHADAMARD_N = prove
(`n_hadamard = hadamard_n:complex^(2,N)finite_pow^(2,N)finite_pow`,
  SIMP_TAC[n_hadamard;hadamard_n;cmatrix_list;tensor_n2] THEN
  SIMP_TAC[CART_EQ;LAMBDA_BETA] THEN REPEAT STRIP_TAC THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN SIMP_TAC[LENGTH_MAP;LENGTH_LIST_OF_SEQ] THEN
  SUBGOAL_THEN`MAP (\k. hadamard) (list_of_seq (\k. k) (dimindex (:N)))
    = REPLICATE (LENGTH (list_of_seq (\k. k) (dimindex (:N)))) hadamard`SUBST1_TAC
    THENL[SPEC_TAC(`list_of_seq (\k. k) (dimindex (:N))`,`l:num list`)
    THEN LIST_INDUCT_TAC THENL[SIMP_TAC[MAP;REPLICATE;LENGTH];ALL_TAC] THEN
    ASM_SIMP_TAC[REPLICATE;LENGTH;MAP];ALL_TAC] THEN
  SIMP_TAC[LENGTH_LIST_OF_SEQ] THEN SIMP_TAC[REVERSE_REPLICATE] THEN
  SUBGOAL_THEN`cproduct (0..dimindex (:N) - 1)
  (\k. EL k (REPLICATE (dimindex (:N)) hadamard)$
      (((i - 1) DIV 2 EXP k) MOD 2 + 1)$
      (((i' - 1) DIV 2 EXP k) MOD 2 + 1)) =
      cproduct (0..dimindex (:N) - 1)
  (\k. hadamard$
      (((i - 1) DIV 2 EXP k) MOD 2 + 1)$
      (((i' - 1) DIV 2 EXP k) MOD 2 + 1))`SUBST1_TAC THENL[MATCH_MP_TAC CPRODUCT_EQ
      THEN SIMP_TAC[IN_NUMSEG] THEN REPEAT STRIP_TAC THEN AP_THM_TAC THEN AP_TERM_TAC
      THEN AP_THM_TAC THEN AP_TERM_TAC THEN MATCH_MP_TAC EL_REPLICATE THEN
      ASM_SIMP_TAC[ARITH_RULE`1 <= b /\ a <= b - 1 ==> a < b`;DIMINDEX_GE_1];ALL_TAC]
      THEN SIMP_TAC[MOD_2_CASES] THEN SIMP_TAC[GSYM NOT_ODD;COND_SWAP] THEN
      SIMP_TAC[COND_RAND] THEN SIMP_TAC[COND_RATOR;ARITH_RULE`1+1=2`;ADD] THEN
      SIMP_TAC[GSYM IN_BITS_OF_NUM] THEN SIMP_TAC[bitand;bitset;BITSET_EQ_BITSNUM] THEN
  SUBGOAL_THEN`(\k. hadamard$
           (if k IN bits_of_num (i - 1) then 2 else 1)$
           (if k IN bits_of_num (i' - 1) then 2 else 1)) =
           (\k.if k IN bits_of_num (i - 1) /\ k IN bits_of_num (i' - 1)
           then  --Cx(&1 / sqrt(&2))
           else Cx(&1 / sqrt(&2)))`SUBST1_TAC THENL[SIMP_TAC[FUN_EQ_THM] THEN GEN_TAC THEN
           COND_CASES_TAC THEN COND_CASES_TAC THEN SIMP_TAC[HADAMARD_EQ;LAMBDA_BETA;
           DIMINDEX_2;ARITH_RULE`1 <= 2 /\ 2 <= 2`;DIMINDEX_FINITE_POW;DIMINDEX_1;EXP_1;
           ARITH;ARITH_RULE`1 <= 1 /\ 1 <= 2`];ALL_TAC] THEN
           SIMP_TAC[GSYM IN_INTER] THEN
  SUBGOAL_THEN`(0..dimindex (:N) - 1) = (bits_of_num (i - 1) INTER bits_of_num (i' - 1)) UNION
  ((0..dimindex (:N) - 1) DIFF (bits_of_num (i - 1) INTER bits_of_num (i' - 1)))`SUBST1_TAC
  THENL[MATCH_MP_TAC UNION_DIFF THEN MATCH_MP_TAC SUBSET_TRANS THEN
  EXISTS_TAC` bits_of_num (i - 1) ` THEN SIMP_TAC[INTER_SUBSET] THEN
  MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC`{k | k < dimindex(:N)}` THEN
  SIMP_TAC[BITS_OF_NUM_SUBSET_NUMSEG_EQ] THEN ASM_SIMP_TAC[GSYM DIMINDEX_FINITE_POW;GSYM DIMINDEX_2;
  SUBSET;IN_ELIM_THM;IN_NUMSEG;ARITH] THEN ASM_ARITH_TAC;ALL_TAC] THEN
  SUBGOAL_THEN`cproduct (bits_of_num (i - 1) INTER bits_of_num (i' - 1) UNION
  (0..dimindex (:N) - 1) DIFF bits_of_num (i - 1) INTER bits_of_num (i' - 1))
      (\k. if k IN bits_of_num (i - 1) INTER bits_of_num (i' - 1)
           then --Cx (&1 / sqrt (&2))
           else Cx (&1 / sqrt (&2))) = cproduct (bits_of_num (i - 1) INTER bits_of_num (i' - 1))
      (\k. if k IN bits_of_num (i - 1) INTER bits_of_num (i' - 1)
           then --Cx (&1 / sqrt (&2))
           else Cx (&1 / sqrt (&2))) * cproduct ((0..dimindex (:N) - 1) DIFF
       bits_of_num (i - 1) INTER bits_of_num (i' - 1))
      (\k. if k IN bits_of_num (i - 1) INTER bits_of_num (i' - 1)
           then --Cx (&1 / sqrt (&2))
           else Cx (&1 / sqrt (&2)))`SUBST1_TAC THENL[MATCH_MP_TAC CPRODUCT_UNION
    THEN SIMP_TAC[FINITE_BITS_OF_NUM;FINITE_INTER;FINITE_DIFF;FINITE_NUMSEG] THEN
    SIMP_TAC[SET_RULE`DISJOINT s (t DIFF s)`];ALL_TAC] THEN
    SIMP_TAC[CPRODUCT_CONST;FINITE_INTER;FINITE_BITS_OF_NUM] THEN SIMP_TAC[DIFF] THEN
    SIMP_TAC[CPRODUCT_CONST;FINITE_INTER;FINITE_BITS_OF_NUM;FINITE_DIFF;GSYM DIFF;FINITE_NUMSEG] THEN
    COND_CASES_TAC THENL[ASM_SIMP_TAC[COMPLEX_POW_NEG;GSYM NOT_ODD] THEN
    SIMP_TAC[COMPLEX_MUL_LNEG;GSYM COMPLEX_POW_ADD] THEN
      SUBGOAL_THEN`CARD (bits_of_num (i - 1) INTER bits_of_num (i' - 1)) +
      CARD((0..dimindex (:N) - 1) DIFF bits_of_num (i - 1) INTER bits_of_num (i' - 1))
      = CARD(0 .. dimindex(:N) - 1)`SUBST1_TAC THENL[MATCH_MP_TAC CARD_UNION_EQ THEN
      SIMP_TAC[FINITE_NUMSEG] THEN MATCH_MP_TAC (SET_RULE`s SUBSET t ==> s INTER (t DIFF s)
      = {} /\ s UNION (t DIFF s) = t`) THEN MATCH_MP_TAC SUBSET_TRANS THEN
      EXISTS_TAC` bits_of_num (i - 1) ` THEN SIMP_TAC[INTER_SUBSET] THEN
    MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC`{k | k < dimindex(:N)}` THEN
    SIMP_TAC[BITS_OF_NUM_SUBSET_NUMSEG_EQ] THEN ASM_SIMP_TAC[GSYM DIMINDEX_FINITE_POW;
    GSYM DIMINDEX_2;SUBSET;IN_ELIM_THM;IN_NUMSEG;ARITH] THEN ASM_ARITH_TAC;ALL_TAC] THEN
  SIMP_TAC[CARD_NUMSEG;DIMINDEX_FINITE_POW;DIMINDEX_2;GSYM REAL_OF_NUM_CLAUSES] THEN
  SIMP_TAC[DIMINDEX_GE_1;ARITH_RULE`1 <= a ==> (a - 1 + 1) - 0 = a`] THEN
  AP_TERM_TAC THEN SIMP_TAC[GSYM CX_POW] THEN AP_TERM_TAC THEN SIMP_TAC[REAL_POW_DIV;
  REAL_POW_ONE] THEN AP_TERM_TAC THEN SIMP_TAC[SQRT_POW];ALL_TAC] THEN
  ASM_SIMP_TAC[GSYM NOT_ODD;COMPLEX_POW_NEG] THEN SIMP_TAC[GSYM COMPLEX_POW_ADD] THEN
  SUBGOAL_THEN`CARD (bits_of_num (i - 1) INTER bits_of_num (i' - 1)) +
      CARD((0..dimindex (:N) - 1) DIFF bits_of_num (i - 1) INTER bits_of_num (i' - 1))
      = CARD(0 .. dimindex(:N) - 1)`SUBST1_TAC THENL[MATCH_MP_TAC CARD_UNION_EQ THEN
      SIMP_TAC[FINITE_NUMSEG] THEN MATCH_MP_TAC (SET_RULE`s SUBSET t ==> s INTER (t DIFF s)
      = {} /\ s UNION (t DIFF s) = t`) THEN MATCH_MP_TAC SUBSET_TRANS THEN
      EXISTS_TAC` bits_of_num (i - 1) ` THEN SIMP_TAC[INTER_SUBSET] THEN
    MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC`{k | k < dimindex(:N)}` THEN
    SIMP_TAC[BITS_OF_NUM_SUBSET_NUMSEG_EQ] THEN ASM_SIMP_TAC[GSYM DIMINDEX_FINITE_POW;
    GSYM DIMINDEX_2;SUBSET;IN_ELIM_THM;IN_NUMSEG;ARITH] THEN ASM_ARITH_TAC;ALL_TAC] THEN
    SIMP_TAC[CARD_NUMSEG;DIMINDEX_FINITE_POW;DIMINDEX_2;GSYM REAL_OF_NUM_CLAUSES] THEN
  SIMP_TAC[DIMINDEX_GE_1;ARITH_RULE`1 <= a ==> (a - 1 + 1) - 0 = a`] THEN
  SIMP_TAC[GSYM CX_POW;REAL_POW_DIV;REAL_POW_ONE] THEN REPEAT AP_TERM_TAC THEN
  SIMP_TAC[SQRT_POW]
);;

(* ------------------------------------------------------------------------- *)
(* BV algorithm.                                                             *)
(* ------------------------------------------------------------------------- *)

let zero_qstate = new_definition
  `zero_qstate :(N)qstate =
   mk_qstate (lambda i. if i = 1 then Cx(&1) else Cx(&0))`;;

let one_qstate = new_definition
  `one_qstate :(N)qstate =
   mk_qstate (lambda i. if i = dimindex(:(2,N)finite_pow) then Cx(&1) else Cx(&0))`;;

let zero_h = new_definition
`zero_h = cmatrix_qstate_mul (hadamard_n:complex^(2,N)finite_pow^(2,N)finite_pow) (zero_qstate :(N)qstate)`;;

let one_h = new_definition
`one_h = cmatrix_qstate_mul hadamard (one_qstate:(1)qstate)`;;

let flip_mat = new_definition
`(flip_mat:num -> complex^(2,N)finite_pow^(2,N)finite_pow) k =
    lambda i j. if (i = k ) /\ (j = k) then --Cx(&1)
                   else if i = j /\ ~(i = k) then Cx(&1)
                   else Cx(&0)`;;

let FLIP_MAT = prove
 (`!n i j.
        1 <= i /\ i <= dimindex(:(2,N)finite_pow) /\
        1 <= j /\ j <= dimindex(:(2,N)finite_pow)
        ==> (flip_mat n:complex^(2,N)finite_pow^(2,N)finite_pow)$i$j = if (i = n ) /\ (j = n) then --Cx(&1)
                   else if i = j /\ ~(i = n) then Cx(&1)
                   else Cx(&0)`,
  REPEAT GEN_TAC THEN CHOOSE_TAC (SPEC_ALL FINITE_INDEX_INRANGE)
  THEN ASM_SIMP_TAC[flip_mat;LAMBDA_BETA]);;

let FLIP_DIAGONAL = prove
(`!k.diagonal_cmatrix (flip_mat k:complex^(2,N)finite_pow^(2,N)finite_pow)`,
SIMP_TAC[diagonal_cmatrix;flip_mat;LAMBDA_BETA] THEN MESON_TAC[]);;

let FLIP_TRANSP = prove
(`!k.ctransp (flip_mat k:complex^(2,N)finite_pow^(2,N)finite_pow) = flip_mat k`,
SIMP_TAC[FLIP_DIAGONAL;CTRANSP_DIAGONAL_CMATRIX]);;

let FLIP_MAT_HERMITIAN = prove
(`!a. flip_mat a = hermitian_matrix (flip_mat a:complex^(2,N)finite_pow^(2,N)finite_pow)`,
GEN_TAC THEN SIMP_TAC[hermitian_matrix;cmatrix_cnj] THEN
SUBGOAL_THEN `?k. 1 <= k /\ k <= dimindex(:(2,N)finite_pow) /\
                    (!A:complex^(2,M)finite_pow^(2,N)finite_pow. A$i = A$k) /\
                      (!z:complex^(2,N)finite_pow. z$i = z$k)`
  CHOOSE_TAC THENL[REWRITE_TAC[FINITE_INDEX_INRANGE2];ALL_TAC] THEN
SUBGOAL_THEN `?l. 1 <= l /\ l <= dimindex(:(2,M)finite_pow) /\
                    (!A:complex^(2,N)finite_pow^(2,M)finite_pow. A$j = A$l) /\
                      (!z:complex^(2,M)finite_pow. z$j = z$l)`
  CHOOSE_TAC THENL[REWRITE_TAC[FINITE_INDEX_INRANGE2];ALL_TAC] THEN
SIMP_TAC[flip_mat] THEN SIMP_TAC[CART_EQ;LAMBDA_BETA] THEN
ONCE_SIMP_TAC[COND_RAND] THEN ONCE_SIMP_TAC[COND_RAND] THEN ONCE_SIMP_TAC[COND_RAND]
THEN SIMP_TAC[GSYM CX_NEG;CNJ_CX] THEN ASM_MESON_TAC[]);;

let FLIP_MAT_UNITARY = prove
(`!k. unitary_matrix (flip_mat k : complex^(2,N)finite_pow^(2,N)finite_pow)`,
SIMP_TAC[unitary_matrix;GSYM FLIP_MAT_HERMITIAN;FLIP_DIAGONAL;CMATRIX_MUL_DIAGONAL]
THEN SIMP_TAC[flip_mat;id_cmatrix] THEN SIMP_TAC[CART_EQ;LAMBDA_BETA]
THEN SIMP_TAC[COND_RMUL;COND_LMUL] THEN
SIMP_TAC[COMPLEX_MUL_RID;COMPLEX_MUL_RZERO;COMPLEX_MUL_RNEG;COMPLEX_NEG_MUL2;COMPLEX_NEG_0]
THEN ASM_MESON_TAC[]);;

let DEST_OF_QSTATE_COMPONENT = prove
 (`!q:complex^(2,N)finite_pow k.
 cnorm2 q = &1
         ==> dest_qstate(mk_qstate q)$k = q$k`,
         SIMP_TAC[GSYM is_qstate;DEST_OF_QSTATE]);;

let IDCMAT_MUL_COMPONENT = prove
(`!i:num q:(N)qstate.
  1 <= i /\ i <= dimindex(:(2,N)finite_pow) ==>
  dest_qstate(id_cmatrix:complex^(2,N)finite_pow^(2,N)finite_pow ** q)$i = dest_qstate q$i`,
REPEAT STRIP_TAC THEN SIMP_TAC[cmatrix_qstate_mul] THEN
ASSUME_TAC (SPEC_ALL IDCMAT_UNITARY) THEN
FIRST_X_ASSUM(ASSUME_TAC o MATCH_MP (SPEC_ALL UNITARITY)) THEN
FIRST_X_ASSUM(ASSUME_TAC o MATCH_MP (SPEC_ALL DEST_OF_QSTATE_COMPONENT))
THEN ASM_SIMP_TAC[CART_EQ;LAMBDA_BETA;IDCMAT] THEN
SIMP_TAC[COND_LMUL;COMPLEX_MUL_LID;COMPLEX_MUL_LZERO] THEN
REPEAT STRIP_TAC THEN GEN_REWRITE_TAC(LAND_CONV o ONCE_DEPTH_CONV)[EQ_SYM_EQ]
THEN ASM_SIMP_TAC[VSUM_DELTA_ALT;IN_NUMSEG]);;

let CMATRIX_QSTATE_MUL_ASSOC = prove
 (`!A B:complex^(2,N)finite_pow^(2,N)finite_pow x:(N)qstate.
    unitary_matrix A /\ unitary_matrix B ==> A ** B ** x = (A ** B) ** x`,
  REPEAT STRIP_TAC THEN FIRST_X_ASSUM(ASSUME_TAC o MATCH_MP (SPEC_ALL UNITARITY)) THEN
  FIRST_X_ASSUM(ASSUME_TAC o MATCH_MP (SPEC_ALL UNITARITY)) THEN RULE_ASSUM_TAC(SIMP_RULE[GSYM is_qstate])
THEN  FIRST_X_ASSUM(ASSUME_TAC o MATCH_MP (SPEC_ALL DEST_OF_QSTATE))
  THEN FIRST_X_ASSUM(ASSUME_TAC o MATCH_MP (SPEC_ALL DEST_OF_QSTATE)) THEN
  SIMP_TAC[cmatrix_mul;cmatrix_qstate_mul] THEN AP_TERM_TAC THEN
  ASM_SIMP_TAC[CART_EQ; LAMBDA_BETA] THEN SIMP_TAC[FINITE_NUMSEG;GSYM VSUM_COMPLEX_LMUL;GSYM VSUM_COMPLEX_RMUL]
  THEN REWRITE_TAC[COMPLEX_MUL_ASSOC] THEN REPEAT STRIP_TAC THEN
 GEN_REWRITE_TAC (RAND_CONV o ONCE_DEPTH_CONV ) [VSUM_SWAP_NUMSEG] THEN REWRITE_TAC[]);;

let FLIP_COMPONENT = prove
(`!a:num q:(N)qstate.
  1 <= a /\ a <= dimindex(:(2,N)finite_pow) ==>
  dest_qstate(flip_mat a:complex^(2,N)finite_pow^(2,N)finite_pow ** q)$a = --(dest_qstate q$a)`,
REPEAT STRIP_TAC THEN SIMP_TAC[cmatrix_qstate_mul] THEN
ASSUME_TAC (SPEC_ALL FLIP_MAT_UNITARY) THEN
FIRST_X_ASSUM(ASSUME_TAC o MATCH_MP (SPEC_ALL UNITARITY)) THEN
FIRST_X_ASSUM(ASSUME_TAC o MATCH_MP (SPEC_ALL DEST_OF_QSTATE_COMPONENT))
THEN ASM_SIMP_TAC[CART_EQ;LAMBDA_BETA;FLIP_MAT] THEN
SIMP_TAC[COND_LMUL;GSYM COMPLEX_NEG_MINUS1;COMPLEX_MUL_LZERO] THEN
SIMP_TAC[VSUM_DELTA_ALT] THEN ASM_SIMP_TAC[IN_NUMSEG]);;

let NHADAMARD_MUL_ZERO_QSTATE = prove
(`hadamard_n ** zero_qstate:(N)qstate = mk_qstate(lambda i. Cx (&1 / sqrt (&(dimindex (:(2,N)finite_pow)))))`,
SIMP_TAC[cmatrix_qstate_mul;zero_qstate] THEN AP_TERM_TAC THEN
SUBGOAL_THEN`dest_qstate
                   (mk_qstate (lambda i. if i = 1 then Cx (&1) else Cx (&0)))
  = (lambda i. if i = 1 then Cx (&1) else Cx (&0)):complex^(2,N)finite_pow`SUBST1_TAC
THENL[MATCH_MP_TAC DEST_OF_QSTATE THEN SIMP_TAC[is_qstate;CNORM2_ALT;cdot;LAMBDA_BETA;COND_CNJ;CNJ_CX]
THEN SIMP_TAC[COND_LMUL;COMPLEX_MUL_LID;COMPLEX_MUL_LZERO] THEN SIMP_TAC[VSUM_DELTA_ALT;IN_NUMSEG;DIMINDEX_GE_1;LE_REFL]
THEN SIMP_TAC[complex_norm;RE_CX;IM_CX;REAL_ARITH`&1 pow 2 = &1`;REAL_ARITH` &0 pow 2 = &0`;REAL_ARITH`&1 + &0 = &1`;SQRT_1]
;ALL_TAC] THEN SIMP_TAC[LAMBDA_BETA;COND_RMUL;COMPLEX_MUL_RID;COMPLEX_MUL_RZERO] THEN
SIMP_TAC[VSUM_DELTA_ALT;IN_NUMSEG;DIMINDEX_GE_1;LE_REFL] THEN SIMP_TAC[CART_EQ;LAMBDA_BETA]
THEN REPEAT STRIP_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
MP_TAC (SPECL[`i:num`;`1`]NHADAMARD_MAT) THEN ASM_SIMP_TAC[LE_REFL;DIMINDEX_GE_1;ARITH;BITAND_0;EVEN]);;


(* ------------------------------------------------------------------------- *)
(* f(x) function                                                             *)
(* ------------------------------------------------------------------------- *)

let fx = new_definition
`(fx:num -> num -> bool) a b = ODD (CARD(bitand a b))`;;

let state_after_ora = new_definition
  `(state_after_ora:num -> (N)qstate) inputs =
     mk_qstate (lambda i.
        if fx (i - 1) inputs
        then dest_qstate (flip_mat i ** zero_h:(N)qstate)$i
        else dest_qstate (id_cmatrix ** zero_h:(N)qstate)$i)`;;

let STATE_AFTER_ORAC = prove
(`!s:num. (state_after_ora s):(N)qstate = mk_qstate (lambda i.
        if fx s (i - 1)
        then --(dest_qstate (zero_h:(N)qstate)$i)
        else dest_qstate (zero_h:(N)qstate)$i)`,
REPEAT STRIP_TAC THEN SIMP_TAC[state_after_ora;IDCMAT_MUL] THEN AP_TERM_TAC THEN
SIMP_TAC[CART_EQ;LAMBDA_BETA;FLIP_COMPONENT] THEN REPEAT STRIP_TAC THEN SIMP_TAC[fx]
THEN GEN_REWRITE_TAC(LAND_CONV o ONCE_DEPTH_CONV)[BITAND_SYM] THEN
AP_THM_TAC THEN REPEAT AP_TERM_TAC THEN ARITH_TAC);;

let second_h = new_definition
`(second_h: num -> (N)qstate) inputs = hadamard_n ** (state_after_ora inputs):(N)qstate`;;

let find_one  = new_definition
`(find_one:(N)qstate -> num) q =
@k. 1 <= k /\ k <= dimindex(:(2,N)finite_pow) /\ dest_qstate q$k = Cx(&1)`;;


(* ---------------------------------------------------------------------------------- *)
(* The hidden decimal string s is calculated as: the index of the '1' element minus 1.*)
(* ---------------------------------------------------------------------------------- *)

let find_s = new_definition
`(find_s:(N)qstate -> num) q =
  (find_one q) - 1`;;


(* ------------------------------------------------------------------------- *)
(* Consistency of Query Result.                                              *)
(* ------------------------------------------------------------------------- *)

let CONSISTENCY = prove
(`!N inputs:num.  0 < inputs /\ inputs < dimindex(:(2,N)finite_pow)
 ==> inputs = find_s((second_h inputs):(N)qstate)`,
REPEAT STRIP_TAC THEN SIMP_TAC[second_h;STATE_AFTER_ORAC;zero_h;NHADAMARD_MUL_ZERO_QSTATE] THEN
SUBGOAL_THEN`dest_qstate(mk_qstate (lambda i. Cx(&1 / sqrt (&(dimindex (:(2,N)finite_pow))))))
= (lambda i. Cx(&1 / sqrt (&(dimindex (:(2,N)finite_pow))))):complex^(2,N)finite_pow`SUBST1_TAC
THENL[MATCH_MP_TAC DEST_OF_QSTATE THEN SIMP_TAC[is_qstate;CNORM2_ALT;cdot;LAMBDA_BETA;COND_CNJ;CNJ_CX]
THEN SIMP_TAC[GSYM CX_MUL;GSYM REAL_POW_2;ONE_DIV_SQRTN;DIMINDEX_GE_1] THEN
SIMP_TAC[VSUM_CONST_NUMSEG;ADD_SUB;COMPLEX_CMUL;GSYM CX_MUL] THEN
SIMP_TAC[REAL_ARITH`a * &1 / a = a / a`;DIMINDEX_FINITE_POW;DIMINDEX_2;GSYM REAL_OF_NUM_POW;POW_REFL]
THEN SIMP_TAC[complex_norm;RE_CX;IM_CX;REAL_ARITH`&1 pow 2 + &0 pow 2 = &1`;SQRT_1];ALL_TAC] THEN
SIMP_TAC[cmatrix_qstate_mul] THEN ABBREV_TAC` c = Cx (&1 / sqrt (&(dimindex (:(2,N)finite_pow))))` THEN
SIMP_TAC[find_s;find_one;fx] THEN
SUBGOAL_THEN`cnorm2 ((lambda i. if ODD (CARD (bitand inputs (i - 1)))
                                 then --((lambda i. c):complex^(2,N)finite_pow$i)
                                 else (lambda i. c):complex^(2,N)finite_pow$i):complex^(2,N)finite_pow) = &1
                                 `ASSUME_TAC THENL[
SIMP_TAC[CNORM2_ALT;cdot;LAMBDA_BETA;COND_CNJ] THEN SIMP_TAC[COND_LMUL] THEN
RULE_ASSUM_TAC(SIMP_RULE[EQ_SYM_EQ]) THEN ASM_SIMP_TAC[CNJ_CX;CNJ_NEG] THEN
SIMP_TAC[COMPLEX_NEG_MUL2;COND_ID;GSYM CX_MUL;GSYM REAL_POW_2;VSUM_CONST_NUMSEG;ADD_SUB;DIMINDEX_GE_1;ONE_DIV_SQRTN]
THEN SIMP_TAC[COMPLEX_CMUL;GSYM CX_MUL;REAL_ARITH`a * &1 / a = a / a`;DIMINDEX_FINITE_POW;DIMINDEX_2;GSYM REAL_OF_NUM_POW;POW_REFL]
THEN SIMP_TAC[complex_norm;RE_CX;IM_CX;REAL_ARITH`&1 pow 2 + &0 pow 2 = &1`;SQRT_1];ALL_TAC] THEN ASM_SIMP_TAC[DEST_OF_QSTATE_COMPONENT]
THEN SIMP_TAC[LAMBDA_BETA] THEN SUBGOAL_THEN`(lambda i. vsum (1..dimindex (:(2,N)finite_pow))
(\j. hadamard_n:complex^(2,N)finite_pow^(2,N)finite_pow$i$j *
                      (if ODD (CARD (bitand inputs (j - 1))) then --c else c))):complex^(2,N)finite_pow =
lambda i. vsum (1..dimindex (:(2,N)finite_pow))
(\j.(if EVEN (CARD (bitand (i - 1) (j - 1)))
              then Cx (&1 / sqrt (&(dimindex (:(2,N)finite_pow))))
              else --Cx (&1 / sqrt (&(dimindex (:(2,N)finite_pow))))) *
              (if ODD (CARD (bitand inputs (j - 1))) then --c else c))`SUBST1_TAC
THENL[SIMP_TAC[CART_EQ;LAMBDA_BETA;NHADAMARD_MAT];ALL_TAC] THEN ASM_SIMP_TAC[] THEN
SIMP_TAC[COND_LMUL;COND_RMUL;COMPLEX_MUL_RNEG;COMPLEX_NEG_MUL2;COMPLEX_MUL_LNEG]
THEN RULE_ASSUM_TAC(SIMP_RULE[EQ_SYM_EQ]) THEN ASM_SIMP_TAC[GSYM CX_MUL;GSYM REAL_POW_2] THEN
SIMP_TAC[DIMINDEX_GE_1;ONE_DIV_SQRTN] THEN SIMP_TAC[DIMINDEX_FINITE_POW;DIMINDEX_2] THEN
ONCE_SIMP_TAC[COND_RAND] THEN SIMP_TAC[COMPLEX_NEG_NEG] THEN
ASM_CASES_TAC`dimindex(:N) <= 1` THENL[POP_ASSUM MP_TAC THEN
SIMP_TAC[ARITH_RULE`a <= 1 <=> a = 1 \/ a = 0`;ARITH_RULE`1 <= a ==> ~(a = 0)`;DIMINDEX_GE_1;EXP_1]
THEN SIMP_TAC[VSUM_2;ARITH;BITAND_0] THEN STRIP_TAC THEN
SUBGOAL_THEN`(lambda i. Cx (&1 / &2) +
                 (if EVEN (CARD (bitand (i - 1) 1))
                  then if ODD (CARD (bitand inputs 1))
                       then --Cx (&1 / &2)
                       else Cx (&1 / &2)
                  else if ODD (CARD (bitand inputs 1))
                       then Cx (&1 / &2)
                       else --Cx (&1 / &2))):complex^(2,N)finite_pow =
(lambda i. if inputs = i - 1 then Cx(&1) else Cx(&0))`SUBST1_TAC THENL[SIMP_TAC[CART_EQ;LAMBDA_BETA] THEN
ASM_SIMP_TAC[DIMINDEX_FINITE_POW;DIMINDEX_2;EXP_1] THEN REPEAT STRIP_TAC THEN AP_THM_TAC THEN AP_TERM_TAC
THEN MP_TAC (ARITH_RULE`1 <= i ==> i <= 2 ==> i = 1 \/ i = 2`) THEN ASM_SIMP_TAC[] THEN STRIP_TAC THENL[
ASM_SIMP_TAC[ARITH;BITAND_0;EVEN] THEN SIMP_TAC[EQ_SYM_EQ] THEN COND_CASES_TAC THENL[ASM_SIMP_TAC[BITAND_0;CARD_CLAUSES;ODD]
THEN SIMPLE_COMPLEX_ARITH_TAC;ALL_TAC] THEN UNDISCH_TAC`inputs < dimindex (:(2,N)finite_pow)`
THEN ASM_SIMP_TAC[DIMINDEX_FINITE_POW;DIMINDEX_2;EXP_1] THEN STRIP_TAC THEN MP_TAC(ARITH_RULE`0 < inputs /\ inputs < 2 <=> inputs = 1`)
THEN ASM_SIMP_TAC[] THEN SIMP_TAC[bitand;BITSET_EQ_BITSNUM;BITS_OF_NUM_1;INTER_IDEMPOT;CARD_SING;ARITH_RULE`ODD 1 <=> T`] THEN STRIP_TAC
THEN SIMPLE_COMPLEX_ARITH_TAC;ALL_TAC] THEN ASM_SIMP_TAC[ARITH;bitand;BITSET_EQ_BITSNUM;BITS_OF_NUM_1;INTER_IDEMPOT;CARD_SING] THEN
SIMP_TAC[ARITH_RULE`EVEN 1 <=> F`] THEN UNDISCH_TAC`inputs < dimindex (:(2,N)finite_pow)` THEN ASM_SIMP_TAC[DIMINDEX_FINITE_POW;DIMINDEX_2;EXP_1]
THEN STRIP_TAC THEN MP_TAC(ARITH_RULE`0 < inputs /\ inputs < 2 <=> inputs = 1`) THEN ASM_SIMP_TAC[] THEN SIMP_TAC[BITS_OF_NUM_1;INTER_IDEMPOT]
THEN SIMP_TAC[CARD_SING;ARITH_RULE`ODD 1 <=> T`] THEN SIMPLE_COMPLEX_ARITH_TAC;ALL_TAC] THEN
SUBGOAL_THEN`dest_qstate
      (mk_qstate (lambda i. if inputs = i - 1 then Cx (&1) else Cx (&0))) =
(lambda i. if inputs = i - 1 then Cx (&1) else Cx (&0)):complex^(2,N)finite_pow`SUBST1_TAC THENL[MATCH_MP_TAC DEST_OF_QSTATE
THEN SIMP_TAC[is_qstate;CNORM2_ALT;cdot;LAMBDA_BETA;COND_CNJ;CNJ_CX] THEN SIMP_TAC[COND_LMUL;COMPLEX_MUL_LID;COMPLEX_MUL_LZERO]
THEN GEN_REWRITE_TAC(LAND_CONV o ONCE_DEPTH_CONV)[EQ_SYM_EQ] THEN UNDISCH_TAC`inputs < dimindex (:(2,N)finite_pow)` THEN ASM_SIMP_TAC[DIMINDEX_FINITE_POW;DIMINDEX_2;EXP_1;VSUM_2] THEN STRIP_TAC THEN MP_TAC(ARITH_RULE`0 < inputs /\ inputs < 2 <=> inputs = 1`)
THEN ASM_SIMP_TAC[ARITH;SIMPLE_COMPLEX_ARITH`Cx(&0) + Cx(&1) = Cx(&1)`;complex_norm;RE_CX;IM_CX;REAL_ARITH`&1 pow 2 + &0 pow 2 = &1`;SQRT_1];ALL_TAC]
THEN UNDISCH_TAC`inputs < dimindex (:(2,N)finite_pow)` THEN ASM_SIMP_TAC[DIMINDEX_FINITE_POW;DIMINDEX_2;EXP_1] THEN
STRIP_TAC THEN MP_TAC(ARITH_RULE`0 < inputs /\ inputs < 2 <=> inputs = 1`) THEN ASM_SIMP_TAC[ARITH] THEN
SIMP_TAC[ARITH_RULE`1 = i - 1 <=> i = 2`] THEN STRIP_TAC THEN MATCH_MP_TAC SELECT_UNIQUE THEN GEN_TAC THEN
SUBGOAL_THEN`(lambda i. if i = 2 then Cx (&1) else Cx (&0)):complex^(2,N)finite_pow
  = cbasis 2`SUBST1_TAC THENL[SIMP_TAC[cbasis;vector_to_cvector;vector_map;CART_EQ;LAMBDA_BETA;basis] THEN
REPEAT STRIP_TAC THEN SIMP_TAC[COND_RAND];ALL_TAC] THEN SIMP_TAC[SPECL[`k:num`;`2`] CBASIS_COMPONENT]
THEN EQ_TAC THENL[STRIP_TAC THEN MP_TAC (SPECL[`y:num`;`2`] CBASIS_COMPONENT) THEN ASM_SIMP_TAC[DIMINDEX_FINITE_POW;DIMINDEX_2;EXP_1]
THEN COND_CASES_TAC THENL[SIMP_TAC[];ALL_TAC] THEN SIMP_TAC[] THEN SIMPLE_COMPLEX_ARITH_TAC;ALL_TAC] THEN
SIMP_TAC[ARITH] THEN STRIP_TAC THEN MP_TAC  (SPECL[`2`;`2`] CBASIS_COMPONENT) THEN
ASM_SIMP_TAC[DIMINDEX_FINITE_POW;DIMINDEX_2;EXP_1] THEN SIMP_TAC[ARITH];ALL_TAC] THEN
RULE_ASSUM_TAC(SIMP_RULE[ARITH_RULE`~(a <= 1) <=> 1 < a`])
THEN SIMP_TAC[FINITE_NUMSEG;FINITE_RESTRICT;VSUM_CASES;VSUM_CONST] THEN
SIMP_TAC[SET_RULE`{k | k IN {k | k IN s /\ P k} /\ Q k} = {k | k IN s /\  P k /\ Q k}`;NOT_ODD;NOT_EVEN]
THEN SUBGOAL_THEN`(lambda i. (&(CARD{j | j IN 1..2 EXP dimindex (:N) /\
EVEN (CARD (bitand (i - 1) (j - 1))) /\ ODD (CARD (bitand inputs (j - 1)))}) %
--Cx (&1 / &(2 EXP dimindex (:N))) + &(CARD{j | j IN 1..2 EXP dimindex (:N) /\
EVEN (CARD (bitand (i - 1) (j - 1))) /\ EVEN (CARD (bitand inputs (j - 1)))}) %
Cx (&1 / &(2 EXP dimindex (:N)))) + &(CARD{j | j IN 1..2 EXP dimindex (:N) /\
ODD (CARD (bitand (i - 1) (j - 1))) /\ ODD (CARD (bitand inputs (j - 1)))}) %
Cx (&1 / &(2 EXP dimindex (:N))) +  &(CARD{j | j IN 1..2 EXP dimindex (:N) /\
ODD (CARD (bitand (i - 1) (j - 1))) /\ EVEN (CARD (bitand inputs (j - 1)))}) %
--Cx (&1 / &(2 EXP dimindex (:N)))):complex^(2,N)finite_pow =
(lambda i. if i - 1 = inputs then Cx(&1) else Cx(&0)):complex^(2,N)finite_pow`SUBST1_TAC THENL[SIMP_TAC[CART_EQ;LAMBDA_BETA] THEN
REPEAT STRIP_TAC THEN COND_CASES_TAC THENL[ASM_SIMP_TAC[GSYM NOT_EVEN] THEN SIMP_TAC[SET_RULE`{k | k IN s /\ p k /\ ~ p k} = {}`;
SET_RULE`{k | k IN s /\ ~ p k /\ p k} = {}`;CARD_CLAUSES;COMPLEX_CMUL;COMPLEX_MUL_LZERO] THEN
SIMP_TAC[GSYM CX_MUL;GSYM CX_ADD] THEN AP_THM_TAC THEN REPEAT AP_TERM_TAC THEN SIMP_TAC[REAL_ARITH`(&0 + a) + b + &0 = a + b`]
THEN SIMP_TAC[REAL_ARITH`a * b + c * b = (a + c) * b`] THEN SIMP_TAC[REAL_OF_NUM_ADD;FINITE_RESTRICT;FINITE_NUMSEG;GSYM CARD_UNION;
SET_RULE`{j |j IN s /\ p j} INTER {j |j IN s /\ ~ p j} = {}`] THEN SIMP_TAC[SET_RULE`{k |k IN s /\ p k} UNION {k |k IN s /\ ~ p k} = {k |k IN s}`]
THEN SIMP_TAC[SET_RULE`{k |k IN 1..m} = (1..m)`;CARD_NUMSEG_1] THEN SIMP_TAC[GSYM REAL_OF_NUM_POW;POW_REFL;REAL_ARITH`a * &1 / a = a / a`];ALL_TAC]
THEN RULE_ASSUM_TAC(SIMP_RULE[DIMINDEX_FINITE_POW;DIMINDEX_2]) THEN MP_TAC (SPECL[`dimindex(:N)`;`i - 1`;`inputs:num`] BITAND_CARD_EVEN2_EQ_ODD2) THEN
MP_TAC (SPECL[`dimindex(:N)`;`i - 1`;`inputs:num`] BITAND_CARD_EVEN_ODD_EQ_ODD2) THEN
MP_TAC (SPECL[`dimindex(:N)`;`i - 1`;`inputs:num`] BITAND_CARD_ODD_EVEN_EQ_ODD2) THEN
ASM_SIMP_TAC[ARITH_RULE`1 <= x ==> x <= 2 EXP N ==> x - 1  < 2 EXP N`] THEN UNDISCH_TAC`1 <= i` THEN
SIMP_TAC[ARITH_RULE`1 <= i <=> i = 1 \/ 1 < i`] THEN STRIP_TAC THENL[ASM_SIMP_TAC[ARITH] THEN SIMP_TAC[BITAND_0;EVEN;ODD;SET_RULE`{j |F} = {}`;
CARD_CLAUSES;COMPLEX_CMUL;COMPLEX_MUL_LZERO] THEN AP_THM_TAC THEN REPEAT AP_TERM_TAC THEN
SIMP_TAC[GSYM CX_ADD;SIMPLE_COMPLEX_ARITH`Cx(&0 + &0) = Cx(&0)`] THEN SIMP_TAC[COMPLEX_MUL_RNEG] THEN
SIMP_TAC[SIMPLE_COMPLEX_ARITH`(-- (a * b) + c * b) + Cx(&0) = Cx(&0) <=> a * b = c * b:complex`] THEN AP_THM_TAC THEN AP_TERM_TAC
THEN AP_TERM_TAC THEN AP_TERM_TAC THEN MP_TAC(SPECL[`dimindex(:N)`;`inputs:num`]BITAND_CARD_ODD_EQ_EVEN) THEN
ASM_SIMP_TAC[ARITH_RULE`1 < a ==> 0 < a`];ALL_TAC] THEN ASM_SIMP_TAC[ARITH_RULE`1 < a ==> 0 < a - 1`] THEN
REPEAT STRIP_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN SIMP_TAC[COMPLEX_CMUL;GSYM COMPLEX_NEG_RMUL;GSYM CX_MUL]
THEN SIMP_TAC[SIMPLE_COMPLEX_ARITH`(--a + a) + a + --a = Cx(&0)`];ALL_TAC] THEN SUBGOAL_THEN`dest_qstate
      (mk_qstate (lambda i. if i - 1 = inputs then Cx (&1) else Cx (&0))) =
(lambda i. if i - 1 = inputs then Cx (&1) else Cx (&0)):complex^(2,N)finite_pow`SUBST1_TAC
THENL[MATCH_MP_TAC DEST_OF_QSTATE
THEN SIMP_TAC[is_qstate;CNORM2_ALT;cdot;LAMBDA_BETA;COND_CNJ;CNJ_CX] THEN SIMP_TAC[COND_LMUL;COMPLEX_MUL_LID;COMPLEX_MUL_LZERO]
THEN SUBGOAL_THEN`vsum (1..dimindex (:(2,N)finite_pow))
 (\i. if i - 1 = inputs then Cx (&1) else Cx (&0)) = vsum (1..dimindex (:(2,N)finite_pow))
 (\i. if i = inputs + 1 then Cx (&1) else Cx (&0))`SUBST1_TAC THENL[MATCH_MP_TAC VSUM_EQ THEN GEN_TAC THEN SIMP_TAC[IN_NUMSEG]
 THEN REPEAT STRIP_TAC THEN MP_TAC (ARITH_RULE`1 <= x ==> x - 1 = inputs ==> x = inputs + 1`) THEN ASM_SIMP_TAC[] THEN
 COND_CASES_TAC THENL[ASM_SIMP_TAC[];ALL_TAC] THEN ASM_SIMP_TAC[] THEN POP_ASSUM MP_TAC THEN
 ONCE_SIMP_TAC[ARITH_RULE`~(a = b) <=> ~(a + 1 = b + 1)`] THEN MP_TAC (ARITH_RULE`1 <= x <=> x - 1 + 1 = x`) THEN
 ASM_SIMP_TAC[];ALL_TAC] THEN SIMP_TAC[VSUM_DELTA_ALT;IN_NUMSEG;ARITH_RULE`1 <= inputs + 1 <=> 0 <= inputs`]
THEN ASM_SIMP_TAC[ARITH_RULE`inputs + 1 <= a  <=> inputs < a`] THEN COND_CASES_TAC THENL[SIMP_TAC[complex_norm;RE_CX;IM_CX;
REAL_ARITH`&1 pow 2 + &0 pow 2 = &1`;SQRT_1];ALL_TAC] THEN POP_ASSUM MP_TAC THEN SIMP_TAC[ARITH_RULE`~(0 <= a) <=> a < 0`]
THEN UNDISCH_TAC`0 < inputs` THEN SIMP_TAC[GSYM IMP_CONJ] THEN SIMP_TAC[ARITH_RULE`0 < a /\ a < 0 <=> F`];ALL_TAC] THEN
SUBGOAL_THEN`(lambda i. if i - 1 = inputs then Cx (&1) else Cx (&0)) =
(lambda i. if i = inputs + 1 then Cx (&1) else Cx (&0)):complex^(2,N)finite_pow`SUBST1_TAC THENL[SIMP_TAC[CART_EQ;LAMBDA_BETA] THEN
REPEAT STRIP_TAC THEN COND_CASES_TAC THENL[MP_TAC (ARITH_RULE`1 <= i /\ i - 1 = inputs <=> i = inputs + 1`) THEN ASM_SIMP_TAC[];ALL_TAC]
THEN POP_ASSUM MP_TAC THEN ONCE_SIMP_TAC[ARITH_RULE`~(a = b) <=> ~(a + 1 = b + 1)`] THEN MP_TAC (ARITH_RULE`1 <= i <=> i - 1 + 1 = i`)
THEN ASM_SIMP_TAC[];ALL_TAC] THEN SUBGOAL_THEN`(lambda i. if i = inputs + 1 then Cx (&1) else Cx (&0)):complex^(2,N)finite_pow
  = cbasis (inputs + 1)`SUBST1_TAC THENL[SIMP_TAC[cbasis;vector_to_cvector;vector_map;CART_EQ;LAMBDA_BETA;basis] THEN
REPEAT STRIP_TAC THEN SIMP_TAC[COND_RAND];ALL_TAC] THEN SIMP_TAC[GSYM DIMINDEX_FINITE_POW;GSYM DIMINDEX_2] THEN
SUBGOAL_THEN`(@k. 1 <= k /\
      k <= dimindex (:(2,N)finite_pow) /\
      (cbasis (inputs + 1)):complex^(2,N)finite_pow$k = Cx (&1)) = inputs + 1`SUBST1_TAC THENL[MATCH_MP_TAC SELECT_UNIQUE
THEN GEN_TAC THEN SIMP_TAC[SPECL[`k:num`;`inputs + 1`] CBASIS_COMPONENT] THEN
EQ_TAC THENL[REPEAT STRIP_TAC THEN POP_ASSUM MP_TAC THEN ASM_SIMP_TAC[SPECL[`y:num`;`inputs + 1`] CBASIS_COMPONENT]
THEN COND_CASES_TAC THENL[SIMP_TAC[];ALL_TAC] THEN SIMP_TAC[SIMPLE_COMPLEX_ARITH`~(Cx(&0) = Cx(&1))`];ALL_TAC]
THEN SIMP_TAC[ARITH_RULE`1 <= inputs + 1 <=> 0 <= inputs`] THEN ASM_SIMP_TAC[ARITH_RULE`inputs + 1 <= a  <=> inputs < a`]
THEN STRIP_TAC THEN STRIP_TAC THENL[ASM_SIMP_TAC[ARITH_RULE`0 <= a <=> a = 0 \/ 0 < a`];ALL_TAC] THEN
MP_TAC(SPECL[`inputs + 1`;`inputs + 1`] CBASIS_COMPONENT) THEN SIMP_TAC[ARITH_RULE`1 <= inputs + 1 <=> 0 <= inputs`]
THEN ASM_SIMP_TAC[ARITH_RULE`inputs + 1 <= a  <=> inputs < a`] THEN ASM_SIMP_TAC[ARITH_RULE`0 <= a <=> a = 0 \/ 0 < a`];ALL_TAC]
THEN ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Definition of Ground State.                                                        *)
(* ------------------------------------------------------------------------- *)

let qbasis = new_definition
  `(qbasis:num -> (N)qstate) k =
     mk_qstate(lambda i. if i = k then Cx(&1) else Cx(&0))`;;

let QBASIS_COMPONENT = prove
 (`!k i. 1 <= k /\ k <= dimindex (:(2,N)finite_pow) /\ 1 <= i /\ i <= dimindex (:(2,N)finite_pow)
         ==> (dest_qstate (qbasis i:(N)qstate)$k = if k = i then Cx(&1) else Cx(&0))`,
  REPEAT STRIP_TAC THEN SIMP_TAC[qbasis] THEN SUBGOAL_THEN`(lambda i'. if i' = i 
  then Cx (&1) else Cx (&0)): complex^(2,N)finite_pow = cbasis (i:num)`SUBST1_TAC THENL[SIMP_TAC[cbasis;vector_to_cvector;vector_map;CART_EQ;LAMBDA_BETA;basis] THEN
  ASM_SIMP_TAC[COND_RAND];ALL_TAC] THEN SUBGOAL_THEN`dest_qstate (mk_qstate (cbasis i))
  = cbasis i:complex^(2,N)finite_pow`SUBST1_TAC THENL[MATCH_MP_TAC DEST_OF_QSTATE THEN 
  SIMP_TAC[is_qstate;CNORM2_VECTOR_TO_CVECTOR;cbasis] THEN 
  ASM_SIMP_TAC[NORM_BASIS;REAL_ARITH`&1 pow 2 = &1`];ALL_TAC] THEN
  ASM_SIMP_TAC[CBASIS_COMPONENT]
 );;

let QBASIS_UNIT = prove
(`!k:num. 1<= k /\ k <= dimindex(:(2,N)finite_pow) ==>
    is_qstate ((lambda i. if i = k then Cx(&1) else Cx(&0)):complex^(2,N)finite_pow)`,
    REPEAT STRIP_TAC THEN SIMP_TAC[is_qstate;CNORM2_ALT;cdot;CART_EQ;LAMBDA_BETA;COND_CNJ;CNJ_CX] THEN
    SIMP_TAC[COND_LMUL;COMPLEX_MUL_LID;COMPLEX_MUL_LZERO;VSUM_DELTA_ALT] THEN 
    ASM_SIMP_TAC[IN_NUMSEG] THEN SIMP_TAC[COMPLEX_NORM_CX; REAL_ARITH`abs (&1) = &1`]
);;

(* ------------------------------------------------------------------------- *)
(* Definition of Outer Product.                                              *)
(* ------------------------------------------------------------------------- *)

let qouter1 = new_definition
  `qouter1 (v:(M)qstate) (w:(N)qstate) :complex^(2,N)finite_pow^(2,M)finite_pow =
     (lambda i j. dest_qstate v$i * cnj (dest_qstate w$j))`;;

(* ------------------------------------------------------------------------- *)
(* Definition of Projection Operator.                                        *)
(* ------------------------------------------------------------------------- *)

let project = new_definition
  `(project:(N)qstate -> complex^(2,N)finite_pow^(2,N)finite_pow) v = qouter1 v v`;;

let PROJECT_HERMITIAN = prove
(`project (v:(N)qstate) = hermitian_matrix (project v)`,
    SIMP_TAC[hermitian_matrix;project] THEN SIMP_TAC[CART_EQ;LAMBDA_BETA] THEN
    REPEAT STRIP_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN SIMP_TAC[qouter1] THEN
    ASM_SIMP_TAC[LAMBDA_BETA] THEN SIMP_TAC[CNJ_MUL;CNJ_CNJ;COMPLEX_MUL_AC]
);;

let PROJECT_IDEMPOTENT = prove
(`!k:num. 1 <= k /\ k <= dimindex (:(2,N)finite_pow) ==>
   (project (tau1 k:(N)qstate)) ** project (tau1 k) = project (tau1 k)`,
  GEN_TAC THEN SIMP_TAC[cmatrix_mul;LAMBDA_BETA;CART_EQ;PROJECT_TAU1_COMPONENT] THEN
  REPEAT STRIP_TAC THEN SIMP_TAC[COND_LMUL;COMPLEX_MUL_LID;COMPLEX_MUL_LZERO] THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN COND_CASES_TAC THENL[
  ASM_SIMP_TAC[] THEN GEN_REWRITE_TAC(LAND_CONV o ONCE_DEPTH_CONV)[EQ_SYM_EQ] THEN
  SIMP_TAC[VSUM_DELTA_ALT] THEN ASM_MESON_TAC[IN_NUMSEG];ALL_TAC] THEN
  GEN_REWRITE_TAC(LAND_CONV o ONCE_DEPTH_CONV)[EQ_SYM_EQ] THEN ASM_SIMP_TAC[] THEN
  RULE_ASSUM_TAC(SIMP_RULE[DE_MORGAN_THM]) THEN POP_ASSUM MP_TAC THEN STRIP_TAC THEN
  ASM_SIMP_TAC[COND_ID;FINITE_NUMSEG;VSUM_CONST;VSUM_CX;SUM_0]
);;

let PROJECT_COMPLETE = prove
(`cmat_sum (1..dimindex(:(2,N)finite_pow)) (\i. project(tau1 i:(N)qstate)) =
  id_cmatrix:complex^(2,N)finite_pow^(2,N)finite_pow`,
  SIMP_TAC[cmat_sum;id_cmatrix;LAMBDA_BETA;CART_EQ] THEN REPEAT STRIP_TAC THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN ASM_SIMP_TAC[PROJECT_TAU1_COMPONENT] THEN
  COND_CASES_TAC THENL[ASM_SIMP_TAC[] THEN GEN_REWRITE_TAC(LAND_CONV o ONCE_DEPTH_CONV)
  [EQ_SYM_EQ] THEN SIMP_TAC[VSUM_DELTA_ALT] THEN ASM_SIMP_TAC[IN_NUMSEG];ALL_TAC] THEN
  GEN_REWRITE_TAC(LAND_CONV o ONCE_DEPTH_CONV)[EQ_SYM_EQ] THEN SIMP_TAC[VSUM_CX;SUM_0]
);;

let PROJECT_QBASIS_COMPONENT = prove
(`!k:num.1 <= k /\ k <= dimindex(:(2,N)finite_pow) /\
         1 <= i /\ i <= dimindex(:(2,N)finite_pow) /\
        1 <= j /\ j <= dimindex(:(2,N)finite_pow)==>
    (project (qbasis k:(N)qstate):complex^(2,N)finite_pow^(2,N)finite_pow)$i$j = 
    if (i = j) /\ (i = k) then Cx(&1) else Cx(&0)`,
    SIMP_TAC[project;qouter1;QBASIS_COMPONENT;LAMBDA_BETA] THEN 
    SIMP_TAC[COND_LMUL;COND_CNJ;CNJ_CX;COND_RMUL] THEN
    SIMP_TAC[COMPLEX_MUL_LID;COMPLEX_MUL_LZERO] THEN REPEAT STRIP_TAC THEN 
    COND_CASES_TAC THENL[ASM_MESON_TAC[];ALL_TAC] THEN 
    ASM_MESON_TAC[]
);;

let apply_cmatrix = new_definition
  `(apply_cmatrix: complex^(2,N)finite_pow^(2,M)finite_pow -> (N)qstate -> complex^(2,M)finite_pow) A q  =
   lambda i. vsum (1..dimindex (:(2,N)finite_pow)) (\j. A$i$j * dest_qstate q$j)`;;

(* ------------------------------------------------------------------------- *)
(* Definition of Measurement.                                                *)
(* ------------------------------------------------------------------------- *)

let measurement_operators = new_definition
`measurement_operators:(complex^(2,N)finite_pow^(2,N)finite_pow) list = 
  MAP (\k. project (qbasis (k + 1):(N)qstate)) (list_of_seq (\k. k) (dimindex(:(2,N)finite_pow)))`;;

let measurement_prob = new_definition
`!y:(N)qstate.
  measurement_prob y = MAP (\k.cnorm2 (apply_cmatrix (EL k (measurement_operators:(complex^(2,N)finite_pow^(2,N)finite_pow) list)) y)) 
                    (list_of_seq (\k. k) (dimindex(:(2,N)finite_pow))) `;;

(* ------------------------------------------------------------------------- *)
(* Measurement after the second H gate in the Bernstein-Vazirani algorithm.  *)
(* ------------------------------------------------------------------------- *)
let BV_MEASURE = prove
(`!inputs:num.
    0 < inputs /\ inputs < dimindex(:(2,N)finite_pow)
        ==> EL inputs (measurement_prob (second_h inputs:(N)qstate)) = &1`,
    REPEAT STRIP_TAC THEN SIMP_TAC[measurement_prob;qbasis;second_h;STATE_AFTER_ORAC;zero_h;
    NHADAMARD_MUL_ZEROQSTATE;measurement_operators] THEN 
    SUBGOAL_THEN`dest_qstate(mk_qstate (lambda i. Cx(&1 / sqrt (&(dimindex (:(2,N)finite_pow))))))
  = (lambda i. Cx(&1 / sqrt (&(dimindex (:(2,N)finite_pow))))):complex^(2,N)finite_pow`SUBST1_TAC
  THENL[MATCH_MP_TAC DEST_OF_QSTATE THEN SIMP_TAC[is_qstate;CNORM2_ALT;cdot;LAMBDA_BETA;COND_CNJ;CNJ_CX]
  THEN SIMP_TAC[GSYM CX_MUL;GSYM REAL_POW_2;ONE_DIV_SQRTN;DIMINDEX_GE_1] THEN
  SIMP_TAC[VSUM_CONST_NUMSEG;ADD_SUB;COMPLEX_CMUL;GSYM CX_MUL] THEN
  SIMP_TAC[REAL_ARITH`a * &1 / a = a / a`;DIMINDEX_FINITE_POW;DIMINDEX_2;GSYM REAL_OF_NUM_POW;POW_REFL]
  THEN SIMP_TAC[complex_norm;RE_CX;IM_CX;REAL_ARITH`&1 pow 2 + &0 pow 2 = &1`;SQRT_1];ALL_TAC] THEN
  SIMP_TAC[cmatrix_qstate_mul;fx] THEN ABBREV_TAC` c = Cx (&1 / sqrt (&(dimindex (:(2,N)finite_pow))))` THEN
  SUBGOAL_THEN`cnorm2 ((lambda i. if ODD (CARD (bitand inputs (i - 1)))
                                 then --((lambda i. c):complex^(2,N)finite_pow$i)
                                 else (lambda i. c):complex^(2,N)finite_pow$i):complex^(2,N)finite_pow) = &1
                                 `ASSUME_TAC THENL[
  SIMP_TAC[CNORM2_ALT;cdot;LAMBDA_BETA;COND_CNJ] THEN SIMP_TAC[COND_LMUL] THEN
  RULE_ASSUM_TAC(SIMP_RULE[EQ_SYM_EQ]) THEN ASM_SIMP_TAC[CNJ_CX;CNJ_NEG] THEN
  SIMP_TAC[COMPLEX_NEG_MUL2;COND_ID;GSYM CX_MUL;GSYM REAL_POW_2;VSUM_CONST_NUMSEG;
  ADD_SUB;DIMINDEX_GE_1;ONE_DIV_SQRTN] THEN SIMP_TAC[COMPLEX_CMUL;GSYM CX_MUL;
  REAL_ARITH`a * &1 / a = a / a`;DIMINDEX_FINITE_POW;DIMINDEX_2;GSYM REAL_OF_NUM_POW;POW_REFL]
  THEN SIMP_TAC[complex_norm;RE_CX;IM_CX;REAL_ARITH`&1 pow 2 + &0 pow 2 = &1`;SQRT_1];ALL_TAC] THEN
  ASM_SIMP_TAC[DEST_OF_QSTATE_COMPONENT] THEN SIMP_TAC[LAMBDA_BETA] THEN
  SUBGOAL_THEN`(lambda i. vsum (1..dimindex (:(2,N)finite_pow))
  (\j. hadamard_n:complex^(2,N)finite_pow^(2,N)finite_pow$i$j *
                      (if ODD (CARD (bitand inputs (j - 1))) then --c else c))):complex^(2,N)finite_pow =
  lambda i. vsum (1..dimindex (:(2,N)finite_pow))
  (\j.(if EVEN (CARD (bitand (i - 1) (j - 1)))
              then Cx (&1 / sqrt (&(dimindex (:(2,N)finite_pow))))
              else --Cx (&1 / sqrt (&(dimindex (:(2,N)finite_pow))))) *
              (if ODD (CARD (bitand inputs (j - 1))) then --c else c))`SUBST1_TAC
  THENL[SIMP_TAC[CART_EQ;LAMBDA_BETA;NHADAMARD_MAT];ALL_TAC] THEN 
  ASM_SIMP_TAC[EL_MAP;LENGTH_LIST_OF_SEQ;EL_LIST_OF_SEQ] THEN 
  ASM_SIMP_TAC[] THEN SIMP_TAC[COND_LMUL;COND_RMUL;COMPLEX_MUL_RNEG;COMPLEX_NEG_MUL2;COMPLEX_MUL_LNEG]
  THEN RULE_ASSUM_TAC(SIMP_RULE[EQ_SYM_EQ]) THEN ASM_SIMP_TAC[GSYM CX_MUL;GSYM REAL_POW_2] THEN
  SIMP_TAC[DIMINDEX_GE_1;ONE_DIV_SQRTN] THEN SIMP_TAC[DIMINDEX_FINITE_POW;DIMINDEX_2] THEN
  ONCE_SIMP_TAC[COND_RAND] THEN SIMP_TAC[COMPLEX_NEG_NEG] THEN
  ASM_CASES_TAC`dimindex(:N) <= 1` THENL[POP_ASSUM MP_TAC THEN
  SIMP_TAC[ARITH_RULE`a <= 1 <=> a = 1 \/ a = 0`;ARITH_RULE`1 <= a ==> ~(a = 0)`;DIMINDEX_GE_1;EXP_1] THEN
  SIMP_TAC[VSUM_2;ARITH;BITAND_0] THEN STRIP_TAC THEN
  SUBGOAL_THEN`(lambda i. Cx (&1 / &2) +
                 (if EVEN (CARD (bitand (i - 1) 1))
                  then if ODD (CARD (bitand inputs 1))
                       then --Cx (&1 / &2)
                       else Cx (&1 / &2)
                  else if ODD (CARD (bitand inputs 1))
                       then Cx (&1 / &2)
                       else --Cx (&1 / &2))):complex^(2,N)finite_pow =
  (lambda i. if inputs = i - 1 then Cx(&1) else Cx(&0))`SUBST1_TAC THENL[SIMP_TAC[CART_EQ;LAMBDA_BETA] THEN
  ASM_SIMP_TAC[DIMINDEX_FINITE_POW;DIMINDEX_2;EXP_1] THEN REPEAT STRIP_TAC THEN AP_THM_TAC THEN AP_TERM_TAC
  THEN MP_TAC (ARITH_RULE`1 <= i ==> i <= 2 ==> i = 1 \/ i = 2`) THEN ASM_SIMP_TAC[] THEN STRIP_TAC THENL[
  ASM_SIMP_TAC[ARITH;BITAND_0;EVEN] THEN SIMP_TAC[EQ_SYM_EQ] THEN COND_CASES_TAC
  THENL[ASM_SIMP_TAC[BITAND_0;CARD_CLAUSES;ODD] THEN SIMPLE_COMPLEX_ARITH_TAC;ALL_TAC]
  THEN UNDISCH_TAC`inputs < dimindex (:(2,N)finite_pow)` THEN
  ASM_SIMP_TAC[DIMINDEX_FINITE_POW;DIMINDEX_2;EXP_1] THEN STRIP_TAC
  THEN MP_TAC(ARITH_RULE`0 < inputs /\ inputs < 2 <=> inputs = 1`)
  THEN ASM_SIMP_TAC[] THEN SIMP_TAC[bitand;BITSET_EQ_BITSNUM;BITS_OF_NUM_1;INTER_IDEMPOT;
  CARD_SING;ARITH_RULE`ODD 1 <=> T`] THEN STRIP_TAC THEN SIMPLE_COMPLEX_ARITH_TAC;ALL_TAC] THEN ASM_SIMP_TAC[ARITH;bitand;BITSET_EQ_BITSNUM;BITS_OF_NUM_1;INTER_IDEMPOT;CARD_SING] THEN
  SIMP_TAC[ARITH_RULE`EVEN 1 <=> F`] THEN UNDISCH_TAC`inputs < dimindex (:(2,N)finite_pow)`
  THEN ASM_SIMP_TAC[DIMINDEX_FINITE_POW;DIMINDEX_2;EXP_1] THEN STRIP_TAC THEN
  MP_TAC(ARITH_RULE`0 < inputs /\ inputs < 2 <=> inputs = 1`) THEN ASM_SIMP_TAC[] THEN
  SIMP_TAC[BITS_OF_NUM_1;INTER_IDEMPOT] THEN SIMP_TAC[CARD_SING;ARITH_RULE`ODD 1 <=> T`] THEN
  SIMPLE_COMPLEX_ARITH_TAC;ALL_TAC] THEN
  SIMP_TAC[apply_cmatrix] THEN ASM_SIMP_TAC[DIMINDEX_FINITE_POW;DIMINDEX_2;EXP_1] THEN SIMP_TAC[GSYM qbasis] THEN
  SUBGOAL_THEN`dest_qstate
      (mk_qstate (lambda i. if inputs = i - 1 then Cx (&1) else Cx (&0))) =
  (lambda i. if inputs = i - 1 then Cx (&1) else Cx (&0)):complex^(2,N)finite_pow`SUBST1_TAC
  THENL[MATCH_MP_TAC DEST_OF_QSTATE THEN SIMP_TAC[is_qstate;CNORM2_ALT;cdot;LAMBDA_BETA;COND_CNJ;CNJ_CX]
  THEN SIMP_TAC[COND_LMUL;COMPLEX_MUL_LID;COMPLEX_MUL_LZERO] THEN
  GEN_REWRITE_TAC(LAND_CONV o ONCE_DEPTH_CONV)[EQ_SYM_EQ] THEN
  UNDISCH_TAC`inputs < dimindex (:(2,N)finite_pow)` THEN
  ASM_SIMP_TAC[DIMINDEX_FINITE_POW;DIMINDEX_2;EXP_1;VSUM_2] THEN STRIP_TAC
  THEN MP_TAC(ARITH_RULE`0 < inputs /\ inputs < 2 <=> inputs = 1`)
  THEN ASM_SIMP_TAC[ARITH;SIMPLE_COMPLEX_ARITH`Cx(&0) + Cx(&1) = Cx(&1)`;complex_norm;
  RE_CX;IM_CX;REAL_ARITH`&1 pow 2 + &0 pow 2 = &1`;SQRT_1];ALL_TAC] THEN
  UNDISCH_TAC`inputs < dimindex (:(2,N)finite_pow)` THEN
  ASM_SIMP_TAC[DIMINDEX_FINITE_POW;DIMINDEX_2;EXP_1] THEN
  STRIP_TAC THEN MP_TAC(ARITH_RULE`0 < inputs /\ inputs < 2 <=> inputs = 1`) THEN
  ASM_SIMP_TAC[ARITH] THEN SIMP_TAC[ARITH_RULE`1 = i - 1 <=> i = 2`] THEN STRIP_TAC THEN
  ASM_SIMP_TAC[VSUM_2;DIMINDEX_FINITE_POW;DIMINDEX_2;EXP_1;CNORM2_ALT;cdot;LAMBDA_BETA;COND_CNJ] THEN
  ASM_SIMP_TAC[LAMBDA_BETA;DIMINDEX_2;PROJECT_QBASIS_COMPONENT;ARITH_RULE`1 <= 2 /\ 2 <= 2`;DIMINDEX_FINITE_POW;
  DIMINDEX_1;EXP_1;ARITH;ARITH_RULE`1 <= 1 /\ 1 <= 2`] THEN SIMP_TAC[COMPLEX_MUL_LZERO;CNJ_CX;COMPLEX_ADD_LID;
  COMPLEX_MUL_LID;COMPLEX_NORM_NUM];ALL_TAC] THEN 
  RULE_ASSUM_TAC(SIMP_RULE[ARITH_RULE`~(a <= 1) <=> 1 < a`]) THEN SIMP_TAC[FINITE_NUMSEG;FINITE_RESTRICT;
  VSUM_CASES;VSUM_CONST] THEN SIMP_TAC[SET_RULE`{k | k IN {k | k IN t /\ P k} /\ Q k} =
  {k | k IN t /\  P k /\ Q k}`;NOT_ODD;NOT_EVEN] THEN
  SUBGOAL_THEN`(lambda i. (&(CARD{j | j IN 1..2 EXP dimindex (:N) /\
  EVEN (CARD (bitand (i - 1) (j - 1))) /\ ODD (CARD (bitand inputs (j - 1)))}) %
  --Cx (&1 / &(2 EXP dimindex (:N))) + &(CARD{j | j IN 1..2 EXP dimindex (:N) /\
  EVEN (CARD (bitand (i - 1) (j - 1))) /\ EVEN (CARD (bitand inputs (j - 1)))}) %
  Cx (&1 / &(2 EXP dimindex (:N)))) + &(CARD{j | j IN 1..2 EXP dimindex (:N) /\
  ODD (CARD (bitand (i - 1) (j - 1))) /\ ODD (CARD (bitand inputs (j - 1)))}) %
  Cx (&1 / &(2 EXP dimindex (:N))) +  &(CARD{j | j IN 1..2 EXP dimindex (:N) /\
  ODD (CARD (bitand (i - 1) (j - 1))) /\ EVEN (CARD (bitand inputs (j - 1)))}) %
  --Cx (&1 / &(2 EXP dimindex (:N)))):complex^(2,N)finite_pow =
  (lambda i. if i - 1 = inputs then Cx(&1) else Cx(&0)):complex^(2,N)finite_pow`SUBST1_TAC
  THENL[SIMP_TAC[CART_EQ;LAMBDA_BETA] THEN REPEAT STRIP_TAC THEN COND_CASES_TAC
  THENL[ASM_SIMP_TAC[GSYM NOT_EVEN] THEN SIMP_TAC[SET_RULE`{k | k IN t /\ p k /\ ~ p k} = {}`;
  SET_RULE`{k | k IN t /\ ~ p k /\ p k} = {}`;CARD_CLAUSES;COMPLEX_CMUL;COMPLEX_MUL_LZERO] THEN
  SIMP_TAC[GSYM CX_MUL;GSYM CX_ADD] THEN AP_THM_TAC THEN REPEAT AP_TERM_TAC THEN
  SIMP_TAC[REAL_ARITH`(&0 + a) + b + &0 = a + b`] THEN SIMP_TAC[REAL_ARITH`a * b + c * b = (a + c) * b:real`]
  THEN SIMP_TAC[REAL_OF_NUM_ADD;FINITE_RESTRICT;FINITE_NUMSEG;GSYM CARD_UNION;
  SET_RULE`{j |j IN t /\ p j} INTER {j |j IN t /\ ~ p j} = {}`] THEN
  SIMP_TAC[SET_RULE`{k |k IN t /\ p k} UNION {k |k IN t /\ ~ p k} = {k |k IN t}`]
  THEN SIMP_TAC[SET_RULE`{k |k IN 1..m} = (1..m)`;CARD_NUMSEG_1] THEN
  SIMP_TAC[GSYM REAL_OF_NUM_POW;POW_REFL;REAL_ARITH`a * &1 / a = a / a`];ALL_TAC]
  THEN RULE_ASSUM_TAC(SIMP_RULE[DIMINDEX_FINITE_POW;DIMINDEX_2]) THEN
  MP_TAC (SPECL[`dimindex(:N)`;`i - 1`;`inputs:num`] BITAND_CARD_EVEN2_EQ_ODD2) THEN
  MP_TAC (SPECL[`dimindex(:N)`;`i - 1`;`inputs:num`] BITAND_CARD_EVEN_ODD_EQ_ODD2) THEN
  MP_TAC (SPECL[`dimindex(:N)`;`i - 1`;`inputs:num`] BITAND_CARD_ODD_EVEN_EQ_ODD2) THEN
  ASM_SIMP_TAC[ARITH_RULE`1 <= x ==> x <= 2 EXP N ==> x - 1  < 2 EXP N`] THEN
  UNDISCH_TAC`1 <= i` THEN SIMP_TAC[ARITH_RULE`1 <= i <=> i = 1 \/ 1 < i`] THEN
  STRIP_TAC THENL[ASM_SIMP_TAC[ARITH] THEN SIMP_TAC[BITAND_0;EVEN;ODD;SET_RULE`{j |F} = {}`;
  CARD_CLAUSES;COMPLEX_CMUL;COMPLEX_MUL_LZERO] THEN AP_THM_TAC THEN REPEAT AP_TERM_TAC THEN
  SIMP_TAC[GSYM CX_ADD;SIMPLE_COMPLEX_ARITH`Cx(&0 + &0) = Cx(&0)`] THEN
  SIMP_TAC[COMPLEX_MUL_RNEG] THEN SIMP_TAC[SIMPLE_COMPLEX_ARITH`(-- (a * b) + c * b) + Cx(&0) =
  Cx(&0) <=> a * b = c * b:complex`] THEN AP_THM_TAC THEN AP_TERM_TAC
  THEN AP_TERM_TAC THEN AP_TERM_TAC THEN MP_TAC(SPECL[`dimindex(:N)`;`inputs:num`]BITAND_CARD_ODD_EQ_EVEN) THEN
  ASM_SIMP_TAC[ARITH_RULE`1 < a ==> 0 < a`];ALL_TAC] THEN ASM_SIMP_TAC[ARITH_RULE`1 < a ==> 0 < a - 1`] THEN
  REPEAT STRIP_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN SIMP_TAC[COMPLEX_CMUL;GSYM COMPLEX_NEG_RMUL;GSYM CX_MUL]
  THEN SIMP_TAC[SIMPLE_COMPLEX_ARITH`(--a + a) + a + --a = Cx(&0)`];ALL_TAC] THEN
  SIMP_TAC[apply_cmatrix] THEN
  SUBGOAL_THEN`dest_qstate
      (mk_qstate (lambda i. if i - 1 = inputs then Cx (&1) else Cx (&0))) =
  (lambda i. if i - 1 = inputs then Cx (&1) else Cx (&0)):complex^(2,N)finite_pow`SUBST1_TAC
  THENL[MATCH_MP_TAC DEST_OF_QSTATE
  THEN SIMP_TAC[is_qstate;CNORM2_ALT;cdot;LAMBDA_BETA;COND_CNJ;CNJ_CX] THEN
  SIMP_TAC[COND_LMUL;COMPLEX_MUL_LID;COMPLEX_MUL_LZERO]
  THEN SUBGOAL_THEN`vsum (1..dimindex (:(2,N)finite_pow))
  (\i. if i - 1 = inputs then Cx (&1) else Cx (&0)) = vsum (1..dimindex (:(2,N)finite_pow))
  (\i. if i = inputs + 1 then Cx (&1) else Cx (&0))`SUBST1_TAC THENL[MATCH_MP_TAC VSUM_EQ
  THEN GEN_TAC THEN SIMP_TAC[IN_NUMSEG] THEN REPEAT STRIP_TAC THEN
  MP_TAC (ARITH_RULE`1 <= x ==> x - 1 = inputs ==> x = inputs + 1`) THEN ASM_SIMP_TAC[] THEN
  COND_CASES_TAC THENL[ASM_SIMP_TAC[];ALL_TAC] THEN ASM_SIMP_TAC[] THEN POP_ASSUM MP_TAC THEN
  ONCE_SIMP_TAC[ARITH_RULE`~(a = b) <=> ~(a + 1 = b + 1)`] THEN MP_TAC (ARITH_RULE`1 <= x <=> x - 1 + 1 = x`) THEN
  ASM_SIMP_TAC[];ALL_TAC] THEN SIMP_TAC[VSUM_DELTA_ALT;IN_NUMSEG;ARITH_RULE`1 <= inputs + 1 <=> 0 <= inputs`]
  THEN ASM_SIMP_TAC[ARITH_RULE`inputs + 1 <= a  <=> inputs < a`] THEN COND_CASES_TAC
  THENL[SIMP_TAC[complex_norm;RE_CX;IM_CX;REAL_ARITH`&1 pow 2 + &0 pow 2 = &1`;SQRT_1];ALL_TAC]
  THEN POP_ASSUM MP_TAC THEN SIMP_TAC[ARITH_RULE`~(0 <= a) <=> a < 0`] THEN
  UNDISCH_TAC`0 < inputs` THEN SIMP_TAC[GSYM IMP_CONJ] THEN SIMP_TAC[ARITH_RULE`0 < a /\ a < 0 <=> F`];ALL_TAC] THEN
  SUBGOAL_THEN`(lambda i. if i - 1 = inputs then Cx (&1) else Cx (&0)) =
  (lambda i. if i = inputs + 1 then Cx (&1) else Cx (&0)):complex^(2,N)finite_pow`SUBST1_TAC
  THENL[SIMP_TAC[CART_EQ;LAMBDA_BETA] THEN REPEAT STRIP_TAC THEN COND_CASES_TAC
  THENL[MP_TAC (ARITH_RULE`1 <= i /\ i - 1 = inputs <=> i = inputs + 1`) THEN
  ASM_SIMP_TAC[];ALL_TAC] THEN POP_ASSUM MP_TAC THEN
  ONCE_SIMP_TAC[ARITH_RULE`~(a = b) <=> ~(a + 1 = b + 1)`] THEN
  MP_TAC (ARITH_RULE`1 <= i <=> i - 1 + 1 = i`) THEN ASM_SIMP_TAC[];ALL_TAC] THEN
  SIMP_TAC[project;qouter1;QBASIS_COMPONENT;LAMBDA_BETA] THEN
  SUBGOAL_THEN`dest_qstate
      (mk_qstate (lambda i. if i = inputs + 1 then Cx (&1) else Cx (&0))) =
  (lambda i. if i = inputs + 1 then Cx (&1) else Cx (&0)):complex^(2,N)finite_pow`SUBST1_TAC THENL[
  MATCH_MP_TAC DEST_OF_QSTATE THEN MATCH_MP_TAC (SPEC`inputs + 1`QBASIS_UNIT)THEN ASM_ARITH_TAC;ALL_TAC] THEN
  ASM_SIMP_TAC[CNORM2_ALT;cdot;LAMBDA_BETA;COND_CNJ;CNJ_CX] THEN SIMP_TAC[COND_RAND] THEN
  SIMP_TAC[COND_RATOR] THEN SIMP_TAC[COMPLEX_MUL_LID;COMPLEX_MUL_LZERO;COMPLEX_MUL_RID;COMPLEX_MUL_RZERO] THEN
  SIMP_TAC[VSUM_DELTA_ALT;IN_NUMSEG] THEN ASM_SIMP_TAC[ARITH_RULE`a < b ==> a + 1 <= b`] THEN
  ASM_SIMP_TAC[ARITH_RULE`1 <= a + 1 <=> 0 <= a`] THEN ASM_SIMP_TAC[ARITH_RULE`0 < a ==> 0 <= a`] THEN
  SIMP_TAC[COND_CNJ;CNJ_CX;VSUM_DELTA_ALT;COND_LMUL;COMPLEX_MUL_LID;COMPLEX_MUL_LZERO] THEN
  ASM_SIMP_TAC[IN_NUMSEG;ARITH_RULE`a < b ==> a + 1 <= b`] THEN
  ASM_SIMP_TAC[ARITH_RULE`1 <= a + 1 <=> 0 <= a`] THEN ASM_SIMP_TAC[ARITH_RULE`0 < a ==> 0 <= a`] THEN
  SIMP_TAC[COMPLEX_NORM_NUM]
);;
  
(* ------------------------------------------------------------------------- *)
(* Definition of XOR.                                                        *)
(* ------------------------------------------------------------------------- *)

let xor = new_definition
`!a b:num. xor a b = bitset a DIFF bitset b UNION bitset b DIFF bitset a`;;

let DECRYPTION = prove
(`!a b:num. xor (binarysum(xor a b)) b = bitset a `,
REPEAT GEN_TAC THEN SIMP_TAC[xor] THEN
SIMP_TAC[FINITE_DIFF;FINITE_BITSET;FINITE_UNION;BITSET_BINARYSUM] THEN
SIMP_TAC[SET_RULE`(A DIFF B UNION B DIFF A) DIFF B = (A DIFF B) DIFF B UNION
  (B DIFF A) DIFF B`] THEN SIMP_TAC[DIFF_DIFF;SET_RULE`A DIFF B DIFF A = {}`;UNION_EMPTY]
THEN SIMP_TAC[SET_RULE`B DIFF (A DIFF B UNION B DIFF A) = A INTER B`] THEN SET_TAC[]);;


(* ------------------------------------------------------------------------- *)
(* Quantum Error Correction.                                                 *)
(* ------------------------------------------------------------------------- *)

let gamma = new_definition
`gamma = 4`;;

let eta = new_definition
`eta = 5`;;

let CORRECTION = prove
(`xor eta (find_s((second_h gamma):(3)qstate)) = {0}`,
SIMP_TAC[gamma;eta] THEN SUBGOAL_THEN`4 = find_s((second_h 4):(3)qstate)`MP_TAC
THENL[MATCH_MP_TAC CONSISTENCY THEN SIMP_TAC[ARITH_RULE`0 < 4`;DIMINDEX_FINITE_POW;DIMINDEX_3;ARITH;DIMINDEX_2];ALL_TAC]
THEN GEN_REWRITE_TAC(LAND_CONV o ONCE_DEPTH_CONV)[EQ_SYM_EQ] THEN SIMP_TAC[xor] THEN
SUBGOAL_THEN`bitset 5 = {0,2}`SUBST1_TAC THENL[SIMP_TAC[IN_ELIM_THM;EXTENSION;bitset] THEN GEN_TAC THEN
SIMP_TAC[GSYM IN_BITS_OF_NUM] THEN AP_TERM_TAC THEN SIMP_TAC[BITS_OF_NUM_GALOIS] THEN
SIMP_TAC[SET_RULE`{0,2} = {0} UNION {2}`;FINITE_SING;FINITE_UNION] THEN SUBGOAL_THEN`DISJOINT {0} {2}`ASSUME_TAC
THENL[SIMP_TAC[DISJOINT_SING;IN_SING;ARITH];ALL_TAC] THEN ASM_SIMP_TAC[NSUM_UNION;FINITE_SING;NSUM_SING;EXP;ARITH];ALL_TAC]
THEN SIMP_TAC[BITSET_EQ_BITSNUM;ARITH_RULE`4 = 2 EXP 2`;BITS_OF_NUM_POW2] THEN SUBGOAL_THEN`{0, 2} DIFF {2} = {0}`SUBST1_TAC
THENL[SIMP_TAC[DIFF;IN_ELIM_THM;EXTENSION;IN_SING] THEN GEN_TAC THEN EQ_TAC THENL[SIMP_TAC[SET_RULE`x IN {0,2} /\ ~(x = 2) ==> x = 0`];ALL_TAC]
THEN SIMP_TAC[SET_RULE`0 IN {0,2}`;ARITH];ALL_TAC] THEN SUBGOAL_THEN`{2} DIFF {0,2} = {}`SUBST1_TAC THENL[
SIMP_TAC[DIFF;IN_ELIM_THM;EXTENSION;IN_SING] THEN GEN_TAC THEN SIMP_TAC[SET_RULE`~(x IN {0,2}) <=> ~(x = 0) /\ ~(x = 2)`]
THEN SIMP_TAC[SET_RULE`x = 2 /\ ~(x = 0) /\ ~(x = 2) <=> x IN {}`] ;ALL_TAC] THEN SIMP_TAC[UNION_EMPTY]);;


(* ------------------------------------------------------------------------- *)
(* Define the values of the 4 pixels in a 2*2 image.                         *)
(* ------------------------------------------------------------------------- *)

let pixel_1 = new_definition
`pixel_1 = 31`;;

let pixel_2 = new_definition
`pixel_2 = 57`;;

let pixel_3 = new_definition
`pixel_3 = 101`;;

let pixel_4 = new_definition
`pixel_4 = 12`;;


(* ------------------------------------------------------------------------- *)
(* Definition of the Key s .                                                 *)
(* ------------------------------------------------------------------------- *)

let s = new_definition
`s = 23`;;


(* ------------------------------------------------------------------------- *)
(* Image Encryption and Decryption.                                          *)
(* ------------------------------------------------------------------------- *)

let encryption_1 = new_definition
`encryption_1 = xor pixel_1 s`;;

let encryption_2 = new_definition
`encryption_2 = xor pixel_2 s`;;

let encryption_3 = new_definition
`encryption_3 = xor pixel_3 s`;;

let encryption_4 = new_definition
`encryption_4 = xor pixel_4 s`;;

let decryption_1 = new_definition
`decryption_1 = xor (binarysum(encryption_1)) s`;;

let decryption_2 = new_definition
`decryption_2 = xor (binarysum(encryption_2)) s`;;

let decryption_3 = new_definition
`decryption_3 = xor (binarysum(encryption_3)) s`;;

let decryption_4 = new_definition
`decryption_4 = xor (binarysum(encryption_4)) s`;;


(* ------------------------------------------------------------------------- *)
(* Prove that the decrypted image is restored to the original image.         *)
(* ------------------------------------------------------------------------- *)

let DECRYPTION_1 = prove
(`binarysum(decryption_1) = pixel_1`,
SIMP_TAC[decryption_1;encryption_1;DECRYPTION;BINARYSUM_BITSET]);;

let DECRYPTION_2 = prove
(`binarysum(decryption_2) = pixel_2`,
SIMP_TAC[decryption_2;encryption_2;DECRYPTION;BINARYSUM_BITSET]);;

let DECRYPTION_3 = prove
(`binarysum(decryption_3) = pixel_3`,
SIMP_TAC[decryption_3;encryption_3;DECRYPTION;BINARYSUM_BITSET]);;

let DECRYPTION_4 = prove
(`binarysum(decryption_4) = pixel_4`,
SIMP_TAC[decryption_4;encryption_4;DECRYPTION;BINARYSUM_BITSET]);;

