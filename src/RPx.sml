(* Test that words can handle numbers between 0 and 31 *)
val _ = if 5 <= Word.wordSize then () else raise (Fail ("wordSize less than 5"));

structure Uint32 : sig
  val set_bit : Word32.word -> IntInf.int -> bool -> Word32.word
  val shiftl : Word32.word -> IntInf.int -> Word32.word
  val shiftr : Word32.word -> IntInf.int -> Word32.word
  val shiftr_signed : Word32.word -> IntInf.int -> Word32.word
  val test_bit : Word32.word -> IntInf.int -> bool
end = struct

fun set_bit x n b =
  let val mask = Word32.<< (0wx1, Word.fromLargeInt (IntInf.toLarge n))
  in if b then Word32.orb (x, mask)
     else Word32.andb (x, Word32.notb mask)
  end

fun shiftl x n =
  Word32.<< (x, Word.fromLargeInt (IntInf.toLarge n))

fun shiftr x n =
  Word32.>> (x, Word.fromLargeInt (IntInf.toLarge n))

fun shiftr_signed x n =
  Word32.~>> (x, Word.fromLargeInt (IntInf.toLarge n))

fun test_bit x n =
  Word32.andb (x, Word32.<< (0wx1, Word.fromLargeInt (IntInf.toLarge n))) <> Word32.fromInt 0

end; (* struct Uint32 *)

structure Bits_Integer : sig
  val set_bit : IntInf.int -> IntInf.int -> bool -> IntInf.int
  val shiftl : IntInf.int -> IntInf.int -> IntInf.int
  val shiftr : IntInf.int -> IntInf.int -> IntInf.int
  val test_bit : IntInf.int -> IntInf.int -> bool
end = struct

val maxWord = IntInf.pow (2, Word.wordSize);

fun set_bit x n b =
  if n < maxWord then
    if b then IntInf.orb (x, IntInf.<< (1, Word.fromLargeInt (IntInf.toLarge n)))
    else IntInf.andb (x, IntInf.notb (IntInf.<< (1, Word.fromLargeInt (IntInf.toLarge n))))
  else raise (Fail ("Bit index too large: " ^ IntInf.toString n));

fun shiftl x n =
  if n < maxWord then IntInf.<< (x, Word.fromLargeInt (IntInf.toLarge n))
  else raise (Fail ("Shift operand too large: " ^ IntInf.toString n));

fun shiftr x n =
  if n < maxWord then IntInf.~>> (x, Word.fromLargeInt (IntInf.toLarge n))
  else raise (Fail ("Shift operand too large: " ^ IntInf.toString n));

fun test_bit x n =
  if n < maxWord then IntInf.andb (x, IntInf.<< (1, Word.fromLargeInt (IntInf.toLarge n))) <> 0
  else raise (Fail ("Bit index too large: " ^ IntInf.toString n));

end; (*struct Bits_Integer*)

structure RPx : sig
  type nat
  val zero_nata : nat
  val suc : nat -> nat
  datatype ('a, 'b) term = Var of 'b | Fun of 'a * ('a, 'b) term list
  datatype 'a literal = Pos of 'a | Neg of 'a
  type char
  val prover : ((nat, nat) term literal list * nat) list -> bool
  val string_literal_of_nat : nat -> string
end = struct

datatype nat = Nat of IntInf.int;

fun integer_of_nat (Nat x) = x;

fun equal_nata m n = (((integer_of_nat m) : IntInf.int) = (integer_of_nat n));

type 'a equal = {equal : 'a -> 'a -> bool};
val equal = #equal : 'a equal -> 'a -> 'a -> bool;

val equal_nat = {equal = equal_nata} : nat equal;

fun plus_nata m n = Nat (IntInf.+ (integer_of_nat m, integer_of_nat n));

type 'a plus = {plus : 'a -> 'a -> 'a};
val plus = #plus : 'a plus -> 'a -> 'a -> 'a;

val plus_nat = {plus = plus_nata} : nat plus;

val zero_nata : nat = Nat (0 : IntInf.int);

type 'a zero = {zero : 'a};
val zero = #zero : 'a zero -> 'a;

val zero_nat = {zero = zero_nata} : nat zero;

fun less_eq_nat m n = IntInf.<= (integer_of_nat m, integer_of_nat n);

type 'a ord = {less_eq : 'a -> 'a -> bool, less : 'a -> 'a -> bool};
val less_eq = #less_eq : 'a ord -> 'a -> 'a -> bool;
val less = #less : 'a ord -> 'a -> 'a -> bool;

fun less_nat m n = IntInf.< (integer_of_nat m, integer_of_nat n);

val ord_nat = {less_eq = less_eq_nat, less = less_nat} : nat ord;

datatype ordera = Eq | Lt | Gt;

fun eq A_ a b = equal A_ a b;

type 'a preorder = {ord_preorder : 'a ord};
val ord_preorder = #ord_preorder : 'a preorder -> 'a ord;

type 'a order = {preorder_order : 'a preorder};
val preorder_order = #preorder_order : 'a order -> 'a preorder;

type 'a linorder = {order_linorder : 'a order};
val order_linorder = #order_linorder : 'a linorder -> 'a order;

fun comparator_of (A1_, A2_) x y =
  (if less ((ord_preorder o preorder_order o order_linorder) A2_) x y then Lt
    else (if eq A1_ x y then Eq else Gt));

val preorder_nat = {ord_preorder = ord_nat} : nat preorder;

val order_nat = {preorder_order = preorder_nat} : nat order;

val linorder_nat = {order_linorder = order_nat} : nat linorder;

fun compare_nata x = comparator_of (equal_nat, linorder_nat) x;

type 'a compare = {compare : 'a -> 'a -> ordera};
val compare = #compare : 'a compare -> 'a -> 'a -> ordera;

val compare_nat = {compare = compare_nata} : nat compare;

type 'a semigroup_add = {plus_semigroup_add : 'a plus};
val plus_semigroup_add = #plus_semigroup_add : 'a semigroup_add -> 'a plus;

type 'a monoid_add =
  {semigroup_add_monoid_add : 'a semigroup_add, zero_monoid_add : 'a zero};
val semigroup_add_monoid_add = #semigroup_add_monoid_add :
  'a monoid_add -> 'a semigroup_add;
val zero_monoid_add = #zero_monoid_add : 'a monoid_add -> 'a zero;

val semigroup_add_nat = {plus_semigroup_add = plus_nat} : nat semigroup_add;

val monoid_add_nat =
  {semigroup_add_monoid_add = semigroup_add_nat, zero_monoid_add = zero_nat} :
  nat monoid_add;

type 'a compare_order =
  {compare_compare_order : 'a compare, linorder_compare_order : 'a linorder};
val compare_compare_order = #compare_compare_order :
  'a compare_order -> 'a compare;
val linorder_compare_order = #linorder_compare_order :
  'a compare_order -> 'a linorder;

val compare_order_nat =
  {compare_compare_order = compare_nat, linorder_compare_order = linorder_nat} :
  nat compare_order;

type 'a ab_semigroup_add = {semigroup_add_ab_semigroup_add : 'a semigroup_add};
val semigroup_add_ab_semigroup_add = #semigroup_add_ab_semigroup_add :
  'a ab_semigroup_add -> 'a semigroup_add;

type 'a comm_monoid_add =
  {ab_semigroup_add_comm_monoid_add : 'a ab_semigroup_add,
    monoid_add_comm_monoid_add : 'a monoid_add};
val ab_semigroup_add_comm_monoid_add = #ab_semigroup_add_comm_monoid_add :
  'a comm_monoid_add -> 'a ab_semigroup_add;
val monoid_add_comm_monoid_add = #monoid_add_comm_monoid_add :
  'a comm_monoid_add -> 'a monoid_add;

val ab_semigroup_add_nat = {semigroup_add_ab_semigroup_add = semigroup_add_nat}
  : nat ab_semigroup_add;

val comm_monoid_add_nat =
  {ab_semigroup_add_comm_monoid_add = ab_semigroup_add_nat,
    monoid_add_comm_monoid_add = monoid_add_nat}
  : nat comm_monoid_add;

datatype ('a, 'b) weights_ext =
  Weights_ext of
    ('a * nat -> nat) * nat * ('a * nat -> 'a * nat -> bool) * ('a -> bool) *
      ('a * nat -> nat -> nat) * 'b;

datatype num = One | Bit0 of num | Bit1 of num;

fun sgn_integer k =
  (if ((k : IntInf.int) = (0 : IntInf.int)) then (0 : IntInf.int)
    else (if IntInf.< (k, (0 : IntInf.int)) then (~1 : IntInf.int)
           else (1 : IntInf.int)));

fun apsnd f (x, y) = (x, f y);

fun divmod_integer k l =
  (if ((k : IntInf.int) = (0 : IntInf.int))
    then ((0 : IntInf.int), (0 : IntInf.int))
    else (if ((l : IntInf.int) = (0 : IntInf.int)) then ((0 : IntInf.int), k)
           else (apsnd o (fn a => fn b => IntInf.* (a, b)) o sgn_integer) l
                  (if (((sgn_integer k) : IntInf.int) = (sgn_integer l))
                    then IntInf.divMod (IntInf.abs k, IntInf.abs l)
                    else let
                           val (r, s) =
                             IntInf.divMod (IntInf.abs k, IntInf.abs l);
                         in
                           (if ((s : IntInf.int) = (0 : IntInf.int))
                             then (IntInf.~ r, (0 : IntInf.int))
                             else (IntInf.- (IntInf.~ r, (1 : IntInf.int)),
                                    IntInf.- (IntInf.abs l, s)))
                         end)));

fun fst (x1, x2) = x1;

fun divide_integer k l = fst (divmod_integer k l);

fun divide_nat m n = Nat (divide_integer (integer_of_nat m) (integer_of_nat n));

fun times_nat m n = Nat (IntInf.* (integer_of_nat m, integer_of_nat n));

fun max A_ a b = (if less_eq A_ a b then b else a);

val ord_integer =
  {less_eq = (fn a => fn b => IntInf.<= (a, b)),
    less = (fn a => fn b => IntInf.< (a, b))}
  : IntInf.int ord;

fun nat_of_integer k = Nat (max ord_integer (0 : IntInf.int) k);

val one_nat : nat = Nat (1 : IntInf.int);

fun suc n = plus_nata n one_nat;

fun triangle n =
  divide_nat (times_nat n (suc n)) (nat_of_integer (2 : IntInf.int));

fun prod_encode x = (fn (m, n) => plus_nata (triangle (plus_nata m n)) m) x;

val weights_nat : (nat, unit) weights_ext =
  Weights_ext
    (suc o prod_encode, one_nat,
      (fn (f, n) => fn (g, m) =>
        less_nat g f orelse equal_nata f g andalso less_nat m n),
      (fn n => equal_nata n zero_nata), (fn _ => fn _ => one_nat), ());

type 'a weighted = {weights : ('a, unit) weights_ext};
val weights = #weights : 'a weighted -> ('a, unit) weights_ext;

val weighted_nat = {weights = weights_nat} : nat weighted;

fun list_all p [] = true
  | list_all p (x :: xs) = p x andalso list_all p xs;

datatype 'a set = Set of 'a list | Coset of 'a list;

fun membera A_ [] y = false
  | membera A_ (x :: xs) y = eq A_ x y orelse membera A_ xs y;

fun member A_ x (Coset xs) = not (membera A_ xs x)
  | member A_ x (Set xs) = membera A_ xs x;

fun null [] = true
  | null (x :: xs) = false;

fun less_eq_set A_ (Coset xs) (Set ys) =
  (if null xs andalso null ys then false
    else (raise Fail
           "subset_eq (List.coset _) (List.set _) requires type class instance card_UNIV")
           (fn _ => less_eq_set A_ (Coset xs) (Set ys)))
  | less_eq_set A_ a (Coset ys) = list_all (fn y => not (member A_ y a)) ys
  | less_eq_set A_ (Set xs) b = list_all (fn x => member A_ x b) xs;

fun equal_seta A_ a b = less_eq_set A_ a b andalso less_eq_set A_ b a;

fun equal_set A_ = {equal = equal_seta A_} : 'a set equal;

fun equal_boola p true = p
  | equal_boola p false = not p
  | equal_boola true p = p
  | equal_boola false p = not p;

val equal_bool = {equal = equal_boola} : bool equal;

fun equal_lista A_ [] (x21 :: x22) = false
  | equal_lista A_ (x21 :: x22) [] = false
  | equal_lista A_ (x21 :: x22) (y21 :: y22) =
    eq A_ x21 y21 andalso equal_lista A_ x22 y22
  | equal_lista A_ [] [] = true;

fun equal_list A_ = {equal = equal_lista A_} : ('a list) equal;

fun comparator_list comp_a (x :: xa) (y :: ya) =
  (case comp_a x y of Eq => comparator_list comp_a xa ya | Lt => Lt | Gt => Gt)
  | comparator_list comp_a (x :: xa) [] = Gt
  | comparator_list comp_a [] (y :: ya) = Lt
  | comparator_list comp_a [] [] = Eq;

fun compare_lista A_ = comparator_list (compare A_);

fun compare_list A_ = {compare = compare_lista A_} : ('a list) compare;

datatype ('a, 'b) term = Var of 'b | Fun of 'a * ('a, 'b) term list;

fun equal_term A_ B_ = {equal = equal_terma A_ B_} : ('a, 'b) term equal
and equal_terma A_ B_ (Var x1) (Fun (x21, x22)) = false
  | equal_terma A_ B_ (Fun (x21, x22)) (Var x1) = false
  | equal_terma A_ B_ (Fun (x21, x22)) (Fun (y21, y22)) =
    eq A_ x21 y21 andalso equal_lista (equal_term A_ B_) x22 y22
  | equal_terma A_ B_ (Var x1) (Var y1) = eq B_ x1 y1;

fun comparator_term comp_f comp_v (Fun (x, xa)) (Fun (ya, yb)) =
  (case comp_f x ya
    of Eq => comparator_list (comparator_term comp_f comp_v) xa yb | Lt => Lt
    | Gt => Gt)
  | comparator_term comp_f comp_v (Fun (x, xa)) (Var y) = Gt
  | comparator_term comp_f comp_v (Var x) (Fun (ya, yb)) = Lt
  | comparator_term comp_f comp_v (Var x) (Var y) = comp_v x y;

fun compare_terma A_ B_ = comparator_term (compare A_) (compare B_);

fun compare_term A_ B_ = {compare = compare_terma A_ B_} :
  ('a, 'b) term compare;

fun equal_option A_ NONE (SOME x2) = false
  | equal_option A_ (SOME x2) NONE = false
  | equal_option A_ (SOME x2) (SOME y2) = eq A_ x2 y2
  | equal_option A_ NONE NONE = true;

fun extract p (x :: xs) =
  (if p x then SOME ([], (x, xs))
    else (case extract p xs of NONE => NONE
           | SOME (ys, (y, zs)) => SOME (x :: ys, (y, zs))))
  | extract p [] = NONE;

fun subset_eq_mset_impl A_ [] ys = SOME (not (null ys))
  | subset_eq_mset_impl A_ (x :: xs) ys =
    (case extract (eq A_ x) ys of NONE => NONE
      | SOME (ys1, (_, ys2)) => subset_eq_mset_impl A_ xs (ys1 @ ys2));

datatype 'a multiset = Mset of 'a list;

fun equal_multiseta A_ (Mset xs) (Mset ys) =
  equal_option equal_bool (subset_eq_mset_impl A_ xs ys) (SOME false);

fun equal_multiset A_ = {equal = equal_multiseta A_} : 'a multiset equal;

fun plus_multiseta (Mset xs) (Mset ys) = Mset (xs @ ys);

val plus_multiset = {plus = plus_multiseta} : 'a multiset plus;

val zero_multiseta : 'a multiset = Mset [];

val zero_multiset = {zero = zero_multiseta} : 'a multiset zero;

val semigroup_add_multiset = {plus_semigroup_add = plus_multiset} :
  'a multiset semigroup_add;

val monoid_add_multiset =
  {semigroup_add_monoid_add = semigroup_add_multiset,
    zero_monoid_add = zero_multiset}
  : 'a multiset monoid_add;

val ab_semigroup_add_multiset =
  {semigroup_add_ab_semigroup_add = semigroup_add_multiset} :
  'a multiset ab_semigroup_add;

val comm_monoid_add_multiset =
  {ab_semigroup_add_comm_monoid_add = ab_semigroup_add_multiset,
    monoid_add_comm_monoid_add = monoid_add_multiset}
  : 'a multiset comm_monoid_add;

fun equal_proda A_ B_ (x1, x2) (y1, y2) = eq A_ x1 y1 andalso eq B_ x2 y2;

fun equal_prod A_ B_ = {equal = equal_proda A_ B_} : ('a * 'b) equal;

fun comparator_prod comp_a comp_b (x, xa) (y, ya) =
  (case comp_a x y of Eq => comp_b xa ya | Lt => Lt | Gt => Gt);

fun compare_proda A_ B_ = comparator_prod (compare A_) (compare B_);

fun compare_prod A_ B_ = {compare = compare_proda A_ B_} : ('a * 'b) compare;

val one_integera : IntInf.int = (1 : IntInf.int);

type 'a one = {one : 'a};
val one = #one : 'a one -> 'a;

val one_integer = {one = one_integera} : IntInf.int one;

val zero_integer = {zero = (0 : IntInf.int)} : IntInf.int zero;

type 'a zero_neq_one = {one_zero_neq_one : 'a one, zero_zero_neq_one : 'a zero};
val one_zero_neq_one = #one_zero_neq_one : 'a zero_neq_one -> 'a one;
val zero_zero_neq_one = #zero_zero_neq_one : 'a zero_neq_one -> 'a zero;

val zero_neq_one_integer =
  {one_zero_neq_one = one_integer, zero_zero_neq_one = zero_integer} :
  IntInf.int zero_neq_one;

datatype 'a literal = Pos of 'a | Neg of 'a;

fun equal_literala A_ (Pos x1) (Neg x2) = false
  | equal_literala A_ (Neg x2) (Pos x1) = false
  | equal_literala A_ (Neg x2) (Neg y2) = eq A_ x2 y2
  | equal_literala A_ (Pos x1) (Pos y1) = eq A_ x1 y1;

fun equal_literal A_ = {equal = equal_literala A_} : 'a literal equal;

datatype char = Chara of bool * bool * bool * bool * bool * bool * bool * bool;

fun id x = (fn xa => xa) x;

fun upt i j = (if less_nat i j then i :: upt (suc i) j else []);

fun zip (x :: xs) (y :: ys) = (x, y) :: zip xs ys
  | zip xs [] = []
  | zip [] ys = [];

fun ball (Set xs) p = list_all p xs;

fun fold f (x :: xs) s = fold f xs (f x s)
  | fold f [] s = s;

fun last (x :: xs) = (if null xs then x else last xs);

fun maps f [] = []
  | maps f (x :: xs) = f x @ maps f xs;

fun map f [] = []
  | map f (x21 :: x22) = f x21 :: map f x22;

fun image f (Set xs) = Set (map f xs);

fun gen_length n (x :: xs) = gen_length (suc n) xs
  | gen_length n [] = n;

fun size_lista x = gen_length zero_nata x;

fun root (Var x) = NONE
  | root (Fun (f, ts)) = SOME (f, size_lista ts);

fun foldr f [] = id
  | foldr f (x :: xs) = f x o foldr f xs;

fun minus_nat m n =
  Nat (max ord_integer (0 : IntInf.int)
        (IntInf.- (integer_of_nat m, integer_of_nat n)));

fun funpow n f =
  (if equal_nata n zero_nata then id else f o funpow (minus_nat n one_nat) f);

fun removeAll A_ x [] = []
  | removeAll A_ x (y :: xs) =
    (if eq A_ x y then removeAll A_ x xs else y :: removeAll A_ x xs);

fun inserta A_ x xs = (if membera A_ xs x then xs else x :: xs);

fun insert A_ x (Coset xs) = Coset (removeAll A_ x xs)
  | insert A_ x (Set xs) = Set (inserta A_ x xs);

fun fun_upd A_ f a b = (fn x => (if eq A_ x a then b else f x));

fun subst A_ x t = fun_upd A_ Var x t;

fun concat xss = foldr (fn a => fn b => a @ b) xss [];

fun filter p [] = []
  | filter p (x :: xs) = (if p x then x :: filter p xs else filter p xs);

fun bind NONE f = NONE
  | bind (SOME x) f = f x;

fun replicate n x =
  (if equal_nata n zero_nata then []
    else x :: replicate (minus_nat n one_nat) x);

fun scf_list scf xs =
  maps (fn (x, i) => replicate (scf i) x)
    (zip xs (upt zero_nata (size_lista xs)));

fun scf_term scf (Var x) = Var x
  | scf_term scf (Fun (f, ts)) =
    Fun (f, scf_list (scf (f, size_lista ts)) (map (scf_term scf) ts));

fun hd (x21 :: x22) = x21;

fun list_ex p [] = false
  | list_ex p (x :: xs) = p x orelse list_ex p xs;

fun remdups A_ [] = []
  | remdups A_ (x :: xs) =
    (if membera A_ xs x then remdups A_ xs else x :: remdups A_ xs);

fun remove1 A_ x [] = []
  | remove1 A_ x (y :: xs) = (if eq A_ x y then xs else y :: remove1 A_ x xs);

fun subseqs [] = [[]]
  | subseqs (x :: xs) = let
                          val xss = subseqs xs;
                        in
                          map (fn a => x :: a) xss @ xss
                        end;

fun is_none (SOME x) = false
  | is_none NONE = true;

fun of_bool A_ true = one (one_zero_neq_one A_)
  | of_bool A_ false = zero (zero_zero_neq_one A_);

fun integer_of_char (Chara (b0, b1, b2, b3, b4, b5, b6, b7)) =
  IntInf.+ (IntInf.* (IntInf.+ (IntInf.* (IntInf.+ (IntInf.* (IntInf.+ (IntInf.* (IntInf.+ (IntInf.* (IntInf.+ (IntInf.* (IntInf.+ (IntInf.* (of_bool
                        zero_neq_one_integer
                        b7, (2 : IntInf.int)), of_bool zero_neq_one_integer
         b6), (2 : IntInf.int)), of_bool zero_neq_one_integer
                                   b5), (2 : IntInf.int)), of_bool
                     zero_neq_one_integer
                     b4), (2 : IntInf.int)), of_bool zero_neq_one_integer
       b3), (2 : IntInf.int)), of_bool zero_neq_one_integer
                                 b2), (2 : IntInf.int)), of_bool
                   zero_neq_one_integer
                   b1), (2 : IntInf.int)), of_bool zero_neq_one_integer b0);

fun implode cs =
  (String.implode
    o map (fn k => if 0 <= k andalso k < 128 then (Char.chr o IntInf.toInt) k else raise Fail "Non-ASCII character in literal"))
    (map integer_of_char cs);

fun map_filter f [] = []
  | map_filter f (x :: xs) =
    (case f x of NONE => map_filter f xs | SOME y => y :: map_filter f xs);

fun count A_ (Mset xs) x =
  fold (fn y => (if eq A_ x y then suc else id)) xs zero_nata;

fun wcount A_ f m = (fn x => times_nat (count A_ m x) (suc (f x)));

fun le_of_comp acomp x y =
  (case acomp x y of Eq => true | Lt => true | Gt => false);

fun insort_key B_ f x (y :: ys) =
  (if le_of_comp (compare B_) (f x) (f y) then x :: y :: ys
    else y :: insort_key B_ f x ys)
  | insort_key B_ f x [] = [x];

fun sort_key B_ f xs = foldr (insort_key B_ f) xs [];

fun sorted_list_of_set (A1_, A2_) (Set xs) =
  sort_key A1_ (fn x => x) (remdups A2_ xs);

fun pairsa (x :: y :: xs) = (x, y) :: pairsa (y :: xs)
  | pairsa [] = []
  | pairsa [v] = [];

fun pairs (A1_, A2_) aaa =
  concat
    (sorted_list_of_set
      (compare_list (compare_prod A1_ A1_), equal_list (equal_prod A2_ A2_))
      (image (pairsa o sorted_list_of_set (A1_, A2_)) aaa));

fun add_mset x (Mset xs) = Mset (x :: xs);

fun set_mset (Mset xs) = Set xs;

fun the (SOME x2) = x2;

fun shows_string x = (fn a => x @ a);

fun subst_apply_term (Var x) sigma = sigma x
  | subst_apply_term (Fun (f, ss)) sigma =
    Fun (f, map (fn t => subst_apply_term t sigma) ss);

fun snd (x1, x2) = x2;

fun subst_list sigma ys =
  map (fn p => (subst_apply_term (fst p) sigma, subst_apply_term (snd p) sigma))
    ys;

fun zip_option [] [] = SOME []
  | zip_option (x :: xs) (y :: ys) =
    bind (zip_option xs ys) (fn zs => SOME ((x, y) :: zs))
  | zip_option (x :: xs) [] = NONE
  | zip_option [] (y :: ys) = NONE;

fun decompose A_ s t =
  (case (s, t) of (Var _, _) => NONE | (Fun (_, _), Var _) => NONE
    | (Fun (f, ss), Fun (g, ts)) =>
      (if eq A_ f g then zip_option ss ts else NONE));

fun sup_set A_ (Coset xs) a = Coset (filter (fn x => not (member A_ x a)) xs)
  | sup_set A_ (Set xs) a = fold (insert A_) xs a;

val bot_set : 'a set = Set [];

fun sup_seta A_ (Set xs) = fold (sup_set A_) xs bot_set;

fun vars_term B_ (Var x1) = insert B_ x1 bot_set
  | vars_term B_ (Fun (x21, x22)) =
    sup_seta B_ (image (vars_term B_) (Set x22));

fun unify A_ B_ [] bs = SOME bs
  | unify A_ B_ ((Fun (f, ss), Fun (g, ts)) :: e) bs =
    (case decompose A_ (Fun (f, ss)) (Fun (g, ts)) of NONE => NONE
      | SOME us => unify A_ B_ (us @ e) bs)
  | unify A_ B_ ((Var x, t) :: e) bs =
    (if equal_terma A_ B_ t (Var x) then unify A_ B_ e bs
      else (if member B_ x (vars_term B_ t) then NONE
             else unify A_ B_ (subst_list (subst B_ x t) e) ((x, t) :: bs)))
  | unify A_ B_ ((Fun (v, va), Var x) :: e) bs =
    (if member B_ x (vars_term B_ (Fun (v, va))) then NONE
      else unify A_ B_ (subst_list (subst B_ x (Fun (v, va))) e)
             ((x, Fun (v, va)) :: bs));

fun apfst f (x, y) = (f x, y);

fun subst_compose sigma tau = (fn x => subst_apply_term (sigma x) tau);

fun lex_ext_unbounded f [] [] = (false, true)
  | lex_ext_unbounded f (uu :: uv) [] = (true, true)
  | lex_ext_unbounded f [] (uw :: ux) = (false, false)
  | lex_ext_unbounded f (a :: asa) (b :: bs) =
    (case f a b of (true, _) => (true, true)
      | (false, true) => lex_ext_unbounded f asa bs
      | (false, false) => (false, false));

fun pr_strict (Weights_ext (wa, w0, pr_strict, least, scf, more)) = pr_strict;

fun least (Weights_ext (wa, w0, pr_strict, least, scf, more)) = least;

fun scf (Weights_ext (wa, w0, pr_strict, least, scf, more)) = scf;

fun subseteq_mset A_ (Mset xs) (Mset ys) =
  not (is_none (subset_eq_mset_impl A_ xs ys));

fun sum_list A_ xs =
  foldr (plus ((plus_semigroup_add o semigroup_add_monoid_add) A_)) xs
    (zero (zero_monoid_add A_));

fun w0 (Weights_ext (wa, w0, pr_strict, least, scf, more)) = w0;

fun w (Weights_ext (wa, w0, pr_strict, least, scf, more)) = wa;

fun weight A_ (Var x) = w0 (weights A_)
  | weight A_ (Fun (f, ts)) =
    let
      val n = size_lista ts;
      val scff = scf (weights A_) (f, n);
    in
      plus_nata (w (weights A_) (f, n))
        (sum_list monoid_add_nat
          (map (fn (ti, i) => times_nat (weight A_ ti) (scff i))
            (zip ts (upt zero_nata n))))
    end;

fun sum_mset A_ (Mset xs) = sum_list (monoid_add_comm_monoid_add A_) xs;

fun vars_term_ms (Var x) = add_mset x zero_multiseta
  | vars_term_ms (Fun (f, ts)) =
    sum_mset comm_monoid_add_multiset (Mset (map vars_term_ms ts));

fun kbo (A1_, A2_) B_ s t =
  let
    val wt = weight A2_ t;
    val ws = weight A2_ s;
  in
    (if subseteq_mset B_ (vars_term_ms (scf_term (scf (weights A2_)) t))
          (vars_term_ms (scf_term (scf (weights A2_)) s)) andalso
          less_eq_nat wt ws
      then (if less_nat wt ws then (true, true)
             else (case s
                    of Var _ =>
                      (false,
                        (case t of Var _ => true
                          | Fun (g, ts) =>
                            null ts andalso least (weights A2_) g))
                    | Fun (f, ss) =>
                      (case t of Var _ => (true, true)
                        | Fun (g, ts) =>
                          (if pr_strict (weights A2_) (f, size_lista ss)
                                (g, size_lista ts)
                            then (true, true)
                            else (if equal_proda A1_ equal_nat
                                       (f, size_lista ss) (g, size_lista ts)
                                   then lex_ext_unbounded (kbo (A1_, A2_) B_) ss
  ts
                                   else (false, false))))))
      else (false, false))
  end;

fun size_list x [] = zero_nata
  | size_list x (x21 :: x22) =
    plus_nata (plus_nata (x x21) (size_list x x22)) (suc zero_nata);

fun image_mset f (Mset xs) = Mset (map f xs);

fun map_option f NONE = NONE
  | map_option f (SOME x2) = SOME (f x2);

fun subst_of A_ ss =
  foldr (fn (x, t) => fn sigma => subst_compose sigma (subst A_ x t)) ss Var;

fun mgu_sets (A1_, A2_) (B1_, B2_) aaa =
  map_option (subst_of B2_)
    (unify A2_ B2_ (pairs (compare_term A1_ B1_, equal_term A2_ B2_) aaa) []);

fun atm_of (Pos x1) = x1
  | atm_of (Neg x2) = x2;

fun atms_of c = image atm_of (set_mset c);

fun sum A_ B_ g (Set xs) =
  sum_list (monoid_add_comm_monoid_add B_) (map g (remdups A_ xs));

fun size_multiset A_ f m =
  sum A_ comm_monoid_add_nat (wcount A_ f m) (set_mset m);

fun vars_clause B_ c =
  sup_seta B_ (set_mset (image_mset (fn l => vars_term B_ (atm_of l)) c));

fun replicate_mset n x = funpow n (add_mset x) zero_multiseta;

fun less_kbo (A1_, A2_) B_ s t = fst (kbo (A1_, A2_) B_ t s);

fun match_term_list A_ B_ C_ [] sigma = SOME sigma
  | match_term_list A_ B_ C_ ((Var x, t) :: p) sigma =
    (if is_none (sigma x) orelse
          equal_option (equal_term A_ C_) (sigma x) (SOME t)
      then match_term_list A_ B_ C_ p (fun_upd B_ sigma x (SOME t)) else NONE)
  | match_term_list A_ B_ C_ ((Fun (f, ss), Fun (g, ts)) :: p) sigma =
    (case decompose A_ (Fun (f, ss)) (Fun (g, ts)) of NONE => NONE
      | SOME us => match_term_list A_ B_ C_ (us @ p) sigma)
  | match_term_list A_ B_ C_ ((Fun (f, ss), Var x) :: p) sigma = NONE;

fun remdups_gen B_ f [] = []
  | remdups_gen B_ f (x :: xs) =
    x :: remdups_gen B_ f (filter (fn y => not (eq B_ (f x) (f y))) xs);

fun modulo_integer k l = snd (divmod_integer k l);

fun modulo_nat m n = Nat (modulo_integer (integer_of_nat m) (integer_of_nat n));

fun string_of_digit n =
  (if equal_nata n zero_nata
    then [Chara (false, false, false, false, true, true, false, false)]
    else (if equal_nata n one_nat
           then [Chara (true, false, false, false, true, true, false, false)]
           else (if equal_nata n (nat_of_integer (2 : IntInf.int))
                  then [Chara (false, true, false, false, true, true, false,
                                false)]
                  else (if equal_nata n (nat_of_integer (3 : IntInf.int))
                         then [Chara (true, true, false, false, true, true,
                                       false, false)]
                         else (if equal_nata n (nat_of_integer (4 : IntInf.int))
                                then [Chara
(false, false, true, false, true, true, false, false)]
                                else (if equal_nata n
   (nat_of_integer (5 : IntInf.int))
                                       then [Chara
       (true, false, true, false, true, true, false, false)]
                                       else (if equal_nata n
          (nat_of_integer (6 : IntInf.int))
      then [Chara (false, true, true, false, true, true, false, false)]
      else (if equal_nata n (nat_of_integer (7 : IntInf.int))
             then [Chara (true, true, true, false, true, true, false, false)]
             else (if equal_nata n (nat_of_integer (8 : IntInf.int))
                    then [Chara (false, false, false, true, true, true, false,
                                  false)]
                    else [Chara (true, false, false, true, true, true, false,
                                  false)])))))))));

fun showsp_nat p n =
  (if less_nat n (nat_of_integer (10 : IntInf.int))
    then shows_string (string_of_digit n)
    else showsp_nat p (divide_nat n (nat_of_integer (10 : IntInf.int))) o
           shows_string
             (string_of_digit
               (modulo_nat n (nat_of_integer (10 : IntInf.int)))));

fun map_literal f (Pos x1) = Pos (f x1)
  | map_literal f (Neg x2) = Neg (f x2);

fun subst_lit subst_atm l sigma = map_literal (fn a => subst_atm a sigma) l;

fun subst_cls subst_atm aa sigma =
  image_mset (fn a => subst_lit subst_atm a sigma) aa;

fun subst_cls_lists subst_atm cs sigma_s =
  map (fn (a, b) => subst_cls subst_atm a b) (zip cs sigma_s);

fun maxa A_ (Set (x :: xs)) =
  fold (max ((ord_preorder o preorder_order o order_linorder) A_)) xs x;

fun vars_clause_list B_ cs = sup_seta B_ (image (vars_clause B_) (Set cs));

fun renamings_apart [] = []
  | renamings_apart (c :: cs) =
    let
      val sigma_s = renamings_apart cs;
    in
      (fn v =>
        Var (plus_nata
              (plus_nata v
                (maxa linorder_nat
                  (sup_set equal_nat
                    (vars_clause_list equal_nat
                      (subst_cls_lists subst_apply_term cs sigma_s))
                    (insert equal_nat zero_nata bot_set))))
              one_nat)) ::
        sigma_s
    end;

fun is_pos (Pos x1) = true
  | is_pos (Neg x2) = false;

fun size_term (Var x1) = suc zero_nata
  | size_term (Fun (x21, x22)) =
    plus_nata (size_list size_term x22) (suc zero_nata);

fun less_eq_prod (A1_, A2_) (B1_, B2_) =
  le_of_comp
    (comparator_prod (comparator_of (A1_, A2_)) (comparator_of (B1_, B2_)));

fun leq_head (A1_, A2_) t u =
  (case (root t, root u) of (NONE, _) => true | (SOME _, NONE) => false
    | (SOME a, SOME b) =>
      less_eq_prod (A1_, A2_) (equal_nat, linorder_nat) a b);

fun leq_lit (A1_, A2_) l k =
  (case (k, l) of (Pos _, Pos _) => leq_head (A1_, A2_) (atm_of l) (atm_of k)
    | (Pos _, Neg _) => false | (Neg _, Pos _) => true
    | (Neg _, Neg _) => leq_head (A1_, A2_) (atm_of l) (atm_of k));

fun quicksort uu [] = []
  | quicksort r (x :: xs) =
    quicksort r (filter (fn y => r y x) xs) @
      [x] @ quicksort r (filter (fn y => not (r y x)) xs);

fun size_literal x (Pos x1) = plus_nata (x x1) (suc zero_nata)
  | size_literal x (Neg x2) = plus_nata (x x2) (suc zero_nata);

fun st0 (A1_, A2_) = (fn n0 => fn n0a => (n0, ([], ([], n0a))));

fun subsumes_list_filter (A1_, A2_) B_ [] ks sigma = true
  | subsumes_list_filter (A1_, A2_) B_ (l :: ls) ks sigma =
    let
      val ksa = filter (leq_lit (A1_, A2_) l) ks;
    in
      list_ex
        (fn k =>
          equal_boola (is_pos k) (is_pos l) andalso
            (case match_term_list A1_ B_ B_ [(atm_of l, atm_of k)] sigma
              of NONE => false
              | SOME a =>
                subsumes_list_filter (A1_, A2_) B_ ls
                  (remove1 (equal_literal (equal_term A1_ B_)) k ksa) a))
        ksa
    end;

fun minus_multiset A_ (Mset xs) (Mset ys) = Mset (fold (remove1 A_) ys xs);

fun shows_prec_nat x = showsp_nat x;

fun maximal_wrt (A1_, A2_, A3_) a c =
  ball (atms_of c) (fn b => not (less_kbo (A2_, A3_) equal_nat a b));

fun strictly_maximal_wrt (A1_, A2_, A3_) a c =
  ball (atms_of c)
    (fn b =>
      not (equal_terma A2_ equal_nat a b) andalso
        not (less_kbo (A2_, A3_) equal_nat a b));

fun resolvable (A1_, A2_, A3_) a d ca ls =
  let
    val sigma =
      mgu_sets (compare_compare_order A1_, A2_) (compare_nat, equal_nat)
        (insert (equal_set (equal_term A2_ equal_nat))
          (insert (equal_term A2_ equal_nat) a (atms_of (Mset ls))) bot_set);
  in
    not (is_none sigma) andalso
      (not (null ls) andalso
        (maximal_wrt (A1_, A2_, A3_) (subst_apply_term a (the sigma))
           (subst_cls subst_apply_term (add_mset (Neg a) (Mset d))
             (the sigma)) andalso
          (strictly_maximal_wrt (A1_, A2_, A3_) (subst_apply_term a (the sigma))
             (subst_cls subst_apply_term
               (minus_multiset (equal_literal (equal_term A2_ equal_nat))
                 (Mset ca) (Mset ls))
               (the sigma)) andalso
            list_all is_pos ls)))
  end;

fun remove_all A_ xs [] = xs
  | remove_all A_ xs (y :: ys) =
    (if membera A_ xs y then remove_all A_ (remove1 A_ y xs) ys
      else remove_all A_ xs ys);

fun resolvent (A1_, A2_, A3_) d a ca ls =
  map (fn m =>
        subst_lit subst_apply_term m
          (the (mgu_sets (compare_compare_order A1_, A2_)
                 (compare_nat, equal_nat)
                 (insert (equal_set (equal_term A2_ equal_nat))
                   (insert (equal_term A2_ equal_nat) a (atms_of (Mset ls)))
                   bot_set))))
    (remove_all (equal_literal (equal_term A2_ equal_nat)) ca ls @ d);

fun resolve_on (A1_, A2_, A3_) a d ca =
  map_filter
    (fn x =>
      (if resolvable (A1_, A2_, A3_) a d ca x
        then SOME (resolvent (A1_, A2_, A3_) d a ca x) else NONE))
    (subseqs ca);

fun resolve (A1_, A2_, A3_) c d =
  maps (fn l =>
         (case l of Pos _ => []
           | Neg a =>
             (if maximal_wrt (A1_, A2_, A3_) a (Mset d)
               then resolve_on (A1_, A2_, A3_) a
                      (remove1 (equal_literal (equal_term A2_ equal_nat)) l d) c
               else [])))
    d;

fun resolve_rename (A1_, A2_, A3_) c d =
  let
    val sigma_s = renamings_apart [Mset d, Mset c];
  in
    resolve (A1_, A2_, A3_)
      (map (fn l => subst_lit subst_apply_term l (last sigma_s)) c)
      (map (fn l => subst_lit subst_apply_term l (hd sigma_s)) d)
  end;

fun resolve_rename_either_way (A1_, A2_, A3_) c d =
  resolve_rename (A1_, A2_, A3_) c d @ resolve_rename (A1_, A2_, A3_) d c;

fun weighta (A1_, A2_, A3_) (c, i) =
  plus_nata
    (times_nat one_nat
      (size_multiset (equal_literal (equal_term A2_ equal_nat))
        (size_literal size_term) c))
    (times_nat one_nat i);

fun select_min_weight_clause (A1_, A2_, A3_) ci (dj :: djs) =
  select_min_weight_clause (A1_, A2_, A3_)
    (if less_nat (weighta (A1_, A2_, A3_) (apfst Mset dj))
          (weighta (A1_, A2_, A3_) (apfst Mset ci))
      then dj else ci)
    djs
  | select_min_weight_clause (A1_, A2_, A3_) ci [] = ci;

fun strictly_subsume (A1_, A2_, A3_) ds c =
  list_ex
    (fn d =>
      subsumes_list_filter (A2_, linorder_compare_order A1_) equal_nat
        (quicksort (leq_lit (A2_, linorder_compare_order A1_)) d) c
        (fn _ => NONE) andalso
        not (subsumes_list_filter (A2_, linorder_compare_order A1_) equal_nat
              (quicksort (leq_lit (A2_, linorder_compare_order A1_)) c) d
              (fn _ => NONE)))
    ds;

fun remdups_clss (A1_, A2_, A3_) [] = []
  | remdups_clss (A1_, A2_, A3_) (ci :: cis) =
    let
      val cia = select_min_weight_clause (A1_, A2_, A3_) ci cis;
    in
      cia ::
        remdups_clss (A1_, A2_, A3_)
          (filter
            (fn (d, _) =>
              not (equal_multiseta (equal_literal (equal_term A2_ equal_nat))
                    (Mset d) (Mset (fst cia))))
            (ci :: cis))
    end;

fun is_tautology (A1_, A2_, A3_) c =
  list_ex
    (fn a =>
      membera (equal_literal (equal_term A2_ equal_nat)) c (Pos a) andalso
        membera (equal_literal (equal_term A2_ equal_nat)) c (Neg a))
    (map atm_of c);

fun is_reducible_lit (A1_, A2_, A3_) ds c l =
  list_ex
    (fn d =>
      list_ex
        (fn la =>
          (if equal_boola (is_pos la) (not (is_pos l))
            then (case match_term_list A2_ equal_nat equal_nat
                         [(atm_of la, atm_of l)] (fn _ => NONE)
                   of NONE => false
                   | SOME a =>
                     subsumes_list_filter (A2_, linorder_compare_order A1_)
                       equal_nat
                       (quicksort (leq_lit (A2_, linorder_compare_order A1_))
                         (remove1 (equal_literal (equal_term A2_ equal_nat)) la
                           d))
                       c a)
            else false))
        d)
    ds;

fun reduce (A1_, A2_, A3_) ds ca (l :: c) =
  (if is_reducible_lit (A1_, A2_, A3_) ds (ca @ c) l
    then reduce (A1_, A2_, A3_) ds ca c
    else l :: reduce (A1_, A2_, A3_) ds (l :: ca) c)
  | reduce (A1_, A2_, A3_) uu uv [] = [];

fun reduce_all2 (A1_, A2_, A3_) d (ci :: cs) =
  let
    val (c, i) = ci;
    val ca = reduce (A1_, A2_, A3_) [d] [] c;
  in
    (if equal_lista (equal_literal (equal_term A2_ equal_nat)) ca c then apsnd
      else apfst)
      (fn a => (ca, i) :: a)
      (reduce_all2 (A1_, A2_, A3_) d cs)
  end
  | reduce_all2 (A1_, A2_, A3_) uu [] = ([], []);

fun reduce_all (A1_, A2_, A3_) d = map (apfst (reduce (A1_, A2_, A3_) [d] []));

fun subsume (A1_, A2_, A3_) ds c =
  list_ex
    (fn d =>
      subsumes_list_filter (A2_, linorder_compare_order A1_) equal_nat
        (quicksort (leq_lit (A2_, linorder_compare_order A1_)) d) c
        (fn _ => NONE))
    ds;

fun deterministic_RP_step (A1_, A2_, A3_) (na, (p, (q, n))) =
  (if list_ex (fn ci => null (fst ci)) (p @ q)
    then ([], ([], (remdups_clss (A1_, A2_, A3_) p @ q,
                     plus_nata n
                       (size_lista (remdups_clss (A1_, A2_, A3_) p)))))
    else (case na
           of [] =>
             (case p of [] => (na, (p, (q, n)))
               | p0 :: pa =>
                 let
                   val (c, i) = select_min_weight_clause (A1_, A2_, A3_) p0 pa;
                   val naa =
                     map (fn d => (d, n))
                       (remdups_gen
                         (equal_multiset
                           (equal_literal (equal_term A2_ equal_nat)))
                         Mset
                         (resolve_rename (A1_, A2_, A3_) c c @
                           maps (resolve_rename_either_way (A1_, A2_, A3_) c o
                                  fst)
                             q));
                   val pb =
                     filter
                       (fn (d, _) =>
                         not (equal_multiseta
                               (equal_literal (equal_term A2_ equal_nat))
                               (Mset d) (Mset c)))
                       p;
                   val qa = (c, i) :: q;
                   val nb = suc n;
                 in
                   (naa, (pb, (qa, nb)))
                 end)
           | (c, i) :: naa =>
             let
               val ca = reduce (A1_, A2_, A3_) (map fst (p @ q)) [] c;
             in
               (if null ca then ([], ([], ([([], i)], suc n)))
                 else (if is_tautology (A1_, A2_, A3_) ca orelse
                            subsume (A1_, A2_, A3_) (map fst (p @ q)) ca
                        then (naa, (p, (q, n)))
                        else let
                               val pa = reduce_all (A1_, A2_, A3_) ca p;
                               val (back_to_P, qa) =
                                 reduce_all2 (A1_, A2_, A3_) ca q;
                               val pb = back_to_P @ pa;
                               val qb =
                                 filter
                                   (not o strictly_subsume (A1_, A2_, A3_)
    [ca] o
                                     fst)
                                   qa;
                               val pc =
                                 filter
                                   (not o strictly_subsume (A1_, A2_, A3_)
    [ca] o
                                     fst)
                                   pb;
                               val pd = (ca, i) :: pc;
                             in
                               (naa, (pd, (qb, n)))
                             end))
             end));

fun is_final_dstate (A1_, A2_) (na, (p, (q, n))) = null na andalso null p;

fun deterministic_RP (A1_, A2_, A3_) st =
  (if is_final_dstate (A1_, A3_) st then let
   val (_, (_, (q, _))) = st;
 in
   SOME (map fst q)
 end
    else deterministic_RP (A1_, A2_, A3_)
           (deterministic_RP_step (A1_, A2_, A3_) st));

fun prover n =
  (case deterministic_RP (compare_order_nat, equal_nat, weighted_nat)
          (st0 (compare_order_nat, weighted_nat) n zero_nata)
    of NONE => true
    | SOME r =>
      not (membera (equal_list (equal_literal (equal_term equal_nat equal_nat)))
            r []));

fun string_literal_of_nat n = implode (shows_prec_nat zero_nata n []);

end; (*struct RPx*)
