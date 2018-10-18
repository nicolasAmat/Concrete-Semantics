theory Chapt2

imports Main

begin

(* Exercise 2.1 *)

value "1 + (2::nat)"
value "1 + (2::int)"
value "1 - (2::nat)"
value "1 - (2::int)"


(* Exercise 2.2 *)

fun add :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
"add 0 n = n" |
"add (Suc m) n = Suc(add m n)"

fun double :: "nat \<Rightarrow> nat" where
"double 0 = 0" |
"double (Suc m) = Suc (Suc (double m))"

lemma add_01[simp]: "add m (Suc n) = Suc (add m n)"
  apply(induction m)
   apply(auto)
  done
        
lemma add_02[simp]: "add m 0 = m"
  apply(induction m)
   apply(auto)
  done

lemma add_commutative[simp]: "add m n = add n m"
  apply(induction m)
   apply(auto)
  done

lemma add_associative[simp]: "add x (add y z) = add (add x y) z"
  apply(induction x)
   apply(auto)
  done

lemma add_double[simp]: "double m = add m m"
  apply(induction m)
   apply(auto)
  done


(* Exercise 2.3 *)

fun app :: "'a list \<Rightarrow> 'a list \<Rightarrow> 'a list" where
"app Nil ys = ys" |
"app (Cons x xs) ys = Cons x (app xs ys)"

fun count :: "'a \<Rightarrow> 'a list \<Rightarrow> nat" where
"count x Nil = 0" |
"count y (x # xs) = (if x = y then Suc(count y xs) else count y xs)"

lemma count_inequality[simp]: "count x xs \<le> length xs"
  apply(induction xs)
  apply(auto)
  done


(* Exercise 2.4 *)
fun snoc :: "'a list \<Rightarrow> 'a \<Rightarrow> 'a list" where
"snoc [] x = [x]" |
"snoc (x # xs) y = x # (snoc xs y)"

fun reverse :: "'a list \<Rightarrow> 'a list" where
"reverse [] = []" |
"reverse (x # xs) = snoc (reverse xs) x"

lemma reverse_01[simp] : "reverse (snoc xs x) = x # reverse xs"
  apply(induction xs)
   apply(auto)
  done

lemma double_reverse[simp] : "reverse(reverse xs) = xs"
  apply(induction xs)
   apply(auto)
  done


(* Exercise 2.5 *)
fun sum_opto :: "nat \<Rightarrow> nat" where
"sum_opto 0 = 0" |
"sum_opto (Suc n) = (sum_opto n) + (Suc n)"

lemma formula_sum[simp] : "sum_opto n = n * (n + 1) div 2"
  apply(induction n)
   apply(auto)
  done

end