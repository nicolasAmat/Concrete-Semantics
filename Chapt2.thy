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

lemma add_01[simp]: "Suc (add m n) = add m (Suc n)"
  apply(induction m)
  apply(auto)
  done
        
lemma add_02[simp]: "add m 0 = m"
  apply(induction m)
   apply(auto)
  done

theorem add_com: "add m n = add n m"
  apply(induction m)
   apply(auto)
  done
 
end