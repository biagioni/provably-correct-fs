theory dev
  imports Main
begin

(* a data block is represented as a list of char, "char list" *)

type_synonym data_block = "char list"

fun init_block :: "nat \<Rightarrow> char list" where
"init_block 0 = []" |
"init_block n = (char_of_integer 0 # (init_block (n - 1)))"

lemma init_block_size :
"length (init_block n) = n"
  apply (induct n)
  apply (auto)
  done

fun block_from_integers :: "integer list \<Rightarrow> char list" where
"block_from_integers list = map char_of_integer list"

(* a device is essentially a read_block function.  Inspired by
   https://www.isa-afp.org/browser_info/Isabelle2021/AFP/Jordan_Normal_Form/Matrix.html *)
type_synonym dev = "nat \<Rightarrow> data_block"

definition initial_dev :: "nat \<Rightarrow> nat \<Rightarrow> data_block" where
"initial_dev block_size index = init_block block_size"

lemma initial_block_size :
"length ((initial_dev bs) bn) = bs"
  (* proof by sledgehammer cvc5 zipperposition vampire verit *)
  by (simp add: init_block_size initial_dev_def)

fun write_block :: "dev \<Rightarrow> nat \<Rightarrow> data_block \<Rightarrow> dev" where
"write_block dev bn data = (\<lambda> index . (if index = bn then data else dev index))"

(* true, but not needed for our theorem
lemma read_block_returns_immediately_written :
"(write_block dev bn data) bn = data"
  by simp
*)

(* function to demonstrate that even if we write any and all,
   except as long as we avoid the given block number/bn,
   the written device then still correctly returns
   the data block that was written *)
fun write_other_blocks :: "dev \<Rightarrow> nat \<Rightarrow> (nat * data_block) list \<Rightarrow> dev" where
"write_other_blocks dev avoid [] = dev" |
"write_other_blocks dev avoid ((first_bn, first_data) # rest) =
  (if first_bn = avoid then dev
   else write_block (write_other_blocks dev avoid rest) first_bn first_data)"

(* no matter what we write at indexes other than block_number/bn,
   reading block_number always returns the original value *)
theorem read_block_returns_most_recently_written :
"(write_other_blocks (write_block dev bn data) bn writes) bn = data"
  apply (induct writes)
  apply (auto)
  done

(* demonstrate that we can write a block and read it again *)
definition sample_block :: "data_block" where
"sample_block = (block_from_integers [1, 2, 3, 4])"

value "(write_block (initial_dev 4) 99 sample_block) 99"

(* a read of something that hasn't been written returns a block of 0s *)
value "(write_block (initial_dev 16) 99 sample_block) 98"

(* prove that writing constant-sized blocks of size block_size/bs
   always returns the same size *)
fun write_same_sized_blocks :: "dev \<Rightarrow> nat \<Rightarrow> (nat * data_block) list \<Rightarrow> dev" where
"write_same_sized_blocks dev bs [] = dev" |
"write_same_sized_blocks dev bs ((first_bn, first_data) # rest) =
  (if length first_data = bs then
    write_block (write_same_sized_blocks dev bs rest) first_bn first_data
   else dev)"

theorem constant_block_size :
"(length ((write_same_sized_blocks (initial_dev bs) bs writes) bn)) = bs"
proof (induct writes)
  case Nil
  then show ?case using initial_block_size by simp
next
  case (Cons a writes)
  then show ?case  (* proof found by sledgehammer cvc5 *)
    by (smt (verit) initial_block_size list.inject write_block.simps
        write_same_sized_blocks.elims)
qed

end
