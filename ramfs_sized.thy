theory ramfs_sized
  imports Main
begin

(* the name of a file is a string, the contents are a list of numbers \<ge> 0 *)
(* to do: would it be possible to have the contents be a byte list?
 * what is a char in isabelle? *)

datatype read_result = Data "nat list" | File_Not_Found
datatype write_result = Written "(string * nat list) list" | Insufficent_Space | Exists

fun names :: "(string * nat list) list \<Rightarrow> string list" where
"names [] = []" |
"names ((first_name, first_data) # rest) = (first_name # (names rest))"

fun member :: "string list \<Rightarrow> string \<Rightarrow> bool" where
"member [] name = False" |
"member (first # rest) name = ((first = name) \<or> (member rest name))"

lemma member_equiv_to_set [simp]:
"(member xs x) \<Longrightarrow> x \<in> set (xs)"
proof (induct xs)
  case Nil
  then show ?case by simp
next
  case (Cons first rest)   (* proof found by sledgehammer cvc5 and vampire and verit and spass *)
  then show ?case by auto
qed

(* read_file returns File_Not_Found if the file is not found. *)
fun read_file :: "(string * nat list) list \<Rightarrow> string \<Rightarrow> read_result" where
"read_file [] name = File_Not_Found" |      (* file not found *)
"read_file ((first_name, first_data) # rest) name =
  (if name = first_name then Data first_data
   else read_file rest name)"


(* if name occurs more than once, removes all of the matching files
 * any file system created only as a result of write_file and remove
 * should not have duplicates, but have not yet figured out how to
 * express that in Isabelle, so might as well remove all. *)
fun remove :: "(string * nat list) list \<Rightarrow> string \<Rightarrow> (string * nat list) list" where
"remove [] name = []" |
"remove ((first_name, first_content) # rest) name =
  (if name = first_name then remove rest name
   else (first_name, first_content) # (remove rest name))"

fun has_file :: "(string * nat list) list \<Rightarrow> string \<Rightarrow> bool" where 
"has_file fs name = ((read_file fs name) \<noteq> File_Not_Found)"

fun not_in_fs :: "(string * nat list) list \<Rightarrow> string \<Rightarrow> bool" where 
"not_in_fs fs name = ((read_file fs name) = File_Not_Found)"

lemma has_not_opposites [simp]: "has_file fs name = (\<not> not_in_fs fs name)"
  by simp

fun has_file2 :: "(string * nat list) list \<Rightarrow> string \<Rightarrow> bool" where 
"has_file2 fs name = member (names fs) name"

lemma has_file_equiv [simp]:
"has_file fs name = has_file2 fs name"
proof (induct fs)
  case Nil
  then show ?case by auto
next
  case (Cons a fs)
  then show ?case
    by (smt (verit) has_file.simps has_file2.elims(1) list.distinct(1) list.inject member.elims(1) names.elims prod.inject read_file.elims
        read_result.simps(3))
qed

lemma name_not_in_empty_set [simp]: "name \<notin> set []"
  by simp
lemma name_not_in_empty_fs [simp]: "name \<notin> set (names [])"
  by simp
lemma empty_fs_does_not_have_file [simp]: "\<not>(has_file [] name)"
  by simp
lemma name_in_set_beginning_with_name [simp]: "name \<in> set (name # rest)"
  by simp
lemma name_in_fs_beginning_with_name [simp]: "name \<in> set (names ((name, content) # rest))"
  by simp

lemma has_file_correct :
"(if has_file fs name then name \<in> set (names fs)
  else name \<notin> set (names fs))"
proof (induct fs)
  case Nil
  then show ?case by simp
next
  case (Cons a list)
  then show ?case  (* proof found by sledghammer e *)
    by (metis has_file2.elims(1) has_file_equiv insert_iff list.simps(15) names.simps(2) old.prod.exhaust
        ramfs_sized.member.simps(2))
qed

lemma read_file_succeeds_if_file_in_fs :
"member (names fs) name \<Longrightarrow> read_file fs name \<noteq> File_Not_Found"  (* proof found by sledgehammer cvc5 and spass and e *)
  using has_file_equiv by auto

lemma read_file_succeeds_if_file_in_fs2 :
"has_file fs name \<Longrightarrow> read_file fs name \<noteq> File_Not_Found"
  by simp

lemma remove_removes : "not_in_fs (remove fs name) name"
proof (induct fs)
  case Nil
  then show ?case by auto
next
  case (Cons a fs)  (* proof found by sledgehammer cvc5 *)
  then show ?case by (metis (no_types, lifting) fst_conv list.distinct(1) list.inject not_in_fs.elims(2,3) read_file.elims remove.elims)
qed

lemma remove_nonexistent_no_change :
"not_in_fs fs name ==> remove fs name = fs"
proof (induct fs)
  case Nil
  then show ?case by simp
next
  case (Cons a fs)
  then show ?case (* proof found by sledgehammer cvc5 *)
    by (smt (z3) list.inject not_in_fs.simps read_file.simps(2) read_result.simps(3) remove.elims)
qed

lemma read_cleared_by_remove :
"read_file (remove fs name) name = File_Not_Found"
  (* proof found by sledgehammer cvc5 vampire verit spass *)
  using remove_removes by auto

lemma read_ignores_different_remove :
"name1 \<noteq> name2 \<Longrightarrow>
   read_file fs name1 = read_file (remove fs name2) name1"
proof (induct fs)
  case Nil
  then show ?case by simp
next
  case (Cons a fs)
  then show ?case  (* proof found by sledgehammer cvc5 *)
    by (smt (verit) list.distinct(1) list.inject prod.inject read_file.elims
        remove.elims)
qed

(* assume 16 bytes overhead per file, plus the bytes in the name and the bytes in the content *)
fun space_used :: "(string * nat list) list \<Rightarrow> nat" where
"space_used [] = 0" |
"space_used ((first_name, first_content) # rest) =
      length first_name + length first_content + 16 + space_used rest"

fun write_file :: "(string * nat list) list \<Rightarrow> string \<Rightarrow> nat list \<Rightarrow> nat \<Rightarrow> write_result" where
"write_file fs name content max_size =
   (if has_file fs name then Exists
    else if (space_used fs + length name + length content) \<ge> max_size then Insufficent_Space
    else Written ((name, content) # fs))"

(* older version, always removes before adding
fun write_file :: "(string * nat list) list \<Rightarrow> string \<Rightarrow> nat list \<Rightarrow> nat \<Rightarrow> write_result" where
"write_file fs name content max_size =
   (let removed_fs = remove fs name in
    (if (space_used removed_fs + length name + length content) < max_size then
       Written ((name, content) # removed_fs)
     else Insufficent_Space))"
*)

(* always returns the file system, even in case of failure *)
fun write_return_fs :: "(string * nat list) list \<Rightarrow> string \<Rightarrow> nat list \<Rightarrow> nat \<Rightarrow> (string * nat list) list" where
"write_return_fs fs name content max_size =
   (case write_file fs name content max_size of
     Written new_fs \<Rightarrow> new_fs | _ \<Rightarrow> fs)"

lemma read_returns_content_from_successful_write :
"write_file fs name content max_size = Written new_fs \<Longrightarrow>
   read_file new_fs name = Data content" (* proof found by sledgehammer cvc5 *)
  by (metis list.distinct(1) list.inject prod.inject read_file.elims write_file.simps
      write_result.inject write_result.simps(3,5))

lemma successful_write_is_at_front:
"not_in_fs fs name \<and> write_file fs name content max_size = Written new_fs ==>
  new_fs = ((name, content) # fs)" (* proof found by sledgehammer cvc5 *)
  by (metis write_file.simps write_result.inject write_result.simps(3,5))

lemma missing_file_unchanged_by_other_write :
"name1 \<noteq> name2 \<and> not_in_fs fs name1 \<and>
   write_file fs name2 content2 max_size = Written new_fs ==>
   not_in_fs new_fs name1"
proof (induct fs)
  case Nil
  then show ?case (* proof found by sledgehammer e *)
    by (metis not_in_fs.elims(3) read_file.simps(1,2) successful_write_is_at_front)
next
  case (Cons a fs)
  then show ?case (* proof found by sledgehammer vampire *)
    by (metis has_not_opposites not_in_fs.elims(1) read_file.simps(2)
        successful_write_is_at_front write_file.simps write_result.simps(5))
qed

lemma successful_read_unchanged_by_other_write :
"name1 \<noteq> name2 \<and> read_file fs name1 = Data content1 \<and>
   write_file fs name2 content2 max_size = Written new_fs ==>
   read_file new_fs name1 = Data content1" (* proof found by sledgehammer e *)
  by (metis has_file.simps not_in_fs.elims(3) read_file.simps(2)
      successful_write_is_at_front write_file.simps write_result.simps(5))

lemma read_unchanged_by_other_write :
"name1 \<noteq> name2 \<and> read_file fs name1 = result \<and>
   write_file fs name2 content2 max_size = Written new_fs \<Longrightarrow>
   read_file new_fs name1 = result" (* proof found by sledgehammer vampire *)
  by (metis has_file.elims(3) not_in_fs.simps read_file.simps(2)
      successful_write_is_at_front write_file.simps write_result.distinct(3)) 

lemma read_ignores_other_write :
"name1 \<noteq> name2 \<and> read_file fs name1 = result1 \<and>
     write_file fs name2 content max_size = Written new_fs \<Longrightarrow>
   read_file new_fs name1 = result1" (* proof found by sledgehammer multiple provers *)
  using read_unchanged_by_other_write by blast

lemma read_returns_contents_from_correct_write :
"name1 \<noteq> name2 \<and> write_file fs name1 content1 max_size = Written new_fs \<Longrightarrow>
     read_file (write_return_fs new_fs name2 content2 max_size)
                                 name1 = Data content1" (* proof found by sledgehammer cvc5 *)
  by (metis (no_types, lifting) read_ignores_other_write
      read_returns_content_from_successful_write write_file.simps write_result.simps(10,8,9)
      write_return_fs.simps)

lemma read_after_write_ignores_different_remove :
"name1 \<noteq> name2 \<and> write_file fs name1 content1 max_size = Written new_fs \<Longrightarrow>
   read_file (remove new_fs name2) name1 = Data content1" (* proof found by sledgehammer verit *)
  by (metis (no_types, lifting) Pair_inject has_not_opposites list.inject neq_Nil_conv
      read_file.elims remove.elims successful_write_is_at_front write_file.simps
      write_result.distinct(3)) 
