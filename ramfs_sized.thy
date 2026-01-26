theory ramfs_sized
  imports Main
begin

(* the name of a file is a string, the contents are a list of numbers \<ge> 0 *)
(* to do: would it be possible to have the contents be a byte list?
 * I think the Isabelle char would work, then a file system would
 * be a (string * string) list *)

datatype read_result = Data "nat list" | File_Not_Found
datatype write_result = Written "(string * nat list) list"
                      | Insufficent_Space
                      | Exists

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
fun read_file :: "(string * nat list) list \<Rightarrow> string \<Rightarrow>
                  read_result" where
"read_file [] name = File_Not_Found" |      (* file not found *)
"read_file ((first_name, first_data) # rest) name =
  (if name = first_name then Data first_data
   else read_file rest name)"

(* if name occurs more than once, removes only the first matching file
   normally names are unique, so this is the correct remove method. *)
fun remove_once :: "(string * nat list) list \<Rightarrow> string \<Rightarrow>
                   (string * nat list) list" where
"remove_once [] name = []" |
"remove_once ((first_name, first_content) # rest) name =
  (if name = first_name then rest
   else (first_name, first_content) # (remove_once rest name))"

(* if name occurs more than once, removes all of the matching files
 * any file system created only as a result of write_file and remove
 * does not have duplicates, so remove_all is not used:
fun remove_all :: "(string * nat list) list \<Rightarrow> string \<Rightarrow>
                   (string * nat list) list" where
"remove_all [] name = []" |
"remove_all ((first_name, first_content) # rest) name =
  (if name = first_name then remove_all rest name
   else (first_name, first_content) # (remove_all rest name))"
*)

fun has_file :: "(string * nat list) list \<Rightarrow> string \<Rightarrow>
                 bool" where 
"has_file fs name = ((read_file fs name) \<noteq> File_Not_Found)"

fun not_in_fs :: "(string * nat list) list \<Rightarrow> string \<Rightarrow>
                  bool" where 
"not_in_fs fs name = ((read_file fs name) = File_Not_Found)"

(* has_file and not_in_fs are opposites *)
lemma has_not_opposites [simp]:
"has_file fs name = (\<not> not_in_fs fs name)"
  by simp

fun has_file2 :: "(string * nat list) list \<Rightarrow> string \<Rightarrow>
                  bool" where 
"has_file2 fs name = member (names fs) name"

(* has_file and has_file2 are equivalent *)
lemma has_file_equiv [simp]:
"has_file fs name = has_file2 fs name"
proof (induct fs)
  case Nil
  then show ?case by auto
next
  case (Cons a fs)
  then show ?case
    by (smt (verit) has_file.simps has_file2.elims(1) list.distinct(1)
        list.inject member.elims(1) names.elims prod.inject read_file.elims
        read_result.simps(3))
qed

lemma has_file_correct [simp] :
"(if has_file fs name then name \<in> set (names fs)
  else name \<notin> set (names fs))"
proof (induct fs)
  case Nil
  then show ?case by simp
next
  case (Cons a list)
  then show ?case  (* proof found by sledghammer e *)
    by (metis has_file2.elims(1) has_file_equiv insert_iff
        list.simps(15) names.simps(2) old.prod.exhaust
        ramfs_sized.member.simps(2))
qed

lemma read_file_succeeds_if_file_in_fs :
"member (names fs) name \<Longrightarrow>
  read_file fs name \<noteq> File_Not_Found"
  (* proof found by sledgehammer cvc5 and spass and e *)
  using has_file_equiv by auto

lemma read_file_succeeds_if_file_in_fs2 :
"has_file fs name \<Longrightarrow> read_file fs name \<noteq> File_Not_Found"
  by simp

lemma remove_once_removes_if_distinct :
"distinct (names fs) \<Longrightarrow>
   not_in_fs (remove_once fs name) name"
proof (induct fs)
  case Nil
  then show ?case by simp
next
  case (Cons a fs)
  then show ?case
    (* proof found by sledgehammer cvc5 *)
    by (smt (verit) distinct.simps(2) has_file.elims(3)
        has_file_correct list.distinct(1)
        list.inject names.elims not_in_fs.simps prod.inject read_file.elims
        remove_once.elims)
qed

fun num_names :: "(string * nat list) list \<Rightarrow> string \<Rightarrow> nat" where
"num_names [] name = 0" |
"num_names ((first_name, first_content) # rest) name =
  (if first_name = name then 1 else 0) + num_names rest name"

lemma remove_once_has_one_less :
"has_file fs name \<Longrightarrow> num_names fs name = 1 + num_names (remove_once fs name) name"
proof (induct fs)
  case Nil
  then show ?case by simp
next
  case (Cons a fs)
  then show ?case (* proof found by sledgehammer cvc5 *)
    by (smt (verit) add_0 has_file.simps list.distinct(1)
        list.inject num_names.elims
        prod.inject read_file.simps(2) remove_once.elims)
qed

lemma remove_once_removes_distinct :
"distinct (names fs) \<Longrightarrow> not_in_fs (remove_once fs name) name"
proof (induct fs)
  case Nil
  then show ?case by auto
next
  case (Cons a fs)
  then show ?case  (* proof found by sledgehammer cvc5 *)
    by (smt (verit) distinct.simps(2) has_file.simps has_file_correct
        list.distinct(1) list.inject names.elims not_in_fs.simps
        prod.inject read_file.elims remove_once.elims) 
qed

lemma remove_once_nonexistent_no_change :
"not_in_fs fs name ==> remove_once fs name = fs"
proof (induct fs)
  case Nil
  then show ?case by simp
next
  case (Cons a fs)
  then show ?case  (* proof found by sledgehammer cvc5 *)
    by (smt (verit) list.inject not_in_fs.simps read_file.simps(2)
        read_result.simps(3) remove_once.elims)
qed

lemma read_cleared_by_remove_once :
"distinct (names fs) \<Longrightarrow> read_file (remove_once fs name) name = File_Not_Found"
  using remove_once_removes_distinct by auto

lemma read_ignores_different_remove_once :
"name1 \<noteq> name2 \<and> distinct (names fs) \<Longrightarrow>
   read_file fs name1 = read_file (remove_once fs name2) name1"
proof (induct fs)
  case Nil
  then show ?case by simp
next
  case (Cons a fs)
  then show ?case  (* proof found by sledgehammer cvc5 *)
    by (smt (verit) distinct_length_2_or_more list.distinct(1) list.inject
        names.elims prod.inject read_file.elims remove_once.elims)
qed

(* assume 17 bytes overhead per file, plus the bytes in the name
   and the bytes in the content.  17 bytes assuming a 16-byte header
   and one byte to null-terminate the name *)
fun space_used :: "(string * nat list) list \<Rightarrow> nat" where
"space_used [] = 0" |
"space_used ((first_name, first_content) # rest) =
      length first_name + length first_content + 17 + space_used rest"

fun write_file :: "(string * nat list) list \<Rightarrow> string \<Rightarrow> nat list \<Rightarrow> nat \<Rightarrow> write_result" where
"write_file fs name content max_size =
   (if has_file fs name then Exists
    else if (space_used fs + length name + length content) \<ge> max_size then Insufficent_Space
    else Written ((name, content) # fs))"

(* older version, always removes before adding and so guarantees (rather
 * than just preserves) file name uniqueness
fun write_file :: "(string * nat list) list \<Rightarrow> string \<Rightarrow> nat list \<Rightarrow> nat \<Rightarrow> write_result" where
"write_file fs name content max_size =
   (let removed_fs = remove fs name in
    (if (space_used removed_fs + length name + length content) < max_size then
       Written ((name, content) # removed_fs)
     else Insufficent_Space))"
*)

(* always returns the file system.  If unable to write, returns the old fs *)
fun write_return_fs :: "(string * nat list) list \<Rightarrow> string \<Rightarrow> nat list \<Rightarrow> nat \<Rightarrow> (string * nat list) list" where
"write_return_fs fs name content max_size =
   (case write_file fs name content max_size of
     Written new_fs \<Rightarrow> new_fs | _ \<Rightarrow> fs)"

(* ============ prove relationships between reads and writes: =========== *)

lemma read_returns_content_from_successful_write :
"write_file fs name content max_size = Written new_fs \<Longrightarrow>
   read_file new_fs name = Data content" (* proof found by sledgehammer cvc5 *)
  by (metis list.distinct(1) list.inject prod.inject
      read_file.elims write_file.simps
      write_result.inject write_result.simps(3,5))

lemma missing_file_unchanged_by_other_write :
"name1 \<noteq> name2 \<and> not_in_fs fs name1 ==>
   not_in_fs (write_return_fs fs name2 content2 max_size) name1" by simp

(* not needed:
lemma successful_read_unchanged_by_other_write :
"name1 \<noteq> name2 \<and> read_file fs name1 = Data content1 \<and>
   write_file fs name2 content2 max_size = Written new_fs ==>
   read_file new_fs name1 = Data content1" (* proof found by sledgehammer e *)
  by (metis has_file.simps not_in_fs.elims(3) read_file.simps(2)
      successful_write_is_at_front write_file.simps write_result.simps(5))
*)

(* if a file exists, no write will change it *)
lemma successful_read_unchanged_by_write:
"read_file fs name1 = Data content1 \<and>
   write_return_fs fs name2 content2 max_size = maybe_new_fs \<Longrightarrow>
   read_file maybe_new_fs name1 = Data content1" by auto

lemma unsuccessful_read_unchanged_by_other_write:
"name1 \<noteq> name2 \<and> read_file fs name1 = File_Not_Found \<Longrightarrow>
   read_file (write_return_fs fs name2 content2 max_size) name1 = File_Not_Found" by auto

(* same lemma, slightly different formulation
lemma unsuccessful_read_unchanged_by_other_write:
"name1 \<noteq> name2 \<and> read_file fs name1 = File_Not_Found \<and>
   write_return_fs fs name2 content2 max_size = maybe_new_fs \<Longrightarrow>
   read_file maybe_new_fs name1 = File_Not_Found" by auto
*)

(* if a file exists, write to a different name will not change it, as implied
 * by successful_read_unchanged_by_write.
 * If it does not exist, write to a different name will not create it *)
lemma read_unchanged_by_other_write :
"name1 \<noteq> name2 \<and> read_file fs name1 = result \<and>
   write_file fs name2 content2 max_size = Written new_fs \<Longrightarrow>
   read_file new_fs name1 = result"
   (* proof found by sledgehammer cvc5, different proof by spass *)
  by (metis list.distinct(1) list.inject prod.inject
      read_file.elims write_file.simps
      write_result.inject write_result.simps(3,5))

(* once we've written a file, a subsequent write will not change it
 * pretty obvious from the preceding lemmas, and the sledghammer proof
 * reflects this.  Found by sledgehammer cvc5, vampire, spass, and e *)
lemma read_returns_contents_from_correct_write :
"name1 \<noteq> name2 \<and> write_file fs name1 content1 max_size = Written new_fs \<Longrightarrow>
     read_file (write_return_fs new_fs name2 content2 max_size)
                                 name1 = Data content1"
  using read_returns_content_from_successful_write successful_read_unchanged_by_write
  by blast

lemma read_after_write_ignores_different_remove_once :
"name1 \<noteq> name2 \<and> write_file fs name1 content1 max_size = Written new_fs \<Longrightarrow>
 read_file (remove_once new_fs name2) name1 = Data content1"
  (* proof found by sledgehammer cvc5 *)
  by (metis (no_types, lifting) list.distinct(1) list.inject prod.inject read_file.elims
      remove_once.elims write_file.simps write_result.inject write_result.simps(3,5))


lemma read_after_write_ignores_subsequent_write :
"write_file fs name content max_size = Written new_fs \<Longrightarrow>
  read_file (write_return_fs new_fs any_name any_content max_size) name = Data content"
(* proof found by sledgehammer cvc5, similar proof by vampire *)
  using read_returns_content_from_successful_write successful_read_unchanged_by_write
  by blast

(* ========= prove that write and remove preserve unique file names: ======== *)

theorem write_preserves_distinct [simp] :
"distinct (names fs) \<Longrightarrow> distinct (names (write_return_fs fs name content max_size))"
  by simp

theorem remove_preserves_distinct [simp] :
"distinct (names fs) \<Longrightarrow> distinct (names (remove_once fs name))"
proof (induct fs)
  case Nil
  then show ?case by simp
next
  case (Cons a fs)
  then show ?case  (* proof by sledgehammer cvc5 *)
    by (smt (verit) Pair_inject distinct.simps(2) has_file.simps has_file_correct
        list.distinct(1) list.inject names.elims read_ignores_different_remove_once
        remove_once.elims)
qed

(* ============ prove effects of arbitrary writes or removes: =========== *)

(* the operations that may change the file system are write and remove *)
datatype Op = Write "(string * nat list)" | Remove string

(* can do arbitrary write or remove, except not remove name *)
(* to distinguish from single_op, below, we refer to this as opr *)
fun single_op_except_remove :: "(string * nat list) list \<Rightarrow>
                                Op \<Rightarrow> string \<Rightarrow> nat
                                \<Rightarrow> (string * nat list) list" where
"single_op_except_remove fs (Write (name, content)) avoid_removing max_size =
    write_return_fs fs name content max_size" |
"single_op_except_remove fs (Remove name) avoid_removing max_size =
    (if name = avoid_removing then fs else (remove_once fs name))"

(* can do arbitrary write or remove, except not on name
   so if a name is not in the fs, we don't create it *)
fun single_op :: "(string * nat list) list \<Rightarrow> Op \<Rightarrow> string \<Rightarrow> nat
                    \<Rightarrow> (string * nat list) list" where
"single_op fs (Write (name, content)) avoid_name max_size =
    (if name = avoid_name then fs else write_return_fs fs name content max_size)" |
"single_op fs (Remove name) avoid_name max_size =
    (if name = avoid_name then fs else (remove_once fs name))"

(* some assertions are valid even without staying away from a name
   op_no_exception is abbreviated opn when used below *)
fun single_op_no_exception :: "(string * nat list) list \<Rightarrow> Op \<Rightarrow> nat
                                   \<Rightarrow> (string * nat list) list" where
"single_op_no_exception fs (Write (name, content)) max_size =
    write_return_fs fs name content max_size" |
"single_op_no_exception fs (Remove name) max_size =
    remove_once fs name"

lemma single_opr_preserves_distinct :
"distinct (names fs) \<Longrightarrow> distinct (names (single_op_except_remove fs op name max_size))"
  (* proof found by sledgehammer cvc5, alternative by e *)
  by (metis remove_preserves_distinct single_op_except_remove.elims
      write_preserves_distinct)

lemma single_op_preserves_distinct :
"distinct (names fs) \<Longrightarrow> distinct (names (single_op fs op name max_size))"
  (* proof found by sledgehammer cvc5 *)
  by (metis remove_preserves_distinct single_op.elims write_preserves_distinct)

lemma single_opn_preserves_distinct :
"distinct (names fs) \<Longrightarrow> distinct (names (single_op_no_exception fs op max_size))"
  (* proof found by sledgehammer cvc5, other proofs also by cvc5 and by zipperposition *)
  by (metis remove_preserves_distinct single_op_no_exception.elims
      write_preserves_distinct)

(* as long as we don't remove name,
   successful read always returns the same value *)
lemma single_opr_preserves_successful_read :
"distinct (names fs) \<and> read_file fs name = Data content \<Longrightarrow>
 read_file (single_op_except_remove fs op name max_size) name = Data content"
  (* proof found by sledgehammer zipperposition
     (also by cvc5, with a more complicated proof) *)
  by (metis Op.exhaust old.prod.exhaust read_ignores_different_remove_once
      single_op_except_remove.simps(1,2) successful_read_unchanged_by_write) 

(* this is a weaker statement: as long as we don't write or remove name,
   successful read always returns the same value
   also apparently much harder to prove! *)
lemma single_op_preserves_successful_read :
"distinct (names fs) \<and> read_file fs name = Data content \<Longrightarrow>
 read_file (single_op fs op name max_size) name = Data content"
  using single_opr_preserves_successful_read
  (* proof found by sledgehammer cvc5 *)
  by (smt read_ignores_different_remove_once single_op.elims
      successful_read_unchanged_by_write) 

(* as long as we don't write or remove name,
   unsuccessful read always returns the same value *)
lemma single_op_preserves_unsuccessful_read :
"distinct (names fs) \<and> read_file fs name = File_Not_Found \<Longrightarrow>
 read_file (single_op fs op name max_size) name = File_Not_Found"
  (* proof found by sledgehammer cvc5 *)
  by (metis missing_file_unchanged_by_other_write not_in_fs.elims(1)
      read_ignores_different_remove_once single_op.elims)

lemma single_op_preserves_read :
"distinct (names fs) \<Longrightarrow>
  read_file (single_op fs op name max_size) name = read_file fs name"
  (* proof found by sledgehammer cvc5 had smt (verit), which failed
     removing (verit) now works.  Very strange *)
  by (smt read_ignores_different_remove_once read_result.exhaust single_op.elims
      successful_read_unchanged_by_write
      single_op_preserves_unsuccessful_read)

(* ========== reads are preserved even after multiple arbitrary writes and removes: ========== *)
(* assertion holds as long as we don't remove that specific file name,
   and if the file did not exist, also don't write to that name.  So these
   multiple operations (op and opr, not opn) take that name as parameter *)
fun multiple_opn :: "Op list \<Rightarrow> (string * nat list) list \<Rightarrow> nat
                          \<Rightarrow> (string * nat list) list" where
"multiple_opn [] fs _ = fs" |
"multiple_opn (first # rest) fs max_size =
   single_op_no_exception (multiple_opn rest fs max_size)
                           first max_size"

fun multiple_op :: "Op list \<Rightarrow> (string * nat list) list \<Rightarrow> string \<Rightarrow> nat
                          \<Rightarrow> (string * nat list) list" where
"multiple_op [] fs _ _ = fs" |
"multiple_op (first # rest) fs except max_size =
   single_op (multiple_op rest fs except max_size)
              first except max_size"

fun multiple_opr :: "Op list \<Rightarrow> (string * nat list) list \<Rightarrow> string \<Rightarrow> nat
                          \<Rightarrow> (string * nat list) list" where
"multiple_opr [] fs _ _ = fs" |
"multiple_opr (first # rest) fs except max_size =
   single_op_except_remove (multiple_opr rest fs except max_size)
                            first except max_size"

(* the proofs of these assertions only work if the names
   in the file system are unique/distinct, so start by proving
   that all these multiple operations preserve uniqueness *)

lemma multiple_opn_preserves_distinct :
"distinct (names fs) \<Longrightarrow> distinct (names (multiple_opn ops fs max_size))"
proof (induct ops)
  case Nil
  then show ?case by simp
next
  case (Cons a ops)
  then show ?case
    by (metis list.inject multiple_opn.elims single_opn_preserves_distinct)
qed

lemma multiple_op_preserves_distinct :
"distinct (names fs) \<Longrightarrow> distinct (names (multiple_op ops fs name max_size))"
proof (induct ops)
  case Nil
  then show ?case by simp
next
  case (Cons a ops)
  then show ?case  (* found by sledgehammer cvc5, vampire, verit, e *)
    by (simp add: single_op_preserves_distinct)
qed

lemma multiple_opr_preserves_distinct :
"distinct (names fs) \<Longrightarrow> distinct (names (multiple_opr ops fs name max_size))"
proof (induct ops)
  case Nil
  then show ?case by simp
next
  case (Cons a ops)
  then show ?case  (* found by sledgehammer cvc5, vampire, verit, e *)
    by (simp add: single_opr_preserves_distinct)
qed

(* these *_creates_distinct proven by sledgehammer spass verit vampire cvc5 *)
lemma multiple_opn_creates_distinct :
"distinct (names (multiple_opn ops Nil max_size))"
  by (simp add: multiple_opn_preserves_distinct)  
lemma multiple_op_creates_distinct :
"distinct (names (multiple_op ops Nil name max_size))"
  by (simp add: multiple_op_preserves_distinct)
lemma multiple_opr_creates_distinct :
"distinct (names (multiple_opr ops Nil name max_size))"
  by (simp add: multiple_opr_preserves_distinct)

theorem multiple_opr_preserves_successful_read :
"distinct (names fs) \<and> read_file fs name = Data content \<Longrightarrow>
 read_file (multiple_opr ops fs name max_size) name = Data content"
proof (induct ops)
  case Nil
  then show ?case by simp
next
  case (Cons a ops)
  then show ?case (* proof found by sledgehammer cvc5 vampire verit *)
    by (simp add: multiple_opr_preserves_distinct
                  single_opr_preserves_successful_read) 
qed

theorem multiple_op_preserves_read :
"distinct (names fs) \<Longrightarrow>
 read_file (multiple_op ops fs name max_size) name = read_file fs name"
proof (induct ops)
  case Nil
  then show ?case by simp
next
  case (Cons a ops)
  then show ?case  (*third "using" found by sledgehammer cvc5 verit vampire *)
    using single_op_preserves_read
    using multiple_op_preserves_distinct by simp
qed

theorem multiple_op_name_not_created :
"distinct (names fs) \<and> not_in_fs fs name \<Longrightarrow>
 not_in_fs (multiple_op ops fs name max_size) name"
proof (induct ops)
  case Nil
  then show ?case by simp
next
  case (Cons a ops)
  then show ?case  (* this proof by sledgehammer spass,
                      similar proofs by verit vampire cvc5 *)
    by (metis multiple_op_preserves_read not_in_fs.simps) 
qed

lemma multiple_opr_preserves_file :
"distinct (names fs) \<and> has_file fs name \<Longrightarrow>
 has_file (multiple_opr ops fs name max_size) name"
proof (induct ops)
  case Nil
  then show ?case by simp
next
  case (Cons a ops)
  then show ?case  (* proof found by sledgehammer vampire *)
    by (metis has_file.simps multiple_opr_preserves_successful_read
        read_result.exhaust)
(* alternative found by zipperposition
    by (metis has_file.elims(3) multiple_opr_preserves_successful_read
    read_file_succeeds_if_file_in_fs2 read_result.exhaust)
*)
qed

end
