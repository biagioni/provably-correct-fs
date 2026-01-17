theory ramfs_unlimited
  imports Main
begin

(* the name of a file is a string, the contents are a list of numbers \<ge> 0 *)
(* to do: would it be possible to have the contents be a byte list? *)

datatype read_result = Data "nat list" | Not_Found

fun names :: "(string * nat list) list \<Rightarrow> string list" where
"names [] = []" |
"names ((first_name, first_data) # rest) = (first_name # (names rest))"

fun member :: "string list \<Rightarrow> string \<Rightarrow> bool" where
"member [] name = False" |
"member (first # rest) name = ((first = name) \<or> (member rest name))"

(* read_file returns Not_Found if the file is not found. *)
fun read_file :: "(string * nat list) list \<Rightarrow> string \<Rightarrow> read_result" where
"read_file [] name = Not_Found" |      (* file not found *)
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
"has_file fs name = ((read_file fs name) \<noteq> Not_Found)"

fun not_in_fs :: "(string * nat list) list \<Rightarrow> string \<Rightarrow> bool" where 
"not_in_fs fs name = ((read_file fs name) = Not_Found)"

lemma remove_removes [simp]: "not_in_fs (remove fs name) name"
proof (induct fs)
  case Nil
  then show ?case by auto
next
  case (Cons a fs)  (* proof found by sledgehammer cvc5 *)
  then show ?case by (metis (no_types, lifting) fst_conv list.distinct(1) list.inject not_in_fs.elims(2,3) read_file.elims remove.elims)
qed

fun write_file :: "(string * nat list) list \<Rightarrow> string \<Rightarrow> nat list \<Rightarrow> (string * nat list) list" where
"write_file fs name content = (name, content) # (remove fs name)"

lemma read_returns_contents_from_write [simp]:
"read_file (write_file fs name content) name = Data content"
  by auto

lemma read_returns_contents_from_correct_write [simp]:
"name1 \<noteq> name2 \<Longrightarrow> read_file (write_file (write_file fs name2 content2) name1 content1) name1 = Data content1"
  by auto

lemma read_ignores_different_remove [simp]:
"name1 \<noteq> name2 \<Longrightarrow> read_file (remove (write_file fs name1 content1) name2) name1 = Data content1"
  by auto

