(* authors: Edoardo Biagioni and Nicholas Cheng, 2026.
   Nicholas Cheng did all the challenging proofs. *)

(* saplist.thy stores and retrieves lists of blocks, each of
   which hold data for one file in the simple-as-possible (SAP)
   file system.

   The first block of a file starts with the number of bytes
   in the file.  This number is stored in binary, one bit
   per byte (that is, each byte is CHR 0x00 or CHR 0x01).
   These bits are preceded by a single byte that records
   the length of the number in bits.  Since the maximum
   value of this byte is 255, the maximum length of a file
   is (2^255)-1 bytes

   Functions read_blocks and write_blocks read and write blocks
   starting at a given block number (block index).  On a real
   device all blocks need to be the one size that is supported
   by the device and file system.  saplist does not enforce block
   sizes, just reads and writes what it is given, so any callers
   are responsible for writing blocks of the correct size.

   Theorem read_blocks_after_write_same proves that reading
   a list of blocks after writing a list of blocks returns
   the same list of blocks.

   Theorem read_stored_num_same proves that storing a number
   as a sequence of 0 or 1 bits, each stored in its own byte,
   then reading it back, gives the same number as long as
   the number has no more than 255 bits.

   Theorems read_stored_num_same_even_with_file_data and
   alternate_read_stored_num_same_even_with_file_data show that
   the number is read back correctly even if the bytes storing the
   length are followed by other arbitrary file data.
 *)

theory saplist
  imports Main dev
begin

fun read_blocks :: "dev \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> data_block list" where
"read_blocks dev bn 0 = []" |
"read_blocks dev bn (Suc nb) =
  (dev bn) # read_blocks dev (Suc bn) nb"

(* just for the exercise, this may not be used anywhere *)
lemma read_blocks_length_nb :
"length (read_blocks dev bn nb) = nb"
proof (induct nb arbitrary: bn)
  case 0
  then show ?case by simp
next
  case (Suc nb)
  then show ?case by simp
qed

fun write_blocks :: "dev \<Rightarrow> nat \<Rightarrow> data_block list \<Rightarrow> dev" where
"write_blocks dev bn [] = dev" |
"write_blocks dev bn (block # blocks) =
  write_block (write_blocks dev (Suc bn) blocks) bn block"

lemma read_write_single_block_same :
"read_blocks (write_blocks dev bn [block]) bn 1 = [block]"
  apply(auto)
(* only some versions of Isabelle need the next line, if so uncomment it. *)
  (* apply(simp add: write_block_def) *)
  done

lemma read_write_two_blocks_same :
"read_blocks (write_blocks dev bn [b1, b2]) bn 2 = [b1, b2]"
  apply(auto)
  apply(simp add: write_block_def)
  by (simp add: numeral_2_eq_2)

lemma read_blocks_in_write_block :
"i < bn \<Longrightarrow> read_blocks (write_block dev i block) bn nb = read_blocks dev bn nb"
  apply(induct nb arbitrary: bn)
   apply(simp_all add: write_block_def)
  done

theorem read_blocks_after_write_same :
  "read_blocks (write_blocks dev bn blocks) bn (length blocks) = blocks"
  apply(induct blocks arbitrary:bn)
  using read_write_single_block_same read_blocks_in_write_block
   apply(simp_all)
  done

(* number encoded in binary, one bit per byte, that
   is, each byte holds either CHR 0x00 or CHR 0x01.
   The encoding is little-endian, that is,
   the most significant bit is at the end of the list.
   The number is always encoded in normal form, in this
   case meaning that for all numbers except zero,
   the most significant bit (last bit) is always a 1.
   Zero is represented by the empty list. *)
fun sap_encode_nat :: "nat \<Rightarrow> nat list" where
"sap_encode_nat 0 = []" |
"sap_encode_nat (Suc n) =
  ((Suc n) mod 2) # sap_encode_nat ((Suc n) div 2)"

definition sap_decode_nat :: "nat list \<Rightarrow> nat" where
"sap_decode_nat lst = horner_sum id 2 lst"
(* some of the following are not in normal form *)
value "map sap_decode_nat [[], [0], [1], [1, 0], [0, 1], [0, 1, 1]]"

fun rec_sap_decode_nat :: "nat list \<Rightarrow> nat" where
"rec_sap_decode_nat [] = 0" |
"rec_sap_decode_nat (first # rest) =
  first + 2 * rec_sap_decode_nat rest"

lemma rec_def_decode_same : "rec_sap_decode_nat n = sap_decode_nat n"
  apply(induct n) by (simp_all add: sap_decode_nat_def)

lemma deencode_same : "sap_decode_nat (sap_encode_nat n) = n"
  apply(induct n rule:sap_encode_nat.induct)
  apply(simp_all add: sap_decode_nat_def)
  done

lemma endecode_same : "sap_encode_nat n = ns \<Longrightarrow> sap_decode_nat ns = n"
  using deencode_same by auto

lemma rec_deencode_same : "rec_sap_decode_nat (sap_encode_nat n) = n"
  using rec_def_decode_same endecode_same by auto

lemma rec_endecode_same : "sap_encode_nat n = ns \<Longrightarrow> rec_sap_decode_nat ns = n"
  using rec_def_decode_same endecode_same by auto

(* store_num_as_list is broken into sub-functions, hoping this
   makes it easier to prove properties about store_num_as_list *)
definition prepend_length :: "nat list \<Rightarrow> nat list" where
"prepend_length lst = (length lst) # lst"

definition num_as_nat_list :: "nat \<Rightarrow> nat list" where
"num_as_nat_list n = prepend_length (sap_encode_nat n)"

definition store_num_as_list :: "nat \<Rightarrow> data_block" where
"store_num_as_list n = map char_of (num_as_nat_list n)"

(* the reverse of store_num_as_list *)
definition read_num_from_list :: "data_block \<Rightarrow> nat" where
"read_num_from_list chars =
  (case (map (of_char::char \<Rightarrow> nat) chars) of
      Nil \<Rightarrow> 0
   | len # digits \<Rightarrow>
      sap_decode_nat (take len digits))"

(* a read_num_from_list that doesn't use case of.
   since sap_decode_nat Nil returns 0 anyways, the case might not be needed *)
definition caseless_read_num_from_nat_list :: "nat list \<Rightarrow> nat" where
"caseless_read_num_from_nat_list (xs) = sap_decode_nat (take (hd xs) (tl xs))"

value "map caseless_read_num_from_nat_list [[0], [1, 1], [2, 0, 1], [2, 1, 1], [3, 0, 0, 1]]"

definition caseless_read_num_from_list :: "data_block \<Rightarrow> nat" where
"caseless_read_num_from_list (xs) =
  caseless_read_num_from_nat_list (map of_char xs)"

(* caseless_read_num_from_list and its helper function but condensed into one *)
definition caseless_read_num_from_list_condensed :: "data_block \<Rightarrow> nat" where
"caseless_read_num_from_list_condensed (xs) =
  sap_decode_nat (take (of_char (hd xs)) (map of_char (tl xs)))"

(* proving the 2 caseless definitions are the same *)
lemma both_casesless_defs_same : "caseless_read_num_from_list ns = caseless_read_num_from_list_condensed ns"
  apply(simp add: caseless_read_num_from_list_def caseless_read_num_from_nat_list_def
      caseless_read_num_from_list_condensed_def)
  apply(induct ns)
  by auto

(* proving the definition that uses cases is also the same *)
lemma read_num_from_list_case_caseless_same : "read_num_from_list ns = caseless_read_num_from_list ns"
  apply(induct ns)
   apply(simp_all add: read_num_from_list_def caseless_read_num_from_nat_list_def
      sap_decode_nat_def caseless_read_num_from_list_def)
  done

(* these lemmas are useful for converting the definitions into the caseless condensed def *)

value "map store_num_as_list [0, 1, 2, 3, 4, 5, 6, 7, 12, 64, 99]"
value "map (\<lambda> n . read_num_from_list (store_num_as_list n)) [0, 1, 2, 3, 4, 5, 6, 7, 12, 64, 99]"
value "map read_num_from_list [[], map (char_of::nat \<Rightarrow> char) [3, 0, 1, 1]]"

(* proofs for some of the functions that store_num_as_list uses *)
lemma prepend_length_works : "prepend_length ns = x#xs \<Longrightarrow> length ns = x"
  apply(simp add: prepend_length_def)
  by auto

lemma prepend_length_ns_unchanged : "prepend_length ns = x#xs \<Longrightarrow> ns = xs"
  apply (simp add: prepend_length_def)
  done

lemma take_prepend_length : "prepend_length ns = x#xs \<Longrightarrow> take x xs = xs"
  apply(simp add: prepend_length_def)
  by auto

lemma decode_num_as_nat_list : "num_as_nat_list n = x#xs \<Longrightarrow> sap_decode_nat xs = n"
  apply(simp add: num_as_nat_list_def prepend_length_def endecode_same)
  done

lemma store_num_as_list_length_nonzero :
 "length(store_num_as_list n) > 0"
  apply(simp add: store_num_as_list_def)
  by (simp add: num_as_nat_list_def prepend_length_def)

lemma of_char_of_nat : "(n::nat) < 256 \<Longrightarrow> of_char (char_of n) = n"
  by simp

lemma of_char_of_nat_equiv : "(n::nat) < 256 \<equiv> of_char (char_of n) = n"
  by (smt (verit) nat_of_char_less_256 of_char_of_nat)

lemma of_char_of_nat_byte_value : "of_char (char_of (n::nat)) = n \<equiv> n < 256"
  using of_char_of_nat_equiv by presburger

lemma of_char_of_nat_byte_value_partial : "of_char (char_of (n::nat)) = n \<Longrightarrow> n < 256"
  by (metis nat_of_char_less_256)

(* needed when simplifying with definitions *)
lemma of_char_of_simplify : "map (of_char \<circ> char_of) (sap_encode_nat x) = sap_encode_nat x"
  apply(induct x rule:sap_encode_nat.induct)
  by auto

(* basically read_stored_num_same but with a precondition and the caseless condensed version *)
lemma caseless_read_stored_num_same_condensed :
  "length (sap_encode_nat n) < 256 \<Longrightarrow>
     caseless_read_num_from_list_condensed (store_num_as_list n) = n"
  apply(simp_all add: caseless_read_num_from_list_condensed_def
                      store_num_as_list_def num_as_nat_list_def
                      prepend_length_def of_char_of_simplify deencode_same)
  done

(* needs the precondition/stipulation because the length of a number
   of 256 or more bits cannot be stored in a byte *)
theorem read_stored_num_same :
  "length (sap_encode_nat n) < 256 \<Longrightarrow> read_num_from_list (store_num_as_list n) = n"
  apply (simp add: read_num_from_list_case_caseless_same
                   both_casesless_defs_same
                   caseless_read_stored_num_same_condensed)
  done
(* also seems to get proven with the same "simp add:" line from the caseless lemma 
  with the caseless...condensed def swapped with the regular def *)

(* the number read back should be the same even when the encoded
   number is prepended to the first part of the file. *)
theorem read_stored_num_same_even_with_file_data :
"length (sap_encode_nat n) < 256 \<Longrightarrow>
  read_num_from_list ((store_num_as_list n) @ file_data) = n"
(* proof basically obtained by adding all of the actively used definitions *)
  apply(simp add: read_num_from_list_def
                      store_num_as_list_def num_as_nat_list_def
                      prepend_length_def of_char_of_simplify deencode_same)
  done

(* another read_stored_num_same_even_with_file_data,
   uses a different precondition *)
theorem alternate_read_stored_num_same_even_with_file_data :
"read_num_from_list (store_num_as_list n) = n \<Longrightarrow>
  read_num_from_list ((store_num_as_list n) @ file_data) = n"
(* proof basically obtained by adding all of the actively used definitions *)
  apply(simp add: read_num_from_list_def
                  store_num_as_list_def num_as_nat_list_def
                  prepend_length_def)
  done

end
