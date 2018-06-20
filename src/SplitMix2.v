Require Import String.
Require Import Ascii.
Require Import NArith.

(* Binary numbers. The operations assume little-endianness,
   but this can also be used as a big-endian representation. *)
Inductive binary : Type :=
| b0 : binary -> binary
| b1 : binary -> binary
| b_ : binary (* End *)
.

Fixpoint zeroes (d : nat) : binary :=
  match d with
  | O => b_
  | S d => b0 (zeroes d)
  end.

Fixpoint positive_to_binary (d : nat) (n : positive) :=
  match n, d with
  | xI n, S d => b1 (positive_to_binary d n)
  | xO n, S d => b0 (positive_to_binary d n)
  | xH, _ => b1 (zeroes d)
  | _, O => b_
  end.

Definition N_to_binary (d : nat) (n : N) :=
  match n with
  | N0 => zeroes d
  | Npos n => positive_to_binary d n
  end.

Fixpoint binary_to_N (z : binary) :=
  match z with
  | b_ => 0%N
  | b1 z => N.succ_double (binary_to_N z)
  | b0 z => N.double (binary_to_N z)
  end.
    
Example binary_from_to : (binary_to_N (N_to_binary 64 10) = 10)%N.
Proof. reflexivity. Qed.

Fixpoint length_binary (z : binary) : nat :=
  match z with
  | b0 z | b1 z => S (length_binary z)
  | b_ => O
  end.

Fixpoint rev' (y z : binary) : binary :=
  match z with
  | b0 z => rev' (b0 y) z
  | b1 z => rev' (b1 y) z
  | b_ => y
  end.

(* big-endian <-> little-endian *)
Definition rev : binary -> binary := rev' b_.

(* Bitwise xor. The second operand is
   extended/truncated to the length of the first one. *)
Fixpoint xor (z1 z2 : binary) :=
  match z1, z2 with
  | b0 z1, b0 z2 | b1 z1, b1 z2 => b0 (xor z1 z2)
  | b0 z1, b1 z2 | b1 z1, b0 z2 => b1 (xor z1 z2)
  | _, _ => z1
  end.

Lemma xor_length :
  forall z1 z2, length_binary (xor z1 z2) = length_binary z1.
Proof.
  induction z1; destruct z2; simpl; try f_equal; auto.
Qed.

Fixpoint shiftr (n : nat) (z : binary) :=
  match n, z with
  | S n, (b0 z | b1 z) => shiftr n z
  | _, _ => z
  end.

Example shiftr_test :
  shiftr 3 (N_to_binary 10 30) = (N_to_binary 7 3%N).
Proof. reflexivity. Qed.

Lemma shiftr_length :
  forall n z, length_binary (shiftr n z) = length_binary z - n.
Proof.
  induction n; destruct z; simpl; auto.
Qed.

(* [z ^ (z >>> n)]*)
Definition shift_xor z (n : nat) :=
  xor z (shiftr n z).

Inductive bit := zero | one.

Definition of_bit (a : bit) : binary -> binary :=
  match a with
  | zero => b0
  | one => b1
  end.

Definition of_bool (a : bool) : binary -> binary :=
  match a with
  | false => b0
  | true => b1
  end.

Fixpoint succ (z : binary) : binary :=
  match z with
  | b1 z => b0 (succ z)
  | _ => z
  end.

Definition succ_length :
  forall z, length_binary (succ z) = length_binary z.
Proof.
  induction z; simpl; auto.
Qed.

(* Add two numbers with carry. The result is truncated to the
   length of the first operand. *)
Fixpoint plus' (c : bit) (z1 z2 : binary) :=
  match z1, z2 with
  | b0 z1, b0 z2 => of_bit c (plus' zero z1 z2)
  | b1 z1, b0 z2 | b0 z1, b1 z2 =>
    match c with
    | zero => b1 (plus' zero z1 z2)
    | one => b0 (plus' one z1 z2)
    end
  | b1 z1, b1 z2 =>
    of_bit c (plus' one z1 z2)
  | _, _ => succ z1
  end.

Lemma plus'_length :
  forall z1 z2 c, length_binary (plus' c z1 z2) = length_binary z1.
Proof.
  induction z1; destruct z2; destruct c; simpl; auto using succ_length.
Qed.

Definition plus : binary -> binary -> binary := plus' zero.

Example plus_test :
  plus (N_to_binary 10 3) (N_to_binary 5 5) = N_to_binary 10 8.
Proof. reflexivity. Qed.

Lemma plus_length :
  forall z1 z2, length_binary (plus z1 z2) = length_binary z1.
Proof.
  intros; apply plus'_length.
Qed.

Fixpoint mul (z1 z2 : binary) :=
  match z1 with
  | b0 z1 => b0 (mul z1 z2)
  | b1 z1 => plus (b0 (mul z1 z2)) z2
  | b_ => b_
  end.

Example mul_test :
  mul (N_to_binary 10 3) (N_to_binary 5 5) = N_to_binary 10 15.
Proof. reflexivity. Qed.

Lemma mul_length :
  forall z1 z2, length_binary (mul z1 z2) = length_binary z1.
Proof.
  induction z1; intro z2; simpl; auto.
  rewrite plus_length; simpl; auto.
Qed.  

Fixpoint popcount_under (n : nat) (z : binary) : bool :=
  match z, n with
  | b1 _, O => false
  | b1 z, S n => popcount_under n z
  | b0 z, _ => popcount_under n z
  | b_, _ => true
  end.

Fixpoint hex' (acc : binary) (s : string) : binary :=
  match s with
  | EmptyString => acc
  | String x s =>
    let acc :=
        match x with
        (* Digit *)
        | Ascii a0 a1 a2 a3 _ _ false _ =>
          of_bool a0 (of_bool a1 (of_bool a2 (of_bool a3 acc)))
        | "a" => b0 (b1 (b0 (b1 acc)))
        | "b" => b1 (b1 (b0 (b1 acc)))
        | "c" => b0 (b0 (b1 (b1 acc)))
        | "d" => b1 (b0 (b1 (b1 acc)))
        | "e" => b0 (b1 (b1 (b1 acc)))
        | "f" => b1 (b1 (b1 (b1 acc)))
        | _ => b0 (b0 (b0 (b0 acc)))
        end%char in
    hex' acc s
  end.

Definition hex : string -> binary := hex' b_.

(* Compute hex "123". *)

Definition golden_gamma : binary :=
  Eval compute in hex "9e3779b97f4a7c15".

Definition c1 : binary :=
  Eval compute in hex "ff51afd7ed558ccd".
Definition c2 : binary :=
  Eval compute in hex "c4ceb9fe1a85ec53".

Definition mix64 z :=
  let z := mul c1 (shift_xor z 33) in
  let z := mul c2 (shift_xor z 33) in
  shift_xor z 33.

Definition c3 : binary :=
  Eval compute in hex "bf58476d1ce4e5b9".
Definition c4 : binary :=
  Eval compute in hex "94d049bb133111eb".

Definition mix64variant13 z :=
  let z := mul c3 (shift_xor z 30) in
  let z := mul c4 (shift_xor z 27) in
  shift_xor z 31.

Definition set_lsb z :=
  match z with
  | b0 z => b1 z
  | _ => z
  end.

Definition c5 : binary :=
  Eval compute in hex "aaaaaaaaaaaaaaaa".

Definition mix_gamma z :=
  let z := set_lsb (mix64 z) in
  if popcount_under 24 (shift_xor z 1) then
    xor z c5
  else
    z.

Definition N64 := binary.

Record State := MkState {
  seed : N64;
  gamma : N64;
  counter : N64; (* big-endian *)
  remaining : nat;
}.

Definition split '(MkState s0 g c r) : State * State :=
  match r with
  | S r =>
    let new bx := MkState s0 g (bx c) r in
    (new b0, new b1)
  | O =>
    (* [b0 c = 2 * c], SplitMix's splitting increments the
       counter by 2. *)
    let s1 := plus s0 (mul g (b0 (rev c))) in
    let s2 := plus s1 g in
    let s' := mix64variant13 s1 in
    let g' := mix_gamma s2 in
    let new bx := MkState s' g' (bx b_) 63 in
    (new b0, new b1)
  end.

(* Probably overkill if you just need a few bits. *)
Definition to_binary '(MkState s0 g c r) : binary :=
  let s1 := plus s0 (mul g (b0 (rev c))) in
  mix64variant13 s1.

Definition of_seed n : State :=
  {| seed := N_to_binary 64 n;
     gamma := golden_gamma;
     counter := b_;
     remaining := 64 |}.

Section Ex.

Import NArith.

Fixpoint split_many2 (n : nat) g :=
  match n with
  | O => g
  | S n' => let (_, g) := split g in split_many2 n' g
  end.

End Ex.
