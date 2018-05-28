Require Import List.

Require Import NArith.
Require ZArith.

Import ListNotations.
Open Scope bool_scope.
Open Scope N_scope.

Fixpoint truncate_pos (n : nat) (xs : positive) : N :=
  match n, xs with
  | O, _ => 0
  | S _, xH => Npos xH
  | S n', xI xs' => Pos.Nsucc_double (truncate_pos n' xs')
  | S n', xO xs' => Pos.Ndouble (truncate_pos n' xs')
  end.

Definition truncate (n : nat) (xs : N) : N :=
  match xs with
  | N0 => 0
  | Npos xs' => truncate_pos n xs'
  end.

Fixpoint shiftl_pos (n : nat) (ys : positive) : positive :=
  match n with
  | O => ys
  | S n' => xO (shiftl_pos n' ys)
  end.

Fixpoint catbit_pos (n : nat) (xs : positive) (ys : positive) :
  positive :=
  match n, xs with
  | O, _ => ys
  | S n', xH => xI (shiftl_pos n' ys)
  | S n', xI xs' => xI (catbit_pos n' xs' ys)
  | S n', xO xs' => xO (catbit_pos n' xs' ys)
  end.

Definition catbit (n : nat) (xs : N) (ys : N) : N :=
  match ys with
  | N0 => xs
  | Npos ys' =>
    match xs with
    | N0 => Npos (shiftl_pos n ys')
    | Npos xs' => Npos (catbit_pos n xs' ys')
    end
  end.

Example ex_catbit : catbit 3 2 1 = 10. Proof. reflexivity. Qed.

Fixpoint hex' (hs : list N) : N :=
  match hs with
  | [] => 0
  | h :: hs' => catbit 4 h (hex' hs')
  end.

Definition hex hs := hex' (rev hs).

Example ex_hex : hex [1;0;0] = 256. Proof. reflexivity. Qed.

Definition N64 := N.

Notation A := 10%N.
Notation B := 11%N.
Notation C := 12%N.
Notation D := 13%N.
Notation E := 14%N.
Notation F := 15%N.

(* 0x9e3779b97f4a7c15 *)
Definition golden_gamma : N :=
  hex [9;E;3;7;7;9;B;9;7;F;4;A;7;C;1;5].

Definition shift_xor z n :=
  N.lxor z (N.shiftr z n).

Definition mix64 z :=
  (* 0xff51afd7ed558ccd *)
  let c0 := hex [F;F;5;1;A;F;D;7;E;D;5;5;8;C;C;D] in
  (* 0xc4ceb9fe1a85ec53 *)
  let c1 := hex [C;4;C;E;B;9;F;E;1;A;8;5;E;C;5;3] in
  let z := truncate 64 (shift_xor z 33 * c0) in
  let z := truncate 64 (shift_xor z 33 * c1) in
  truncate 64 (shift_xor z 33).

Definition mix64variant13 z :=
  (* 0xbf58476d1ce4e5b9 *)
  let c0 := hex [B;F;5;8;4;7;6;D;1;C;E;4;E;5;B;9] in
  (* 0x94d049bb133111eb *)
  let c1 := hex [9;4;D;0;4;9;B;B;1;3;3;1;1;1;E;B] in
  let z := truncate 64 (shift_xor z 30 * c0) in
  let z := truncate 64 (shift_xor z 27 * c1) in
  truncate 64 (shift_xor z 31).

Definition popcount_under (n : nat) (z : N) : bool :=
  match z with
  | N0 => true
  | Npos xs =>
    let fix popcount_under' n xs :=
        match n, xs with
        | O, _ => false
        | _, xO xs' => popcount_under' n xs'
        | S n', xI xs' => popcount_under' n' xs'
        | _, xH => true
        end in
    popcount_under' n xs
  end.

Definition mix_gamma z :=
  let z := N.lor (mix64 z) 1 in
  if popcount_under 24 (truncate 64 (shift_xor z 1)) then
    N.lxor z (hex [A;A;A;A;A;A;A;A;A;A;A;A;A;A;A;A])
  else
    z.

Record State := MkState {
  seed : N64;
  gamma : N64;
}.

Definition of_seed n : State :=
  {| seed := n; gamma := golden_gamma |}.

Definition mk_split s1 s2 :=
  {| seed := mix64variant13 s1;
     gamma := mix_gamma s2;
  |}.

Definition split '(MkState s0 g) :=
  let s1 := truncate 64 (s0 + g) in
  let s2 := truncate 64 (s1 + g) in
  let rng1 := mk_split s1 s2 in
  let rng2 := MkState s2 g in
  (rng1, rng2).

Definition next_int64 '(MkState s0 g) :=
  let s1 := truncate 64 (s0 + g) in
  (mix64variant13 s1, MkState s1 g).

(* Misc utils. *)

Import BinInt.

Definition two's (n : N) : Z :=
  if n <? 2 ^ 63 then
    Z.of_N n
  else
    Z.of_N n - 2 ^ 64.
