Require Import List.
Import ListNotations.
Require Import ZArith.

Require Import Pseudorandom.SplitMix.

Fixpoint split_many (n : nat) g :=
  match n with
  | O => g
  | S n' => let (g, _) := split g in split_many n' g
  end.

Time Compute (next_int64 (split_many 3000%nat (of_seed 33))).

Definition test_run :=
  let g0 := of_seed 33 in
  let (x0, g0) := next_int64 g0 in
  let (x1, g0) := next_int64 g0 in
  let (g1, g0) := split g0 in
  let (x2, g1) := next_int64 g1 in
  let (g2, g1) := split g1 in
  let (x3, g1) := next_int64 g1 in
  let (g3, g2) := split g2 in
  let (x4, g2) := next_int64 g2 in
  let (x5, g2) := next_int64 g2 in
  let (x6, g3) := next_int64 g3 in
  let (x7, g3) := next_int64 g3 in
  let (x8, g3) := next_int64 g3 in
  let (x9, _) := next_int64 (split_many 300%nat g3) in
  map two's [x0;x1;x2;x3;x4;x5;x6;x7;x8;x9].

Example ex :
  test_run =
  [ 3174492301114349736;  1387786489429541378;
    2612135949649290519; -6594435460564017959;
    6114845654480584590; -3434961282303982149;
   -4710980162942128616; -5883331640739962744;
    7437753320184232638; -2875907909505887564]%Z.
Proof. Time native_compute. reflexivity. Qed.
