From Coq Require Import PeanoNat.
From Coq Require Import Strings.String.
Require Import ssreflect ssrbool.

Class Eq A :=
{
    eqb: A -> A -> bool;
}.

Notation "x =? y" := (eqb x y) (at level 70).

Class Dec (P : Prop) : Type :=
  {
    dec : decidable P
  }.

Notation "P '?'" :=
  (match (@dec P _) with
   | left _ => true
   | right _ => false
   end)
  (at level 100).

Class EqDec (A : Type) {H : Eq A} :=
{
    eqb_eq : forall x y, x =? y = true <-> x = y
}.

#[export] Instance EqDec__Dec {A} `{H : EqDec A} (x y : A) : Dec (x = y).
Proof.
    constructor.
    unfold decidable.
    destruct (x =? y) eqn:E.
    - left. rewrite <- eqb_eq. assumption.
    - right. intros C. rewrite <- eqb_eq in C. rewrite E in C. inversion C.
Defined.

#[export] Instance eq_bool : Eq bool :=
{
  eqb := Bool.eqb
}.

#[export] Instance eqdec_bool : EqDec bool.
Proof.
  constructor.
  intros x y. destruct x; destruct y; simpl; unfold iff; auto.
Defined.

#[export] Instance eq_nat : Eq nat :=
{
  eqb := Nat.eqb
}.

#[export] Instance eqdec_nat : EqDec nat :=
{
  eqb_eq := Nat.eqb_eq
}.

#[export] Instance eq_string : Eq string :=
{
  eqb := String.eqb
}.

#[export] Instance eqdec_string : EqDec string :=
{
  eqb_eq := String.eqb_eq
}.

#[export] Instance eq_option {V} `{Eq V} : Eq (option V) :=
{
  eqb o1 o2 := match o1, o2 with
           | Some v1, Some v2 => eqb v1 v2
           | None, None => true
           | _, _ => false
           end 
}.

#[export] Instance eqdec_option {V} `{EqDec V} : EqDec (option V).
Proof.
  constructor.
  intros; destruct x; destruct y; split; intros; simpl; try discriminate; auto.
  - unfold eqb in H1. unfold eq_option in H1. apply H0 in H1. rewrite H1. reflexivity.
  - injection H1. intros. apply H0. assumption.
Qed.