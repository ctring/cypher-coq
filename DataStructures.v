From Coq Require Import Strings.String.
From Coq Require Import PeanoNat.
From Coq Require Import Bool.Bool. Import BoolNotations.
From Coq Require Import Lists.List. Import ListNotations.
From Cypher Require Import Decidability.
From Cypher Require Import Map.

Open Scope string.
(** Values **)

Inductive id : Type :=
  | NodeId : nat -> id
  | RelId  : nat -> id.
  
#[export] Instance eq_id : Eq id :=
{
  eqb i1 i2 := match i1, i2 with
               | NodeId n1, NodeId n2 => (n1 =? n2)%nat
               | RelId n1, RelId n2 => (n1 =? n2)%nat
               | _, _ => false
               end
}.

#[export] Instance eqdec_id : EqDec id.
Proof.
  constructor. 
  intros; destruct x; destruct y; split; intros; simpl; try discriminate; auto;
  try (unfold eqb in H; unfold eq_id in H; apply Nat.eqb_eq in H; auto);
  try (injection H; intros; apply Nat.eqb_eq; assumption).
Qed.

Inductive path : Type :=
  (* path with a single node *)
  | PathNode : id -> path
  (* path with multiple nodes *)
  | PathNodeRel : id -> id -> path -> path.

Fixpoint eq_path_aux (p1 p2 : path) :=
  match p1, p2 with
  | PathNode i1, PathNode i2 => (eqb i1 i2)
  | PathNodeRel ia1 ib1 p1, PathNodeRel ia2 ib2 p2 =>
    (eqb ia1 ia2) && (eqb ib1 ib2) && (eq_path_aux p1 p2)
  | _, _ => false
  end. 

#[export] Instance eq_path : Eq path :=
{
  eqb := eq_path_aux
}.

Definition hd_path p :=
  match p with
  | PathNode i => i
  | PathNodeRel i _ _ => i
  end.

Notation "-( n )-" := (PathNode (NodeId n)) (at level 1, format "-(  n  )-").
Notation "p -[ r ]--( x )-" := (PathNodeRel (NodeId x) (RelId r) p)
                            (at level 1, left associativity,
                             format "p -[  r  ]--(  x  )-").

Inductive well_formed_path : path -> Prop :=
  | WFNode : forall (n : nat),
              well_formed_path -( n )-
  | WFMulti : forall (n r : nat) (p : path),
               well_formed_path p -> well_formed_path p-[ r ]--( n )-.

Example wfp1 : well_formed_path -(1)-.
Proof.
  apply WFNode.
Qed.

Example wfp3 : well_formed_path -(1)--[2]--(3)--[4]--(5)-.
Proof.
  repeat apply WFMulti. apply WFNode.
Qed.

Example wfp4 : ~well_formed_path (PathNode (RelId 1)).
Proof.
  unfold not. intros H. inversion H.
Qed.

Example wfp5 : ~well_formed_path (PathNodeRel (NodeId 1) (NodeId 2) (PathNode (NodeId 3))).
Proof.
  unfold not. intros H. inversion H.
Qed.

Example wfp6 : ~well_formed_path (PathNodeRel (NodeId 1) (RelId 2)
                                         (PathNodeRel (RelId 3) (NodeId 4) (PathNode (NodeId 5)))).
Proof.
  unfold not. intros H.
  inversion H. inversion H1.
Qed.

Inductive value : Type :=
  | VNull : value
  | VId   : id -> value
  | VNum  : nat -> value
  | VStr  : string -> value
  | VBool : bool -> value. 

#[export] Instance eq_value : Eq value :=
{
  eqb v1 v2 := match v1, v2 with
               | VId i1, VId i2 => (eqb i1 i2)
               | VNull, VNull => true
               | VNum n1, VNum n2 => (n1 =? n2)%nat
               | VStr s1, VStr s2 => (s1 =? s2)%string
               | VBool b1, VBool b2 => (b1 =? b2)%bool
               | _, _ => false
               end
}.

#[export] Instance eqdec_value : EqDec value.
Proof.
  constructor.
  intros; destruct x; destruct y; split; intros; simpl; try discriminate; auto;
  unfold eqb in H; unfold eq_value in H.
  - apply (@eqb_eq id eq_id eqdec_id) in H. rewrite H. reflexivity.
  - injection H as H. apply (@eqb_eq id eq_id eqdec_id). assumption.
  - apply Nat.eqb_eq in H. rewrite H. reflexivity.  
  - injection H as H. apply Nat.eqb_eq. assumption.
  - apply String.eqb_eq in H. rewrite H. reflexivity.
  - injection H as H. apply String.eqb_eq. assumption.
  - apply -> Bool.eqb_true_iff in H. rewrite H. reflexivity.
  - injection H as H. apply Bool.eqb_true_iff. assumption.
Qed.

Definition vplus (v1 v2 : value) :=
  match v1, v2 with
  | VNum n1, VNum n2 => VNum (n1 + n2)
  | _, _ => VNull
  end.

Definition vminus (v1 v2 : value) :=
  match v1, v2 with
  | VNum n1, VNum n2 => VNum (n1 - n2)
  | _, _ => VNull
  end.

Definition vmult (v1 v2 : value) :=
  match v1, v2 with
  | VNum n1, VNum n2 => VNum (n1 * n2)
  | _, _ => VNull
  end.

Definition veq (v1 v2 : value) := VBool (eqb v1 v2). 
Definition vneq (v1 v2 : value) := VBool (negb (eqb v1 v2)).

Coercion VId : id >-> value.
Coercion VNum : nat >-> value.
Coercion VStr : string >-> value.

(** Table **)
Definition record := Map string value.
Definition table := list record.

(** Expressions **)

Inductive expr : Type :=
  (* Node/Relationship Identifier *)
  | EId : value -> expr
  (* Null *)
  | ENull : expr
  (* Number *)
  | ENum : value -> expr
  | EPlus : expr -> expr -> expr
  | EMinus : expr -> expr -> expr
  | EMult : expr -> expr -> expr
  (* String *)
  | EStr : value -> expr
  (* Property *)
  | EProp : string -> string -> expr
  (* Path *)
  | EPath : value -> expr
  (* Bool *)
  | EBool : value -> expr
  | EEq : expr -> expr -> expr
  | ENeq : expr -> expr -> expr.

Definition value_to_expr v :=
  match v with
  | VId _ => EId v
  | VNull => ENull
  | VNum _ => ENum v
  | VStr _ => EStr v
  | VBool _ => EBool v
  end.

Coercion value_to_expr : value >-> expr. 

Declare Custom Entry ent_expr.
Notation "<{ e }>"  := e (at level 0, e custom ent_expr at level 99).
Notation "x"        := (value_to_expr x) (in custom ent_expr at level 0, x constr at level 0).
Notation "x = y"    := (EEq x y) (in custom ent_expr at level 60, left associativity).
Notation "x <> y"   := (ENeq x y) (in custom ent_expr at level 60, left associativity).
Notation "x + y"    := (EPlus x y) (in custom ent_expr at level 50, left associativity).
Notation "x - y"    := (EMinus x y) (in custom ent_expr at level 50, left associativity).
Notation "x * y"    := (EMult x y) (in custom ent_expr at level 40, left associativity).
Notation "n [ k ]"  := (EProp n k) (in custom ent_expr at level 0,
                                    n constr at level 0, k constr at level 0).

(** Graph **)

Definition properties := Map string value.

Record node := Node
{
  (* Id of the node *)
  n_id    : id
  (* Label of the node *)
; n_label : string
  (* Properties of the node *)
; n_prop  : properties 
}.

Record rel := Rel
{
  (* Id of the source node *)
  r_src   : id
  (* Id of the target node *)
; r_tgt   : id
  (* Id of the relationship *)
; r_id    : id
  (* Type of the relationship *)
; r_type  : string 
  (* Properties of the relationship *)
; r_prop  : properties
}.

Inductive graph : Type :=
  | GEmpty  : graph
  | GNode   : node -> graph -> graph
  | GRel    : rel -> graph -> graph.

Declare Custom Entry ent_graph.
Notation "'G<>G'" := GEmpty (at level 0, only parsing).
Notation "'G<' e '>G'" := e (at level 0, only parsing, e custom ent_graph at level 99).
Notation "-( i lbl props )-" := (GNode (Node (NodeId i) lbl props) GEmpty)
                                (in custom ent_graph at level 0,
                                 i constr at level 0, lbl constr at level 0, props constr at level 0,
                                 format "-(  i  lbl  props  )-").
Notation "g ; -( i lbl props )-" := (GNode (Node (NodeId i) lbl props) g) 
                                   (in custom ent_graph at level 99, left associativity,
                                    i constr at level 0, lbl constr at level 0, props constr at level 0,
                                    format "g ; '//' -(  i  lbl  props  )-").
Notation "g ; -( s )--[ i type props ]->-( t )-" := (GRel (Rel (NodeId s) (NodeId t) (RelId i) type props) g)
                                                    (in custom ent_graph at level 99, left associativity,
                                                     s constr at level 0, i constr at level 0, type constr at level 0,
                                                     props constr at level 0, t constr at level 0,
                                                     format "g ; '//' -(  s  )--[  i  type  props  ]->-(  t  )-").

Fixpoint get_nodes (g : graph) : list node :=
  match g with
  | GEmpty => []
  | GNode n g' => n :: (get_nodes g')
  | GRel _ g' => get_nodes g'
  end.

Fixpoint get_rels (g : graph) : list rel :=
  match g with
  | GEmpty => []
  | GNode _ g' => get_rels g'
  | GRel r g' => r :: get_rels g'
  end.

Fixpoint get_node (g : graph) (nid : id) : option node :=
  match g with
  | GEmpty => None
  | GNode n g' => if (eqb (n_id n) nid) then Some n else get_node g' nid
  | GRel _ g' => get_node g' nid
  end.

Fixpoint get_rel (g : graph) (rid : id) : option rel :=
  match g with
  | GEmpty => None
  | GNode _ g' => get_rel g' rid
  | GRel r g' => if (eqb (r_id r) rid) then Some r else get_rel g' rid
  end.
