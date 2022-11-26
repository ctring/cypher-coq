From Coq Require Import Arith.Peano_dec.
From Coq Require Import Bool.Bool. Import BoolNotations.
From Coq Require Import Lists.ListSet. 
From Coq Require Import Lists.List. Import ListNotations.
From Coq Require Import Strings.String.
From Cypher Require Import Map.

Local Open Scope string.

(** Values **)

Inductive id : Type :=
  | NodeId : nat -> id
  | RelId  : nat -> id.

Lemma id_dec : decidable_eq id.
Proof.
  repeat decide equality.
Defined.

Definition map_id_dom {V} := @map_dom id V id_dec.
Definition map_id_val := @map_values id id id_dec id_dec.

#[global]
Hint Resolve id_dec : typeclass_instances.

Inductive null : Type :=
  | Null.

Section Path.

Inductive path : Type :=
  (* path with a single node *)
  | PNode : id -> path
  (* path with multiple nodes *)
  | PMulti : id -> id -> path -> path.

Notation "-( n )-" := (PNode (NodeId n)) (at level 0, format "-(  n  )-").
Notation "-( x )---[ r ]-- p" := (PMulti (NodeId x) (RelId r) p)
                            (at level 0, right associativity,
                             format "-(  x  )---[  r  ]-- p").

Inductive well_formed_path : path -> Prop :=
  | WFNode : forall (n : nat),
              well_formed_path -( n )-
  | WFMulti : forall (n r : nat) (p : path),
               well_formed_path p -> well_formed_path -( n )---[ r ]--p.

Example wfp1 : well_formed_path -(1)-.
Proof.
  apply WFNode.
Qed.

Example wfp3 : well_formed_path -(1)---[2]---(3)---[4]---(5)-.
Proof.
  repeat apply WFMulti. apply WFNode.
Qed.

Example wfp4 : ~well_formed_path (PNode (RelId 1)).
Proof.
  unfold not. intros H. inversion H.
Qed.

Example wfp5 : ~well_formed_path (PMulti (NodeId 1) (NodeId 2) (PNode (NodeId 3))).
Proof.
  unfold not. intros H. inversion H.
Qed.

Example wfp6 : ~well_formed_path (PMulti (NodeId 1) (RelId 2)
                                         (PMulti (RelId 3) (NodeId 4) (PNode (NodeId 5)))).
Proof.
  unfold not. intros H.
  inversion H. inversion H1.
Qed.
End Path.

Inductive value : Type :=
  | VId   : id -> value
  | VNull : null -> value
  | VNum  : nat -> value
  | VStr  : string -> value
  | VPath : path -> value.

Coercion VId : id >-> value.
Coercion VNull : null >-> value.
Coercion VNum : nat >-> value.
Coercion VStr : string >-> value.
Coercion VPath : path >-> value.


Definition test (x : value) := x.
Compute (test "abc").

(** Expressions **)

Inductive expr : Type :=
  (* Node/Relationship Identifier *)
  | EId : value -> expr
  (* Name *)
  | EName : string -> expr
  (* Null *)
  | ENull : value -> expr
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
  | EPath : value -> expr.

Definition value_to_expr v :=
  match v with
  | VId _ => EId v
  | VNull _ => ENull v
  | VNum _ => ENum v
  | VStr _ => EStr v
  | VPath _ => EPath v
  end.

Coercion value_to_expr : value >-> expr. 

Declare Custom Entry ent_expr.
Notation "<{ e }>" := e (at level 0, e custom ent_expr at level 99).
Notation "x" := (value_to_expr x) (in custom ent_expr at level 0, x constr at level 0).
Notation "x + y"    := (EPlus x y) (in custom ent_expr at level 50, left associativity).
Notation "x - y"    := (EMinus x y) (in custom ent_expr at level 50, left associativity).
Notation "x * y"    := (EMult x y) (in custom ent_expr at level 40, left associativity).
Notation "@ n [ k ]"  := (EProp n k) (in custom ent_expr at level 30,
                                   n constr at level 0, k constr at level 0, format "@ n [ k ]").
Notation "@ n"      := (EName n) (in custom ent_expr at level 30, n constr at level 0, format "@ n").

(** Graph **)

Definition properties := Map string value.

Inductive node : Type :=
  | Node (node : id) (label : string) (prop : properties).

Inductive rel : Type :=
  | Rel (src tgt rel : id) (reltype : string) (prop : properties).

Inductive graph : Type :=
  | GEmpty  : graph
  | GNode   : node -> graph -> graph
  | GRel    : rel -> graph -> graph.

Declare Custom Entry ent_graph.
Notation "'G<>G'" := GEmpty (at level 0, only parsing).
Notation "'G<' e '>G'" := e (at level 0, only parsing, e custom ent_graph at level 99, format "'G<' '[' '//' e ']' '//' '>G'").
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

Record graph_rd := mkGraph
{ 
  (* Set of nodes and their properties *)
  g_nodes : Map id properties
  (* Set of relationships and their properties*)
; g_rels : Map id properties
  (* Map a relationship to its source node*)
; g_src : Map id id
  (* Map a relationship to its target node*)
; g_tgt : Map id id
  (* Map a node to a label *)
; g_lambda : Map id string
  (* Map a relationship to a relationship type *)
; g_tau : Map id string
}.

Definition empty_graph_rd := {|
  g_nodes := nil;
  g_rels := nil;
  g_src := nil;
  g_tgt := nil;
  g_lambda := nil;
  g_tau := nil
|}.

Definition id_graph (g : graph_rd) : graph_rd :=
  let (g_nodes', g_rels', g_src', g_tgt', g_lambda', g_tau') := g in
  mkGraph
    g_nodes'
    g_rels'
    g_src'
    g_tgt'
    g_lambda'
    g_tau'.

Fixpoint to_graph_rd (g : graph) : graph_rd :=
  match g with
  | GEmpty => empty_graph_rd
  | GNode (Node id label prop) g' =>
    let (g_nodes', g_rels', g_src', g_tgt', g_lambda', g_tau') := to_graph_rd g' in
    {|
      g_nodes := map_set g_nodes' id prop
    ; g_rels := g_rels'
    ; g_src := g_src'
    ; g_tgt := g_tgt'
    ; g_lambda := map_set g_lambda' id label
    ; g_tau := g_tau'
    |}
  | GRel (Rel src tgt id reltype prop) g' =>
    let (g_nodes', g_rels', g_src', g_tgt', g_lambda', g_tau') := to_graph_rd g' in
    {|
      g_nodes := g_nodes'
    ; g_rels := map_set g_rels' id prop
    ; g_src := map_set g_src' id src
    ; g_tgt := map_set g_tgt' id tgt
    ; g_lambda := g_lambda'
    ; g_tau := map_set g_tau' id reltype
    |}
  end.

Definition empty_graph := G<>G.
Definition test_graph := G<
    -( 1 "person" [("name", VStr "Alice"); ("age", VNum 23)] )-;
    -( 2 "person" [("name", VStr "Bob"); ("age", VNum 24)] )-;
    -( 3 "person" [("name", VStr "Charlie"); ("age", VNum 30)] )-;
    -( 4 "organization" [("name", VStr "Google"); ("area", VStr "technology")] )-;
    -( 5 "organization" [("name", VStr "Microsoft"); ("area", VStr "technology")] )-;
    -( 6 "organization" [("name", VStr "University of Maryland"); ("area", VStr "education")] )-;
    -( 7 "organization" [("name", VStr "University of Washington"); ("area", VStr "education")] )-;
    -( 8 "state" [("name", VStr "Washington")] )-;
    -( 9 "state" [("name", VStr "New York")] )-;
    -( 10 "state" [("name", VStr "Maryland")] )-;
    -( 1 )--[ 1 "works_at" [] ]->-( 4 )-;
    -( 1 )--[ 2 "from" [] ]->-( 9 )-;
    -( 1 )--[ 3 "studied_at" [] ]->-( 6 )-;
    -( 2 )--[ 4 "works_at" [] ]->-( 4 )-;
    -( 2 )--[ 5 "from" [] ]->-( 10 )-;
    -( 2 )--[ 6 "studied_at" [] ]->-( 7 )-;
    -( 3 )--[ 7 "works_at" [] ]->-( 5 )-;
    -( 3 )--[ 8 "from" [] ]->-( 8 )-;
    -( 3 )--[ 9 "studied_at" [] ]->-( 6 )-;
    -( 4 )--[ 10 "locates_in" [] ]->-( 9 )-;
    -( 5 )--[ 11 "locates_in" [] ]->-( 8 )-;
    -( 6 )--[ 12 "locates_in" [] ]->-( 10 )-;
    -( 7 )--[ 13 "locates_in" [] ]->-( 8 )-
  >G.

Definition test_graph_rd := to_graph_rd test_graph.

(** Pattern **)

Inductive node_pat : Type :=
  | NodePat (name : option string) (labels : list string) (prop : Map string expr).

Inductive direction : Type :=
  | left2right
  | right2left
  | undirected.

Inductive rel_pat : Type :=
  | RelPat (dir : direction) (name : option string) 
           (types : list string) (len : nat)
           (prop : Map string expr).

Inductive pattern : Type :=
  | PatNode : node_pat -> pattern
  | PatNodeRel : node_pat -> rel_pat -> pattern -> pattern.


Declare Custom Entry ent_pat.
Declare Custom Entry ent_rel.
Notation "'??' e '??'" := e (at level 0, e custom ent_pat at level 99, only parsing).
Notation "':' x ':' .. ':' y" := (cons x .. (cons y nil) ..) 
                                 (in custom ent_pat at level 0, x constr at level 0, y constr at level 0,
                                  format "':' x ':' .. ':' y").
Notation "-( a lbl prop )-" := (PatNode (NodePat (Some a) lbl prop))
                               (in custom ent_pat at level 99, right associativity, a constr at level 0, prop constr at level 0,
                                format "'-('  a  lbl  prop  ')-'").
Notation "-( lbl prop )-" := (PatNode (NodePat None lbl prop))
                             (in custom ent_pat at level 99, right associativity, prop constr at level 0,
                              format "'-('  lbl  prop  ')-'").

Notation "r" := r (in custom ent_pat at level 0, r custom ent_rel at level 99).
Notation "-[ a types m prop ]->" := (RelPat left2right (Some a) types m prop)
                                    (in custom ent_rel at level 0, a constr at level 0,
                                     types custom ent_pat at level 0, m constr at level 0,
                                     prop constr at level 0).
Notation "<-[ a types m prop ]-" := (RelPat right2left (Some a) types m prop)
                                    (in custom ent_rel at level 0, a constr at level 0,
                                     types custom ent_pat at level 0, m constr at level 0,
                                     prop constr at level 0).
Notation "-[ a types m prop ]-" := (RelPat undirected (Some a) types m prop)
                                   (in custom ent_rel at level 0, a constr at level 0,
                                    types custom ent_pat at level 0, m constr at level 0,
                                     prop constr at level 0).
Notation "-[ types m prop ]->" := (RelPat left2right None types m prop)
                                     (in custom ent_rel at level 0,
                                      types custom ent_pat at level 0, m constr at level 0,
                                      prop constr at level 0).
 Notation "<-[ types m prop ]-" := (RelPat right2left None types m prop)
                                     (in custom ent_rel at level 0,
                                      types custom ent_pat at level 0, m constr at level 0,
                                      prop constr at level 0).
 Notation "-[ types m prop ]-" := (RelPat undirected None types m prop)
                                    (in custom ent_rel at level 0,
                                     types custom ent_pat at level 0, m constr at level 0,
                                      prop constr at level 0).
Notation "-( a lbl prop )- r  p" := (PatNodeRel (NodePat (Some a) lbl prop) r p)
                                    (in custom ent_pat at level 99, right associativity,
                                     a constr at level 0, prop constr at level 0, r custom ent_rel at level 0,
                                     format "'-('  a  lbl  prop  ')-' r p").
Notation "-( lbl prop )- r  p" := (PatNodeRel (NodePat None lbl prop) r p)
                                  (in custom ent_pat at level 99, right associativity,
                                   prop constr at level 0, r custom ent_rel at level 0,
                                   format "'-('  lbl  prop  ')-' r p").

Check ?? -( :"b":"c" [] )- ??.
Check ?? -( :"b":"c" [] )- <-[ "test" :"a":"b" 1 [] ]- -( "test" :"b":"c" [] )- ??.


(** Query **)
Record Query := mkQuery { pat : pattern ; ret : list (expr * string) }.

Declare Custom Entry ent_ret.
Notation "'RETURN' x , .. , y" := (cons x .. (cons y nil) ..) (in custom ent_ret at level 99).
Notation "x 'AS' a" := (x, a) (in custom ent_ret at level 90, x constr at level 0, a constr at level 0).
Notation "'MATCH' p r" := (mkQuery p r) (at level 90, p custom ent_pat at level 0, r custom ent_ret at level 0). 

Check MATCH -( :"b":"c" [] )- -[ :"b" 2 [] ]-> -( :"c" [] )-
      RETURN <{ @"cd"["abc"] }> AS "abc",
             <{ @"ab" }> AS "bcd",
             <{ 1 }> AS "num",
             <{ 1 + 2 + 3 }> AS "num".             

(** Table **)
Inductive name : Type :=
  | Name : string -> name.

Definition record := Map name value.
Definition table := list record.


(*************************************************************************************************)
(*************************************************************************************************)

Definition label := string.
Definition reltype := string.

Record Graph := mkGraph
{ 
  (* Set of nodes and their properties *)
  N : Map id (Map string value)
  (* Set of relationships and their properties*)
; R : Map id (Map string value)
  (* Map a relationship to its source node*)
; src : Map id id
  (* Map a relationship to its target node*)
; tgt : Map id id
  (* Map a node to a label *)
; lambda : Map id label
  (* Map a relationship to a relationship type *)
; tau : Map id reltype
}.

Definition is_subset (x y : set id) : bool :=
  match set_diff id_dec x y with
  | nil => true
  | _ => false
  end.

Definition is_set_eq (x y : set id) : bool := (is_subset x y) && (is_subset y x).

Definition is_graph_well_formed (g: Graph) : bool :=
  let (N, R, src, tgt, lambda, tau) := g in
  let Nid := map_id_dom N in
  let Rid := map_id_dom R in
    (is_set_eq (map_id_dom src) Rid) &&
    (is_subset (map_id_val src) Nid) &&
    (is_set_eq (map_id_dom tgt) Rid) &&
    (is_subset (map_id_val tgt) Nid) &&
    (is_subset (map_id_dom lambda) Nid) &&
    (is_subset (map_id_dom tau) Rid).


(** Path **)
