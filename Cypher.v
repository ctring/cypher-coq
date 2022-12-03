From Coq Require Import Strings.String.
From Coq Require Import PeanoNat.
From Coq Require Import Bool.Bool. Import BoolNotations.
From Coq Require Import Lists.List. Import ListNotations.
From Coq Require Import Program.Basics.
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
  | VStr  : string -> value.

#[export] Instance eq_value : Eq value :=
{
  eqb v1 v2 := match v1, v2 with
               | VId i1, VId i2 => (eqb i1 i2)
               | VNull, VNull => true
               | VNum n1, VNum n2 => (n1 =? n2)%nat
               | VStr s1, VStr s2 => (s1 =? s2)%string
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
  | EPath : value -> expr.

Definition value_to_expr v :=
  match v with
  | VId _ => EId v
  | VNull => ENull
  | VNum _ => ENum v
  | VStr _ => EStr v
  end.

Coercion value_to_expr : value >-> expr. 

Declare Custom Entry ent_expr.
Notation "<{ e }>"  := e (at level 0, e custom ent_expr at level 99).
Notation "x"        := (value_to_expr x) (in custom ent_expr at level 0, x constr at level 0).
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

(* Definition test_graph := to_graph test_graph_cons. *)

Record node_pat := NodePat
{
  (* Name to bind to the matching nodes *)
  np_name   : option string
  (* Node labels to match with *)
; np_labels : list string
  (* Node properties to match with *)
; np_prop   : properties
}.

Inductive direction : Type :=
  | left2right
  | right2left
  | undirected.

Record rel_pat := RelPat
{
  (* Relationship direction to match with *)
  rp_dir    : direction
  (* Name to bind to the matching relations *)
; rp_name   : option string 
  (* Relationship types to match with *)
; rp_types  : list string 
  (* Relationship properties to match with *)
; rp_prop   : properties
}.

Inductive pattern : Type :=
  | PatNode : node_pat -> pattern
  | PatNodeRel : node_pat -> rel_pat -> pattern -> pattern.

Declare Custom Entry ent_pat.
Declare Custom Entry ent_rel.
Notation "'??' e '??'" := e (at level 0, e custom ent_pat at level 99, only parsing).
Notation "::" := nil (in custom ent_pat at level 0).
Notation "':' x ':' .. ':' y" := (cons x .. (cons y nil) ..) 
                                 (in custom ent_pat at level 0, x constr at level 0, y constr at level 0,
                                  format "':' x ':' .. ':' y").
Notation "-( a lbl prop )-" := (PatNode (NodePat (Some a) lbl prop))
                               (in custom ent_pat at level 99, a constr at level 0, prop constr at level 0).
Notation "-( lbl prop )-" := (PatNode (NodePat None lbl prop))
                             (in custom ent_pat at level 99, prop constr at level 0).
Notation "r" := r (in custom ent_pat at level 0, r custom ent_rel at level 99).
Notation "-[ a types prop ]->" := (RelPat left2right (Some a) types prop)
                                   (in custom ent_rel at level 0, a constr at level 0,
                                    types custom ent_pat at level 0, prop constr at level 0).
Notation "<-[ a types prop ]-" := (RelPat right2left (Some a) types prop)
                                  (in custom ent_rel at level 0, a constr at level 0,
                                   types custom ent_pat at level 0, prop constr at level 0).
Notation "-[ a types prop ]-" := (RelPat undirected (Some a) types prop)
                                 (in custom ent_rel at level 0, a constr at level 0,
                                  types custom ent_pat at level 0, prop constr at level 0).
Notation "-[ types prop ]->" := (RelPat left2right None types prop)
                                (in custom ent_rel at level 0,
                                 types custom ent_pat at level 0, prop constr at level 0).
Notation "<-[ types prop ]-" := (RelPat right2left None types prop)
                                (in custom ent_rel at level 0,
                                 types custom ent_pat at level 0, prop constr at level 0).
Notation "-[ types prop ]-" := (RelPat undirected None types prop)
                               (in custom ent_rel at level 0,
                                types custom ent_pat at level 0, prop constr at level 0).
Notation "p r -( a lbl prop )-" := (PatNodeRel (NodePat (Some a) lbl prop) r p)
                                   (in custom ent_pat at level 99, right associativity,
                                    a constr at level 0, prop constr at level 0, r custom ent_rel at level 0).
Notation "p r -( lbl prop )-" := (PatNodeRel (NodePat None lbl prop) r p)
                                 (in custom ent_pat at level 99, right associativity,
                                  prop constr at level 0, r custom ent_rel at level 0).

Check ?? -( :"b":"c" [] )- ??.
Check ?? -( :"b":"c" [] )- <-[ "test" :"a":"b" [] ]- -( "test" :"b":"c" [] )- ??.
Check ?? -( :: [] )- ??.
(** Query **)
Record query := Query { q_pat : pattern ; q_ret : list (expr * string) }.

Declare Custom Entry ent_ret.
Notation "'RETURN' x , .. , y" := (cons x .. (cons y nil) ..) (in custom ent_ret at level 99).
Notation "x 'AS' a" := (x, a) (in custom ent_ret at level 90, x constr at level 0, a constr at level 0).
Notation "'MATCH' p r" := (Query p r) (at level 90, p custom ent_pat at level 0, r custom ent_ret at level 0). 

Check MATCH -( :"b":"c" [] )- -[ :"b" [] ]-> -( :"c" [] )-
      RETURN <{ "cd"["abc"] }> AS "abc",
             <{ 1 }> AS "num1",
             <{ 1 + 2 + 3 }> AS "num2".             

(***************************************************************************)
(****************************  PATTERN MATCHING ****************************)
(***************************************************************************)

Fixpoint id_in_path (p : path) (i : id) : bool :=
  match p with
  | PathNode _ => false
  | PathNodeRel id1 id2 p' => if eqb i id1 then true else
                         if eqb i id2 then true else id_in_path p' i
  end.

Definition match_node_pat (np : node_pat) (n : node) : bool :=
  match np_labels np with
  | [] => true
  | labels => (existsb (fun l => l =? (n_label n)) labels)
  end &&
  (map_includes (n_prop n) (np_prop np)).

Example match_node_pat1 : match_node_pat (NodePat None ["foo"; "bar"] [("a", VNum 1)])
                                         (Node (NodeId 0) "foo" [("a", VNum 1); ("b", VStr "c")])
                                         = true.
Proof.
  reflexivity.
Qed.

Example match_node_pat2 : match_node_pat (NodePat None ["foo"; "bar"] [("a", VNum 1)])
                                         (Node (NodeId 0) "foo" [("b", VStr "c")])
                                         = false.
Proof.
  reflexivity.
Qed.

Example match_node_pat3 : match_node_pat (NodePat None ["foo"; "bar"] [])
                                         (Node (NodeId 0) "far" [("b", VStr "c")])
                                         = false.
Proof.
  reflexivity.
Qed.

Definition match_rel_pat (rp : rel_pat) (r : rel) : bool :=
  match rp_types rp with
  | [] => true
  | types => (existsb (fun t => t =? (r_type r)) types)
  end
  &&
  (map_includes (r_prop r) (rp_prop rp)).

Example match_rel_pat1 : match_rel_pat (RelPat undirected None ["foo"; "bar"] [("a", VNum 1)])
                                       (Rel (NodeId 0) (NodeId 0) (NodeId 0) "foo" [("a", VNum 1); ("b", VStr "c")])
                                       = true.
Proof.
  reflexivity.
Qed.

Example match_rel_pat2 : match_rel_pat (RelPat undirected None ["foo"; "bar"] [("c", VNum 1)])
                                       (Rel (NodeId 0) (NodeId 0) (NodeId 0) "foo" [("a", VNum 1); ("b", VStr "c")])
                                       = false.
Proof.
  reflexivity.
Qed.

Example match_rel_pat3 : match_rel_pat (RelPat undirected None ["far"] [])
                                       (Rel (NodeId 0) (NodeId 0) (NodeId 0) "foo" [("a", VNum 1); ("b", VStr "c")])
                                       = false.
Proof.
  reflexivity.
Qed.

(*
  Determine if a relationship (r) can connect the head of the path (head)
  to a matching node (m_nodes) while satisfying the relationship pattern (rp).
  Return a pair of (rel_id, node_id) if the relationship  matches the pattern,
  return None otherwise.
*)
Definition match_direction (head : id) (node_ids : list id)
                           (rp : rel_pat) (r : rel) : option (id * id) :=
  let hd_matches_src := eqb head (r_src r) in
  let hd_matches_tgt := eqb head (r_tgt r) in
  let src_in_nodes := existsb (fun n => eqb n (r_src r)) node_ids in
  let tgt_in_nodes := existsb (fun n => eqb n (r_tgt r)) node_ids in
    match (rp_dir rp) with
    | left2right => if hd_matches_src && tgt_in_nodes then Some ((r_tgt r), (r_id r)) else None
    | right2left => if hd_matches_tgt && src_in_nodes then Some ((r_src r), (r_id r)) else None
    | undirected => if hd_matches_src && tgt_in_nodes then Some ((r_tgt r), (r_id r)) else
                    if hd_matches_tgt && src_in_nodes then Some ((r_src r), (r_id r)) else
                    None
    end.

Check (compose negb (compose (id_in_path (PathNode (NodeId 1))) r_id)).

Definition refine_path (g : graph) (np : node_pat) (rp : rel_pat) (p : path) : list path :=
  (* Keep nodes that match the node pattern *)
  let nodes := filter (match_node_pat np) (get_nodes g) in
  (* Keep relationships that matche the relationship pattern *)
  let rels  := filter (match_rel_pat rp) (get_rels g) in
  (* Filter out relationships that already exists in the path *)
  let rels  := filter  (compose negb (compose (id_in_path p) r_id)) rels in
  (* Keep relationships that connect the head of the path to a
     matching node in the matching direction *)
  let nodes_rels := map (match_direction (hd_path p) (map n_id nodes) rp) rels in
    (* Create extended paths (ep) by combining current path with
       the new relationships and nodes *)
    fold_left (fun ep nr => match nr with
                            | None => ep
                            | Some (nid, rid) => (PathNodeRel nid rid p) :: ep
                            end)  
              nodes_rels [].

Fixpoint pattern_match (g : graph) (p : pattern) : list path :=
  match p with
  | PatNode np => map (compose PathNode n_id) (filter (match_node_pat np) (get_nodes g))
  | PatNodeRel np rp p' => flat_map (refine_path g np rp) (pattern_match g p')
  end.

Fixpoint bind_path (g : graph) (p : pattern) (pth : path) : record :=
  let nodes := get_nodes g in
  let rels := get_rels g in
    match p, pth with
    | PatNode (NodePat (Some name) _ _), PathNode i => map_set map_empty name (VId i)
    | PatNodeRel np rp p', PathNodeRel ni ri pth' =>
      (* Bind the rest of the pattern *)
      let rec := bind_path g p' pth' in
      (* Bind the current relationship *)
      let rec := match rp_name rp with
                 | Some name => map_set rec name ri
                 | _ => rec
                 end in
        (* Bind the current node *)
        match np_name np with
        | Some name => map_set rec name ni
        | _ => rec
        end
    | _, _ => map_empty
    end. 

Definition lookup_prop (g : graph) (i : id) (key : string) : option value :=
  match i with
  | NodeId _ => ssrfun.Option.bind (fun nd => map_get (n_prop nd) key) (get_node g i)
  | RelId _ => ssrfun.Option.bind (fun rl => map_get (r_prop rl) key) (get_rel g i)
  end.

Fixpoint eval_expr (g : graph) (b : record) (e : expr) : value :=
  match e with
  | EId i => i
  | ENull => VNull
  | ENum n => n
  | EPlus e1 e2 => vplus (eval_expr g b e1) (eval_expr g b e2)
  | EMinus e1 e2 => vminus (eval_expr g b e1) (eval_expr g b e2)
  | EMult e1 e2 => vmult (eval_expr g b e1) (eval_expr g b e2)
  | EStr s => s
  | EPath p => p
  | EProp name propkey => 
    let propval := ssrfun.Option.bind 
      (fun v => match v with
                | VId i => lookup_prop g i propkey
                | _ => None
                end)
      (map_get b name) in 
        match propval with
        | Some v => v
        | None => VNull
        end
  end.

Compute (pattern_match test_graph 
                       ?? 
                        -( :"state" [] )- <-[ :: [] ]- -( :: [] )- 
                        -[ :: [] ]- -( :: [])-
                       ??).

Compute (eval_expr test_graph [("org", VId (NodeId 7))] <{ "org"["area"] }>).

Fixpoint project_record (g : graph) (r : record) (ret : list (expr * string)) : record :=
  match ret with
  | [] => []
  | (e, name) :: ret' => map_set (project_record g r ret')
                                 name
                                 (eval_expr g r e)
  end.

Fixpoint project (g : graph) (ret : list (expr * string)) (t : table) : table :=
  match t with
  | [] => []
  | rec :: t' => (project_record g rec ret) :: (project g ret t')
  end.

Definition test_pattern :=  ?? 
                            -( "s" :"state" [] )- <-[ :: [] ]- -( "p" :"person" [] )-
                            ??.

Definition test_paths := pattern_match test_graph test_pattern.
Definition bound_test_paths := map (bind_path test_graph test_pattern) test_paths.
Definition projected_table := project test_graph [(<{ "p"["name"] }>, "who");
                                                  (<{ "s"["name"] }>, "where")]
                                                 bound_test_paths.

(* Compute projected_table. *)

Definition execute (g : graph) (q : query) : table :=
  let paths := pattern_match g (q_pat q) in
  let bounded_paths := map (bind_path g (q_pat q)) paths in
    project g (q_ret q) bounded_paths.

Definition test_query := MATCH -( "s" :"state":"organization" [] )- -[ :: [] ]- -( "p" :"person" [] )-
                         RETURN <{ "p"["name"] }> AS "who",
                                <{ "s"["name"] }> AS "where",
                                <{ 1 }> AS "one".

Compute (execute test_graph test_query).