From Coq Require Import Strings.String.
From Coq Require Import PeanoNat.
From Coq Require Import Bool.Bool. Import BoolNotations.
From Coq Require Import Lists.List. Import ListNotations.
From Coq Require Import Program.Basics.
From Cypher Require Import Decidability.
From Cypher Require Import Map.
From Cypher Require Import DataStructures.

Open Scope string.

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

Example match_node_pat2 : match_node_pat (NodePat None ["foo"; "bar"] [])
                                         (Node (NodeId 0) "foo" [("a", VNum 1); ("b", VStr "c")])
                                         = true.
Proof.
  reflexivity.
Qed.

Example match_node_pat3 : match_node_pat (NodePat None ["foo"; "bar"] [("a", VNum 1)])
                                         (Node (NodeId 0) "foo" [("b", VStr "c")])
                                         = false.
Proof.
  reflexivity.
Qed.

Example match_node_pat4 : match_node_pat (NodePat None ["foo"; "bar"] [])
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
    (* Create extended paths by combining current path with
       the new relationships and nodes *)
    fold_left (fun prev nr => match nr with
                              | None => prev
                              | Some (nid, rid) => (PathNodeRel nid rid p) :: prev
                              end)  
              nodes_rels [].

Fixpoint pattern_match (g : graph) (p : pattern) : list path :=
  match p with
  | PatNode np => map (compose PathNode n_id) (filter (match_node_pat np) (get_nodes g))
  | PatNodeRel np rp p' => flat_map (refine_path g np rp) (pattern_match g p')
  end.

Definition record_set (r : record) (k : string) (v : value) : option record :=
  match map_get r k with
  | None => Some (map_set r k v)
  | Some v' => if eqb v v' then Some r else None
  end.

Fixpoint bind_path (g : graph) (p : pattern) (pth : path) : option record :=
  let nodes := get_nodes g in
  let rels := get_rels g in
    match p, pth with
    | PatNode (NodePat (Some name) _ _), PathNode i => Some (map_set map_empty name (VId i))
    | PatNodeRel np rp p', PathNodeRel ni ri pth' =>
      (* Bind the rest of the pattern *)
      let rec := bind_path g p' pth' in
      (* Bind the current relationship *)
      let rec := match rec, rp_name rp with
                 | None, _ => None
                 | Some r, Some name => record_set r name ri 
                 | _, _ => rec
                 end in
        (* Bind the current node *)
        match rec, np_name np with
        | None, _ => None
        | Some r, Some name => record_set r name ni
        | _, _ => rec
        end
    | _, _ => Some map_empty
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

Fixpoint project_record (g : graph) (r : record) (ret : list (expr * string)) : record :=
  match ret with
  | [] => []
  | (e, name) :: ret' => 
    let v := eval_expr g r e in
    let rec' := project_record g r ret' in
      match v with
      | VNull => rec'
      | _ => map_set rec' name v
      end 
  end.

Fixpoint project (g : graph) (ret : list (expr * string)) (t : table) : table :=
  match t with
  | [] => []
  | rec :: t' => (project_record g rec ret) :: (project g ret t')
  end.

Definition execute (g : graph) (q : query) : table :=
  let paths := pattern_match g (q_pat q) in
  let bounded_paths := fold_left (
    fun prev p =>
      match (bind_path g (q_pat q) p) with
      | None => prev
      | Some rec => rec :: prev
      end) paths [] in
    project g (q_ret q) bounded_paths.
