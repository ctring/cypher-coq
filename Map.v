From Coq Require Import Lists.List. Import ListNotations.
From Coq Require Import Lists.ListSet.
From Coq Require Import Bool.Bool Bool.Sumbool.
From Coq Require Import Arith.Peano_dec.
From Coq Require Import Strings.String. 

(* ================================================================= *)
(** ** List-Based Maps *)

(** To encode typing environments (and, later on, states), we will
    need maps from identifiers to values. However, the function-based
    representation in the _Software Foundations_ version of Imp is not
    well suited for testing: we need to be able to access the domain
    of the map, fold over it, and test for equality; these are all
    awkward to define for Coq functions. Therefore, we introduce a
    simple list-based map representation that uses [id]s as the keys.

    The operations we need are:
       - [empty] : To create the empty map.
       - [get] : To look up the binding of an element, if any.
       - [set] : To update the binding of an element.
       - [dom] : To get the list of keys in the map. *)

(** The implementation of a map is a simple association list.  If a
    list contains multiple tuples with the same key, then the binding
    of the key in the map is the one that appears first in the list;
    that is, later bindings can be shadowed. *)

Definition Map K V := list (K * V).

(** The [empty] map is the empty list. *)

Definition map_empty {K V} : Map K V := [].

Notation decidable_eq A := (forall x y : A, {x = y} + {x <> y}).
    
(** To [get] the binding of an identifier [x], we just need to walk 
    through the list and find the first [cons] cell where the key 
    is equal to [x], if any. *)
Fixpoint map_get {K V} (H: decidable_eq K) (m : Map K V) (x : K) : option V :=
    match m with
    | [] => None
    | (k, v) :: m' => if H x k then Some v else map_get H m' x
    end.

(** To [set] the binding of an identifier, we just need to [cons] 
    it at the front of the list. *) 

Definition map_set {K V} (m : Map K V) (x : K) (v : V) : Map K V :=
    (x, v) :: m.

(** Finally, the domain of a map is just the set of its keys. *)
Fixpoint map_dom {K V} (H: decidable_eq K) (m : Map K V) : set K :=
    match m with
    | [] => []
    | (k', v) :: m' => set_add H k' (map_dom H m')
    end.

Definition map_values {K V} (HK: decidable_eq K) 
                            (HV: decidable_eq V)
                            (m : Map K V) : set V :=
    fold_right
        (fun o sv => match o with
                 | None => sv
                 | Some v => set_add HV v sv
                 end)
        nil
        (map (map_get HK m) (map_dom HK m)).

Inductive bound_to {K V} (H: decidable_eq K) : Map K V -> K -> V -> Prop :=
  | Bind : forall x m a, @map_get K V H m x = Some a -> bound_to H m x a.

Local Open Scope string.

Check [("test", 2); ("test", 4)].
