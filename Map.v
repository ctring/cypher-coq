From Coq Require Import Bool.Bool. Import BoolNotations.
From Coq Require Import Lists.List. Import ListNotations.
From Cypher Require Import Decidability.


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


(** The implementation of a map is a simple association list.  If a
    list contains multiple tuples with the same key, then the binding
    of the key in the map is the one that appears first in the list;
    that is, later bindings can be shadowed. *)

Definition Map K V := list (K * V).

(** The [empty] map is the empty list. *)

Definition map_empty {K V} : Map K V := [].

(** To [get] the binding of an identifier [x], we just need to walk 
    through the list and find the first [cons] cell where the key 
    is equal to [x], if any. *)

Fixpoint map_get {K V} `{EqDec K} (m : Map K V) x : option V :=
    match m with
    | [] => None
    | (k, v) :: m' => if x = k ? then Some v else map_get m' x
    end.

(** To [set] the binding of an identifier, we just need to [cons] 
    it at the front of the list. *) 

Definition map_set {K V} (m : Map K V) (x : K) (v : V) : Map K V := (x, v) :: m.

(** Finally, the domain of a map is just the set of its keys. *)
Fixpoint map_dom {K V} (m : Map K V) : list K :=
    match m with
    | [] => []
    | (k', v) :: m' => k' :: map_dom m'
    end.

Fixpoint map_includes_aux {K V} `{EqDec K} `{EqDec V} (m m_included : Map K V) (dom : list K) : bool :=
    match m, m_included with
    | [], [] => true
    | _, [] => true
    | [], _ => false
    | _, _ => match dom with
              | [] => true
              | k :: dom' => if (map_get m k) =? (map_get m_included k) then
                map_includes_aux m m_included dom'
              else
                false
              end
    end.

Definition map_includes {K V} `{EqDec K} `{EqDec V} (m m_included : Map K V) : bool :=
    map_includes_aux m m_included (map_dom m_included).
