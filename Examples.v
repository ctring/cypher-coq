From Coq Require Import Lists.List. Import ListNotations.
From Coq Require Import Strings.String.
From Cypher Require Import DataStructures.
From Cypher Require Import Query.

Open Scope string.

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

Compute (pattern_match test_graph 
?? 
-( :"state" [] )- <-[ :: [] ]- -( :: [] )- 
-[ :: [] ]- -( :: [])-
??).

Compute (eval_expr test_graph [("org", VId (NodeId 7))] <{ "org"["area"] }>).

Definition test_paths := pattern_match test_graph test_pattern.
Definition bound_test_paths := map (bind_path test_graph test_pattern) test_paths.
Definition projected_table := project test_graph [(<{ "p"["name"] }>, "who");
                                                  (<{ "s"["name"] }>, "where")]
                                                 bound_test_paths.
Compute (execute test_graph test_query).