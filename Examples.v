From Coq Require Import Lists.List. Import ListNotations.
From Coq Require Import Strings.String.
From Cypher Require Import DataStructures.
From Cypher Require Import Query.

Open Scope string.

Definition empty_graph := G<>G.
Definition test_graph := G<
    -( 1 "person" [("name", VStr "Alice"); ("age", VNum 23); ("marital status", VStr "married")] )-;
    -( 2 "person" [("name", VStr "Bob"); ("age", VNum 24); ("marital status", VStr "single")])-;
    -( 3 "person" [("name", VStr "Charlie"); ("age", VNum 30); ("marital status", VStr "married")] )-;
    -( 4 "organization" [("name", VStr "Google"); ("area", VStr "technology")] )-;
    -( 5 "organization" [("name", VStr "Microsoft"); ("area", VStr "technology")] )-;
    -( 6 "organization" [("name", VStr "University of Maryland"); ("area", VStr "education")] )-;
    -( 7 "organization" [("name", VStr "University of Washington"); ("area", VStr "education")] )-;
    -( 8 "state" [("name", VStr "Washington")] )-;
    -( 9 "state" [("name", VStr "New York")] )-;
    -( 10 "state" [("name", VStr "Maryland")] )-;
    -( 1 )--[ 1 "works_at" [("since", VNum 2018)] ]->-( 4 )-;
    -( 1 )--[ 2 "from" [] ]->-( 10 )-;
    -( 1 )--[ 3 "studied_at" [] ]->-( 6 )-;
    -( 2 )--[ 4 "works_at" [("since", VNum 2020)] ]->-( 4 )-;
    -( 2 )--[ 5 "from" [] ]->-( 9 )-;
    -( 2 )--[ 6 "studied_at" [] ]->-( 7 )-;
    -( 3 )--[ 7 "works_at" [("since", VNum 2019)] ]->-( 5 )-;
    -( 3 )--[ 8 "from" [] ]->-( 8 )-;
    -( 3 )--[ 9 "studied_at" [] ]->-( 6 )-;
    -( 4 )--[ 10 "locates_in" [] ]->-( 9 )-;
    -( 5 )--[ 11 "locates_in" [] ]->-( 8 )-;
    -( 6 )--[ 12 "locates_in" [] ]->-( 10 )-;
    -( 7 )--[ 13 "locates_in" [] ]->-( 8 )-
  >G.


(* Names and ages of all people ("Dummy" column is just to demonstrate constant projection ) *)
Definition q_name_and_age := MATCH -( "p" :"person" [] )-
                             RETURN <{ "p"["name"] }> AS "Name",
                                    <{ "p"["age"] }> AS "Age",
                                    <{ 1 + 1 }> AS "Dummy".
Example q_name_and_age_ok : 
  execute test_graph q_name_and_age = [
    [("Name", VStr "Alice"); ("Age", VNum 23); ("Dummy", VNum 2)];
    [("Name", VStr "Bob"); ("Age", VNum 24); ("Dummy", VNum 2)];
    [("Name", VStr "Charlie"); ("Age", VNum 30); ("Dummy", VNum 2)]
  ].
Proof.
  reflexivity.
Qed.

(* Names and workplaces of married people *)
Definition q_workplace_of_married_people :=
  MATCH -( "p" :"person" [("marital status", VStr "married")] )- -[ "w" :"works_at" [] ]-> -( "o" :"organization" [] )-
  RETURN <{ "p"["name"] }> AS "Name",
         <{ "o"["name"] }> AS "Company",
         <{ 2022 - "w"["since"] }> AS "Years of work".
Example q_workplace_of_married_people_ok:
  execute test_graph q_workplace_of_married_people = [
    [("Name", VStr "Alice"); ("Company", VStr "Google"); ("Years of work", VNum 4)];
    [("Name", VStr "Charlie"); ("Company", VStr "Microsoft"); ("Years of work", VNum 3)]
  ].
Proof.
  reflexivity.
Qed.

(* People and organizations from the state of Washington *)
Definition q_from_Washington :=
  MATCH -( :: [("name", VStr "Washington")] )- <-[ :"from":"locates_in" [] ]- -( "entity" :: [] )-
  RETURN <{ "entity"["name"] }> AS "Name",
         <{ "entity"["age"] }> AS "Age",
         <{ "entity"["area"]}> AS "Area".
Example q_from_Washington_ok:
  execute test_graph q_from_Washington = [
    [("Name", VStr "University of Washington"); ("Area", VStr "education")];
    [("Name", VStr "Microsoft"); ("Area", VStr "technology")];
    [("Name", VStr "Charlie"); ("Age", VNum 30)]
  ].
Proof.
  reflexivity.
Qed.

(* People and the states they work in *)
Definition q_people_work_in_states :=
  MATCH -( "p" :"person" [] )- -[ "w" :"works_at" [] ]- -( "o" :: [] )- -[ :"locates_in" [] ]- -( "s" :: [] )-
  RETURN <{ "p"["name"] }> AS "Name",
         <{ "o"["name"] }> AS "Company",
         <{ "s"["name"]}> AS "State",
         <{ "w"["since"]}> AS "Since".
Example q_people_work_in_states_ok :
  execute test_graph q_people_work_in_states = [
    [("Name", VStr "Alice"); ("Company", VStr "Google"); ("State", VStr "New York"); ("Since", VNum 2018)];
    [("Name", VStr "Bob"); ("Company", VStr "Google"); ("State", VStr "New York"); ("Since", VNum 2020)];
    [("Name", VStr "Charlie"); ("Company", VStr "Microsoft"); ("State", VStr "Washington"); ("Since", VNum 2019)]
  ].
Proof.
  reflexivity.
Qed.

Definition q_people_work_and_come_from_the_same_state :=
  MATCH -( "p" :"person" [] )- -[ :"works_at" [] ]-> 
        -( :: [] )- -[ :"locates_in" [] ]-> 
        -( "s" :: [] )- <-[ :"from" [] ]- -( "p" :"person" [])-
  RETURN <{ "p"["name"] }> AS "Name",
         <{ "s"["name"]}> AS "State".
Example q_people_work_and_come_from_the_same_state_ok :
  execute test_graph q_people_work_and_come_from_the_same_state = [
    [("Name", VStr "Bob"); ("State", VStr "New York")];
    [("Name", VStr "Charlie"); ("State", VStr "Washington")]
  ].
Proof.  
  reflexivity.
Qed.
