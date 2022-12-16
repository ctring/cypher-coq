From Coq Require Import Lists.List. Import ListNotations.
From Coq Require Import Strings.String.
From Cypher Require Import DataStructures.
From Cypher Require Import Query.

Open Scope string.

Definition empty_graph := G<>G.
Definition test_graph := G<
    -( 1 "person" [("name", VStr "Alice"); ("bornIn", VNum 1995); ("marital status", VStr "married")] )-;
    -( 2 "person" [("name", VStr "Bob"); ("bornIn", VNum 1999); ("marital status", VStr "single")])-;
    -( 3 "person" [("name", VStr "Charlie"); ("bornIn", VNum 1994); ("marital status", VStr "married")] )-;
    -( 4 "organization" [("name", VStr "Google"); ("area", VStr "technology")] )-;
    -( 5 "organization" [("name", VStr "Microsoft"); ("area", VStr "technology")] )-;
    -( 6 "organization" [("name", VStr "University of Maryland"); ("area", VStr "education")] )-;
    -( 7 "organization" [("name", VStr "University of Washington"); ("area", VStr "education")] )-;
    -( 8 "state" [("name", VStr "Washington")] )-;
    -( 9 "state" [("name", VStr "New York")] )-;
    -( 10 "state" [("name", VStr "Maryland")] )-;
    -( 1 )--[ 1 "worksAt" [("since", VNum 2018)] ]->-( 4 )-;
    -( 1 )--[ 2 "from" [] ]->-( 10 )-;
    -( 1 )--[ 3 "studiesAt" [] ]->-( 6 )-;
    -( 2 )--[ 4 "worksAt" [("since", VNum 2020)] ]->-( 4 )-;
    -( 2 )--[ 5 "from" [] ]->-( 9 )-;
    -( 2 )--[ 6 "studiesAt" [] ]->-( 7 )-;
    -( 3 )--[ 7 "worksAt" [("since", VNum 2019)] ]->-( 5 )-;
    -( 3 )--[ 8 "from" [] ]->-( 8 )-;
    -( 3 )--[ 9 "studiesAt" [] ]->-( 6 )-;
    -( 4 )--[ 10 "locatesIn" [] ]->-( 9 )-;
    -( 5 )--[ 11 "locatesIn" [] ]->-( 8 )-;
    -( 6 )--[ 12 "locatesIn" [] ]->-( 10 )-;
    -( 7 )--[ 13 "locatesIn" [] ]->-( 8 )-
  >G.

(* Match with all possible nodes. Some extra columns to demonstrate expression evaluation *)
Definition q_all_nodes := MATCH -( "n" :: [] )-
                          RETURN <{ "n"["name"] }> AS "Name",
                                 <{ "n"["bornIn"] <> VNull }> AS "Is Person",
                                 <{ "n"["area"] = "education" }> AS "Is University",
                                 <{ "n"["bornIn"] = VNull && "n"["area"] = VNull }> AS "Is State".
Example q_all_nodes_ok :
  execute test_graph q_all_nodes = [
    [("Name", VStr "Alice"); ("Is Person", VBool true); ("Is University", VBool false); ("Is State", VBool false)];
    [("Name", VStr "Bob"); ("Is Person", VBool true); ("Is University", VBool false); ("Is State", VBool false)];
    [("Name", VStr "Charlie"); ("Is Person", VBool true); ("Is University", VBool false); ("Is State", VBool false)];
    [("Name", VStr "Google"); ("Is Person", VBool false); ("Is University", VBool false); ("Is State", VBool false)];
    [("Name", VStr "Microsoft"); ("Is Person", VBool false); ("Is University", VBool false); ("Is State", VBool false)];
    [("Name", VStr "University of Maryland"); ("Is Person", VBool false); ("Is University", VBool true); ("Is State", VBool false)];
    [("Name", VStr "University of Washington"); ("Is Person", VBool false); ("Is University", VBool true); ("Is State", VBool false)];
    [("Name", VStr "Washington"); ("Is Person", VBool false); ("Is University", VBool false); ("Is State", VBool true)];
    [("Name", VStr "New York"); ("Is Person", VBool false); ("Is University", VBool false); ("Is State", VBool true)];
    [("Name", VStr "Maryland"); ("Is Person", VBool false); ("Is University", VBool false); ("Is State", VBool true)]
  ].
Proof.
  reflexivity.
Qed.

(* Names and ages of all people  *)
Definition q_name_and_age := MATCH -( "p" :"person" [] )-
                             RETURN <{ "p"["name"] }> AS "Name",
                                    <{ 2022 - "p"["bornIn"] }> AS "Age".

Example q_name_and_age_ok : 
  execute test_graph q_name_and_age = [
    [("Name", VStr "Alice"); ("Age", VNum 27)];
    [("Name", VStr "Bob"); ("Age", VNum 23)];
    [("Name", VStr "Charlie"); ("Age", VNum 28)]
  ].
Proof.
  reflexivity.
Qed.

(* Names, workplaces, and years of work of married people *)
Definition q_workplace_of_married_people :=
  MATCH -( "p" :"person" [("marital status", VStr "married")] )- -[ "w" :"worksAt" [] ]-> -( "o" :"organization" [] )-
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
  MATCH -( :: [("name", VStr "Washington")] )- <-[ :"from":"locatesIn" [] ]- -( "n" :: [] )-
  RETURN <{ "n"["name"] }> AS "Name",
         <{ "n"["bornIn"] }> AS "Born In",
         <{ "n"["area"] }> AS "Area".

Example q_from_Washington_ok:
  execute test_graph q_from_Washington = [
    [("Name", VStr "University of Washington"); ("Area", VStr "education")];
    [("Name", VStr "Microsoft"); ("Area", VStr "technology")];
    [("Name", VStr "Charlie"); ("Born In", VNum 1994)]
  ].
Proof.
  reflexivity.
Qed.

(* People and the companies and the states they work in *)
Definition q_people_work_in_states :=
  MATCH -( "p" :"person" [] )- -[ "w" :"worksAt" [] ]- -( "o" :: [] )- -[ :"locatesIn" [] ]- -( "s" :: [] )-
  RETURN <{ "p"["name"] }> AS "Name",
         <{ "o"["name"] }> AS "Company",
         <{ "s"["name"] }> AS "State",
         <{ "w"["since"] }> AS "Since".

Example q_people_work_in_states_ok :
  execute test_graph q_people_work_in_states = [
    [("Name", VStr "Alice"); ("Company", VStr "Google"); ("State", VStr "New York"); ("Since", VNum 2018)];
    [("Name", VStr "Bob"); ("Company", VStr "Google"); ("State", VStr "New York"); ("Since", VNum 2020)];
    [("Name", VStr "Charlie"); ("Company", VStr "Microsoft"); ("State", VStr "Washington"); ("Since", VNum 2019)]
  ].
Proof.
  reflexivity.
Qed.

(* People who work in the state they are from. Note that the first and last node share the same name, which 
   dictates that they must match the same node. *)
Definition q_people_work_and_come_from_the_same_state :=
  MATCH -( "p" :"person" [] )- -[ :"worksAt" [] ]-> 
        -( :: [] )- -[ :"locatesIn" [] ]-> -( "s" :: [] )-
        <-[ :"from" [] ]- -( "p" :"person" [] )-
  RETURN <{ "p"["name"] }> AS "Name",
         <{ "s"["name"] }> AS "State".

Example q_people_work_and_come_from_the_same_state_ok :
  execute test_graph q_people_work_and_come_from_the_same_state = [
    [("Name", VStr "Bob"); ("State", VStr "New York")];
    [("Name", VStr "Charlie"); ("State", VStr "Washington")]
  ].
Proof.  
  reflexivity.
Qed.
