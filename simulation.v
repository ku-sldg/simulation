(******************************
    Looking into the following simulations relations 
    - Bisimulation 
    - Weak Bisimulation 
    - Branching Bisimulation 
    
    By: Anna Fritz
    Date: August 2, 2023 *)

Require Import Coq.Relations.Relation_Definitions.
Require Import Coq.Relations.Relation_Operators.
Require Import Coq.Classes.RelationClasses.
Set Implicit Arguments.

Context {label L : Set}. 

Hypothesis eqL_dec : forall a b : L, {a = b} + {a <> b}.

(* First, define Labeled Transition System
 * Given a set of states and labels, 
 * define a transition relation and initial state.
 * A label may either be a label or the silent label.  *)
(*
Record LTS (state : Type) : Type := {
    initial : state;
    step : state -> label -> state -> Prop 
}.

Check LTS.
(* Check LTS.(step). *)

Definition relation (X : Type) := X -> X -> Prop.

(* bisimilarity relation for two states 
* type of this relation should be state -> state -> Prop *)
Definition BR_state {state} (sys : LTS state) (R: relation state) : Prop := 
    forall q p, R q p /\ forall l q', (sys.(step) q l q') -> 
    (exists p', (sys.(step) p l p') /\ R q' p').

(* simulation is one way *)
Definition simulation {state} (S1 S2 : LTS state) (R : relation state) : Prop := 
    forall q p, R q p /\ forall q' l, S1.(step) q l q' -> 
    exists p', (S2.(step) p l p') /\ R q' p'.

(* strong bisimulation is two way *)
Definition bisimulation {state1 state2} (S1: LTS state1) (S2: LTS state2) (R : state1 -> state2 -> Prop) : Prop := 
    R S1.(initial) S2.(initial) /\
    ( forall q p, R q p /\ forall q' l, S1.(step) q l q' -> 
    exists p', (S2.(step) p l p') /\ R q' p' ) /\
    ( forall q p, R q p /\ forall p' l, S2.(step) p l p' -> 
    exists q', (S1.(step) q l q') /\ R q' p').

*) 
(* Redefine Label transition system to include silent labels *)

Inductive sl := 
| silentlabel.

Record LTS : Type := {
    st : Set ; 
    initial : st -> Prop ; 
    step : st -> st -> Prop ;
    l : st -> L + sl
  }.

(* the transitive reflexive closure of silent transitions *)
Inductive silentstar (lts : LTS) : lts.(st) -> lts.(st) -> Prop := 
| star_refl : forall (s : lts.(st)), silentstar lts s s
| star_trans : forall (s s' s'' : lts.(st)), lts.(step) s s' -> 
                lts.(l) s = inr silentlabel -> 
                silentstar lts s' s'' ->  silentstar lts s s''.

Inductive silentplus (lts : LTS) : lts.(st) -> lts.(st) -> Prop :=
| plus_step : forall a (s s' : lts.(st)), 
                lts.(step) s s' -> 
                lts.(l) s = inr silentlabel -> 
                lts.(l) s' = inl a -> 
                silentplus lts s s'
| plus_trans : forall (s s' s'' : lts.(st)), 
                lts.(step) s s' -> 
                lts.(l) s = inr silentlabel -> 
                lts.(l) s' = inr silentlabel ->
                silentplus lts s' s'' -> 
                silentplus lts s s''.


Lemma silentstar_transitive : forall LTS s1 s2,
  silentstar LTS s1 s2 ->
  forall s3, silentstar LTS s2 s3 ->
  silentstar LTS s1 s3.
Proof.
  intros LTS s1 s2 H12. induction H12.
  - auto.
  - intros s3 H23. apply IHsilentstar in H23. 
    econstructor; eauto.
Qed.



Lemma silentstar_steplast : forall LTS sil lab a, 
  silentstar LTS sil lab ->
  LTS.(l) sil = inr silentlabel ->
  LTS.(l) lab = inl a ->
  exists int, silentstar LTS sil int /\ LTS.(l) int = inr silentlabel /\ LTS.(step) int lab.
Proof.
  intros LTS sil lab a HStar HSil HLab. induction HStar.

    (* base case *)
  - rewrite HSil in HLab. inversion HLab.

    (* inductive case *)
  - destruct (l LTS s') as [b|] eqn:Heq.

     (* s' is labeled *)
  -- destruct (eqL_dec a b).

      (* s' and s'' have same label *)
  --- inversion HStar; subst.
  ---- exists s. repeat split; [constructor| | ]; assumption.
  ---- rewrite Heq in H2. inversion H2.

      (* s' and s'' have different labels *)
  --- inversion HStar; subst.
  ---- rewrite Heq in HLab. inversion HLab. symmetry in H2. contradiction.
  ---- rewrite Heq in H2. inversion H2.

     (* s' is silent *)
  -- destruct s0. intuition. destruct H2 as [int H2].
     destruct H2 as [HStar' H2].
     destruct H2 as [HLab' HStep'].
     exists int. repeat split.
  --- apply star_trans with (s':=s'); assumption.
  --- assumption.
  --- assumption.
Qed.


Lemma silentstar_stepfirst : forall LTS sil lab a,
  silentstar LTS sil lab ->
  LTS.(l) sil = inr silentlabel ->
  LTS.(l) lab = inl a ->
 (LTS.(step) sil lab) \/ (exists int, LTS.(step) sil int /\ LTS.(l) int = inr silentlabel /\ silentstar LTS int lab).
Proof.
  intros LTS sil lab a HStar HSil HLab. destruct HStar.
  - rewrite HSil in HLab. inversion HLab.
  - destruct (l LTS s') as [b|] eqn:Heq.
  -- destruct (eqL_dec a b).
  --- inversion HStar; subst.
  ---- left. assumption.
  ---- rewrite Heq in H2. inversion H2.
  --- inversion HStar; subst.
  ---- rewrite Heq in HLab. inversion HLab. symmetry in H2. contradiction.
  ---- rewrite Heq in H2. inversion H2.
  -- destruct s0. right. exists s'. repeat split; assumption.
Defined.


Lemma silentstar_silentplus : forall LTS sil lab a,
  silentstar LTS sil lab ->
  LTS.(l) sil = inr silentlabel ->
  LTS.(l) lab = inl a ->
  silentplus LTS sil lab.
Proof.
  intros LTS sil lab a HStar HSil HLab. induction HStar.
  - rewrite HSil in HLab. inversion HLab.
  - destruct (l LTS s') as [b|] eqn:Heq.
  -- destruct (eqL_dec a b).
  --- inversion HStar; subst.
  ---- apply plus_step with (a:=b); assumption.
  ---- rewrite Heq in H2. inversion H2.
  --- inversion HStar; subst.
  ---- rewrite Heq in HLab. inversion HLab. symmetry in H2. contradiction.
  ---- rewrite Heq in H2. inversion H2.
  -- destruct s0. apply plus_trans with (s':=s'); try assumption.
     apply IHHStar. reflexivity. assumption.
Defined.

Lemma silentplus_silentstar: forall LTS s s',
  silentplus LTS s s' ->
  silentstar LTS s s'.
Proof.
  intros LTS s s' H.
  induction H.
  - eapply star_trans; eauto. constructor.
  - eapply star_trans; eauto.
Qed.


(* Defining a weak simulation. This is a one-way relation between two LTS'.
 * There are three cases.  *)
Definition weakSimulation (S1 S2 : LTS) (R: S1.(st) -> S2.(st) -> Prop) := 
    (* initial condition. All start states in one graph must be present in the other. *)
    (forall (p : S1.(st)), S1.(initial) p -> 
    (exists (q : S2.(st)), S2.(initial) q /\ R p q /\ S1.(l) p = S2.(l) q) 
    \/
    (exists (q : S2.(st)), S2.(initial) q /\ R p q /\ S2.(l) q = inr silentlabel /\ exists q', silentstar S2 q q' /\ S1.(l) p = S2.(l) q')) /\ 

    (* if there is a silent step in S1 then there exists some related silent step in S2 *)
    (forall p q, R p q -> forall p', S1.(step) p p' /\ S1.(l) p = inr silentlabel  -> 
     exists q', silentstar S2 q q' /\ R p' q' /\ S1.(l) p' = S2.(l) q') /\ 

    (* if there is some labeled step in S1 then there exists some labeled transition in S2 that may include silent states *)
    (forall p q, R p q -> forall p' a, S1.(step) p p' /\ S1.(l) p = inl a -> 
     exists q1 q2 q', silentstar S2 q q1 /\ S2.(step) q1 q2 /\ S2.(l) q1 = inl a /\ silentstar S2 q2 q' /\ R p' q' /\ S1.(l) p' = S2.(l) q').

(* use weak simulation as a partial order *)
Notation "x <= y" := (weakSimulation x y) (at level 70).



(* Prove that a weak simulation is reflexive *)
Lemma  WS_refl : forall x, exists r , (x <= x) r.
Proof.
(*
    intros.
    (* exists r : st x -> st x -> Prop, *) 
    exists eq.  
    unfold weakSimulation. split.
    + intros. exists p; eauto.
    + split.
    ++ intros. exists p'. split; eauto.
    +++ apply star_trans with (s' := p'); try (rewrite <- H; destruct H0 as [H0 H1]; eauto). apply star_refl.
    ++ intros. exists p. exists p'. exists p'; repeat split.
    +++ rewrite H. apply star_refl.
    +++ inversion H0; eauto.
    +++ inversion H0; eauto.
    +++ apply star_refl.         
Qed.
*)
Abort.


(* Inductive eq (A : Type) (x : A) : A -> Prop :=  eq_refl : x = x. *) 


Definition transitive {X: Type} (R: relation X) :=
  forall a b c : X, (R a b) -> (R b c) -> (R a c).



Inductive relation_comp {A B C : Type} (R1 : A -> B -> Prop ) (R2 : B -> C -> Prop ) : A -> C -> Prop :=
| rc : forall a b c, R1 a b -> R2 b c -> relation_comp R1 R2 a c.



Lemma  WB_trans : forall (x y z : LTS),       
                    ( exists r1, (x <= y) r1 ) -> 
                    ( exists r2, (y <= z) r2 ) -> 
                      exists r3, (x <= z) r3.
Proof. 
    intros.
    destruct H as [Rxy Hxy].
    destruct H0 as [Ryz Hyz].
    exists (relation_comp Rxy Ryz).
    unfold weakSimulation.
    destruct Hxy as [Hxy_initial Hxy].
    destruct Hxy as [Hxy_silent Hxy_ns].
    destruct Hyz as [Hyz_initial Hyz].
    destruct Hyz as [Hyz_silent Hyz_ns].
    repeat split.
    (* Weak Simulation Initial Clause *)
    + intros px HIni.
      apply Hxy_initial in HIni. destruct HIni.
      (* x and y same label *)
    ++ destruct H as [py H].
       destruct H as [HIni H].
       destruct H as [HRxy HLxy].
       apply Hyz_initial in HIni.
       destruct HIni.
       (* y and z same label *)
    +++ left. destruct H as [pz H].
        exists pz.
        destruct H as [HIni H].
        destruct H as [HRyz HLyz].
        repeat split.
    +++++ assumption.
    +++++ apply rc with (b:=py); assumption.
    +++++ rewrite HLxy. assumption.
       (* y and z silent label *)
    +++ destruct H as [pz H].
        destruct H as [HIni H].
        destruct H as [HRyz H].
        destruct H as [HLyz H].
        destruct H as [pz' H].
        destruct H as [HSil HLyz'].
        right.
        exists pz. repeat split.
    ++++ assumption.
    ++++ apply rc with (b:=py); assumption.
    ++++ assumption.
    ++++ exists pz'. split.
    +++++ assumption.
    +++++ rewrite HLxy. assumption.
      (* x and y silent label *)
    ++ destruct H as [py H].
       destruct H as [HIni H].
       destruct H as [HRxy H].
       destruct H as [HLxy H].
       destruct H as [py' H].
       destruct H as [HSil HLxy'].
       apply Hyz_initial in HIni. destruct HIni.
       (* y and z same label *)
    +++ right. destruct H as [pz H].
        exists pz.
        destruct H as [HIni H].
        destruct H as [HRyz HLyz].
        repeat split.
    ++++ assumption.
    ++++ apply rc with (b:=py); assumption.
    ++++ rewrite <- HLyz. assumption.
    (* HERE *)
    ++++ destruct (l y py') as [a|] eqn:Heq.
          (* py' is labeled *)
    +++++ assert (HPlus : silentplus y py py').
          { apply silentstar_silentplus with (a:=a); assumption. }
          clear HRxy HIni.
          generalize dependent pz.
          induction HPlus.
    ++++++ intros pz HRyz HLyz. apply Hyz_silent with (p':=s') in HRyz; try (split; assumption). 
           destruct HRyz as [pz' HRyz]. destruct HRyz as [HStar HRyz]. destruct HRyz as [HRyz HLyz']. 
           exists pz'. split. assumption.
           rewrite Heq in HLyz'. rewrite HLxy'. assumption.
    ++++++ intros pz HRyz HLyz. apply Hyz_silent with (p':=s') in HRyz; try (split; assumption).
           destruct HRyz as [int HRyz]. intuition.
           apply silentplus_silentstar in HPlus. intuition. 
           specialize H3 with int. intuition. 
           destruct H3 as [pz' H3]. destruct H3.
           exists pz'. split.
           apply silentstar_transitive with (s2:=int); assumption.
           assumption.
            (* py' is silent *)
     +++++ destruct s. exists pz. split. constructor. rewrite HLxy'. rewrite <- HLyz. rewrite HLxy. reflexivity.
      (* y and z silent label*)
    +++ right. destruct H as [pz H]. destruct H as [HIni H]. destruct H as [HRyz H]. destruct H as [HLz H]. 
        destruct H as [pz'' H]. destruct H as [HStar HLyz'].
        exists pz. repeat split. 
    ++++ assumption.
    ++++  apply rc with (b:=py); assumption.
    ++++ assumption.
    ++++ destruct (l y py') as [a|] eqn:Heq.
    +++++ assert (HPlus : silentplus y py py').
          { apply silentstar_silentplus with (a:=a); assumption. }
          clear HRxy HIni HStar HLyz'.
          generalize dependent pz. induction HPlus.
    ++++++ intros pz HRyz HLyz. apply Hyz_silent with (p':=s') in HRyz; try (split; assumption). destruct HRyz as [pz' HRyz].
           destruct HRyz as [HStar HRyz]. destruct HRyz as [HRyz HLsz']. exists pz'. split. assumption.
           rewrite Heq in HLsz'. rewrite HLxy'. assumption.
    ++++++ intros pz HRyz HLyz.
           apply Hyz_silent with (p':=s') in HRyz; try (split; assumption). destruct HRyz as [int HRyz]. intuition.
           apply silentplus_silentstar in HPlus. intuition. specialize H3 with int. intuition. 
           rewrite H1 in H5. symmetry in H5. intuition. destruct H3 as [pz' H3]. destruct H3.
           exists pz'. split.
           apply silentstar_transitive with (s2:=int); assumption.
          assumption.
    +++++ destruct s. exists pz. split. constructor. rewrite HLxy'. rewrite <- HLz. reflexivity.

    + admit.

    + admit.
    



(* need to define equal... and prove that it's an equivalence relation 
 * maybe isomorphism as equivalence ...?
 * Here: https://github.com/coq-contribs/ccs/blob/master/Trans_Sys.v 
 * different equivalence's are defined over transition systems  *)

Lemma WB_antisym : forall x y, 
                    ( exists r1, weakBisimulation x y r1 ) -> 
                    ( exists r2, weakBisimulation y x r2 ) -> 
                      x = y.

(* Three cases for graph comparison 
 * 1. <= /\ = -> = 
 * 2. <= /\ <> -> < 
 * 3. incomparable *)

(* Consider sets of graph comparison *)
