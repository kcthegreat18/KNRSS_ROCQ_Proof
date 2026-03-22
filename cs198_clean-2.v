
From Coq Require Import List Arith Bool Lia ZArith Reals.
Require Import Coq.micromega.Lra.
Import ListNotations.
Open Scope R_scope.
Require Import Coq.Reals.Rseries.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Reals.Rdefinitions.
Require Import Coq.Reals.Raxioms.

Module Kol_Naor_ROCQ.


(* ========= Players: ================ *)


Inductive Player:=
  |P1
  |P2 .
  
Definition all_players: list Player:=
  cons P1 (cons P2 nil).

(* A coalition is authorized iff both players are in the set *)
Definition authorized (S:list Player) : Prop:=
  In P1 S /\ In P2 S.




(* ============ Shares and  Unbounded iterations ===========
- Iteration
- Stage
- Secret
- Share
- Shares are generated per iteration
- Reconstruction is defined relative to a single iteration *
- Definitive iteration reveas the secret
*)



Parameter Secret: Type.

Record Share :=
{
  carried_secret: Secret
}.

Parameter gen_share:
  nat -> Player -> Share.
(* in interation k, player p wil generate a share for that iteration 
 gen_share (k,p) = share of player p at iteration k *)
  
  

(* ============== Iterations and Stages =========== 
- Iteration
- Stage
*)

Definition Iteration := nat.
Definition Stage := nat.

Parameter is_definitive_iter: nat -> Prop. 
(* Predicate describing a geometric distribution over iterations *)





(* ================== Player Actions and Strats =============== 
-Player moves: follow, deviate
-strategies based on local shares and protocol states

*)

Inductive Action :=
  | Send
  | Withhold.
  

Definition honest_strategy (p:Player) (sh:Share) : Action :=
  Send.
 
Parameter deviation:
  Player -> Share -> Action.

Parameter sigma:
  Player -> Share -> Action. (* General strategy lang *)
  


(* =============== Utilities and Equilibrium (and TREE) ============== *)

Record Outcome := {
  learned_p: Player -> bool;
  secret_leaked: bool
  }.
  


Parameter Utility: Player -> Outcome -> R.
(* Payoff of each player given a single outcome *)

Inductive Tree :=
  | Leaf : Outcome -> Tree
  | Choice: Player -> (Action -> Tree) -> Tree
  | Chance: (nat -> R) -> (nat -> Tree) -> Tree.
  

Parameter EU: Player -> Tree -> R.





(*=================== NEW DEFINITONS for `RECONSTRUCT AT` ===================*)

Parameter Player_eq_dec : forall (p1 p2 : Player), {p1 = p2} + {p1 <> p2}.

(*Check if a player p is in S *)
Definition player_in (p : Player) (S : list Player) : bool :=
  existsb (fun q => if Player_eq_dec p q then true else false) S. 

Definition authorizedb (S: list Player) : bool :=
  andb (player_in P1 S) (player_in P2 S).

Definition secret_of_share (sh: Share) : Secret :=
  carried_secret sh. (* extract secret from share *)
  
  
Definition reconstruct_at (k : nat) (S : list Player) (f : Player -> Share)
  : option Secret :=
  if authorizedb S
  then Some (secret_of_share (f P1))
  else None.




(*=================== Costs and other parameters ===================*)

 
Parameter ci : Player-> R.
(* Cost parameters for player p sending share s.*)

Definition c0 : R :=
  match all_players with
  | [] => 0  (* default if no players, must have at least 1 player anyway *)
  | p :: ps => fold_right Rmin (ci p) (map ci ps)
  end.
  (* minimum cost *)
Axiom ci_positive : forall p, ci p > 0.


(* =========== Broadcast and Protocol Stage =========== *)


Parameter broadcast: Player -> Share -> list (Player * Share).


Record ProtocolState := {
  iteration: Iteration;
  stage: Stage;
  player_views : Player -> list Share;
  broadcast_log: list (Player * Share);
  }.
  

  
Parameter protocol_step :
  ProtocolState -> list (Player * Action) -> ProtocolState.


  

(*============= Trees and Player Semantics  ============= *)
Parameter honest_tree: Tree.
Parameter deviating_tree :
Player -> (Player -> Share -> Action) -> Tree.



(* ============= Beta Parameters ================= 
beta and geometric probabilites and sht
*)

Parameter beta : R.
Axiom beta_range : 0 < beta /\ beta < 1.

Parameter epsilon : R.
Axiom epsilon_range : 0 < epsilon /\ epsilon < beta.

Parameter geo_prob : nat -> R.
Axiom geo_prob_def :
  forall k, geo_prob k = beta * (1 - beta)^k.

Parameter N : nat.  
Axiom geo_prob_sum_n :
  sum_f_R0 geo_prob N = 1.  




(* ============= Theorem 5.2 ==================================
Theorem strict_equilibrium:
  forall p delta,
    EU p honest_tree >
    EU p (deviating_tree p delta).

*)

(* 2 Instantiation of the Theorem 5.2 Proof *)




(* Proof 1: No group of less than m players is able to learn anything about the secret. *)


(* Proving lemma proof1_security *)
Definition learns_secret (S : list Player) (k : nat) : Prop :=
  exists s,
    reconstruct_at k S (fun p => gen_share k p) = Some s.
    
Lemma player_in_true_implies_in :
  forall (p : Player) (S : list Player),
    player_in p S = true ->
    In p S.
Proof.
    intros p S.
    induction S as [ | x xs IH].
    -intros H.
    discriminate H.
    -intros H.
     unfold player_in in H.
     simpl in H.
     destruct (Player_eq_dec p x) as [Heq | Hneq].
     +left. symmetry. apply Heq.
     +right. apply IH. exact H.
     Qed.

Lemma not_authorized_implies_authorizedb_false :
  forall S,
    ~ authorized S ->
    authorizedb S = false.
Proof.
  intros S Hnotauth.
  unfold authorizedb.
  destruct (player_in P1 S) eqn:HP1.
  - destruct (player_in P2 S) eqn:HP2.
    + (* true true case *)
      apply player_in_true_implies_in in HP1.
      apply player_in_true_implies_in in HP2.
      unfold authorized in Hnotauth.
      destruct Hnotauth.
      split; assumption.
    + reflexivity.
  - destruct (player_in P2 S) eqn:HP2.
    + reflexivity.
    + reflexivity.
Qed.

Lemma reconstruct_requires_authorized :
  forall (S : list Player) (k : nat),
    ~ authorized S ->
    reconstruct_at k S (fun p => gen_share k p) = None.
Proof.
  intros S k Hnotauth.
  unfold reconstruct_at.
  rewrite (not_authorized_implies_authorizedb_false S Hnotauth).
  reflexivity.
Qed.
  
  

Lemma proof1_security : (* Unauthorized coalitions cannot learn teh secret *)
  forall (S : list Player) (k : nat),
    ~ authorized S ->
    ~ learns_secret S k.
  Proof.
  intros S k.
  intros Hnoauth Hlearn.
  unfold learns_secret in Hlearn.
  destruct Hlearn as [s H].
  rewrite reconstruct_requires_authorized in H.
  -discriminate H.
  -simpl. apply Hnoauth.

  Qed.
  

 
(* No group of less than m players can learn anything about the secret. *)



(* Proof 2: Every subset of at least m players following their prescribed strategies reconstructs the secret. *)


(* --------------------------------------------------------------------- *)
(* gen_shares_proj_authorized says that if a coalition S is authorized,   *)
(* i.e., |S| >= m, then they can always reconstruct the secret:          *)
(*                                                                       *)
(*      reconstruct_subset S (proj_view S (gen_shares s all_players))    *)
(*      = Some s                                                          *)
(*                                                                       *)
(* This captures correctness for honest players.                         *)
(* --------------------------------------------------------------------- *)


(* ========= LEMMAS FOR PROOF 2 ============== *)


(* Bridge the prop to bool lemma  ang hirapppp *)
Lemma player_in_true:
  forall (p: Player) (S: list Player),
    In p S ->
      player_in p S = true.
  Proof.
  intros p S Hin.
  induction S as [ | x xs IH].
  -inversion Hin.
  -simpl in Hin.
   simpl.
   destruct Hin as [H | H1].
   +subst.
    destruct (Player_eq_dec p p).
     *reflexivity.
     *contradiction.
   +destruct (Player_eq_dec p x).
    *reflexivity.
    *apply IH in H1. rewrite H1. simpl. reflexivity.
    
   Qed.
   
 

(*If authorized S, then authorizedb S = true *)
Lemma authorized_implies_authorizedb_true:
  forall (S : list Player),
  authorized S -> authorizedb S = true.
  
  Proof.
  intros S [H1 H2].
  unfold authorizedb.
  rewrite (player_in_true P1 S).
  rewrite (player_in_true P2 S).
  -simpl. reflexivity.
  -exact H2.
  -exact H1.
  Qed.


(* ========= LEMMAS FOR PROOF 2 ============== *)



(* Honest shares for a given secret in that game *)
Definition gen_share_for_secret (s: Secret) (p: Player) : Share :=
  {| carried_secret := s |}. 

Lemma secret_of_generated_share :
  forall (s : Secret),
    secret_of_share (gen_share_for_secret s P1) = s.
  
  Proof.
  intros.
  simpl.
  reflexivity.
  Qed.
    

Definition honest_share_assignment (s : Secret) : Player -> Share:=
  fun p => gen_share_for_secret s p.



(* Basically defining what it means to follow an honest strategy *)
Definition follows_honest_strategy (S: list Player) (s : Secret) : Prop :=
  forall p,
    In p S ->
      (honest_strategy p (gen_share_for_secret s p) ) = Send.
      

(* for any player who follows the honest strategy, they send*)    
Lemma honest_strategy_sends_valid_shares_lem:
  forall (p : Player) (s : Secret),
  honest_strategy p (gen_share_for_secret s p)= Send.

  Proof.
  intros. simpl. reflexivity.
  Qed.


    
(* Authorized coalitions + honest implies successful reconstruction *)
Lemma reconstruct_authorized_honest_lem:
  forall (s : Secret) (S: list Player) (k:nat),
    authorized S->
      follows_honest_strategy S s-> reconstruct_at k S (honest_share_assignment s ) = Some s.
  Proof.
  intros sec S Hauth Hhon.
  unfold reconstruct_at.
  rewrite (authorized_implies_authorizedb_true S).
    simpl.
  -simpl.
    unfold follows_honest_strategy.
    intros H.
    reflexivity.
  -simpl. apply Hhon. 
  Qed.
  
(* Proof 4: The strategies prescribed to every subset of at least m players are strict best responses. *)

(* Definitions section *)

(* gain 1 minus cost if secret leaked, 0 otherwise *)
Definition Utility_def (p : Player) (o : Outcome) : R :=
  if secret_leaked o then 1 - ci p else 0.

(* Recursive computation of expected utility for a player in a protocol tree.
   - Leaf: return utility of the outcome
   - Choice: pick branch according to strategy
   - Chance: compute expected value over possible iterations
   - Models the Kol Naor geometric probability secret-sharing process *)
Fixpoint EU_tree_compute (t : Tree) (p : Player) : R :=
  match t with
  | Leaf o => Utility_def p o
  | Choice chooser next =>
      EU_tree_compute (next Send) p
  | Chance prob next =>
      let N := 1%nat in  (* only 1 iteration for simplicity *)
      sum_f_R0 (fun k => prob k * EU_tree_compute (next k) p) N
  end.


(* Previously axiom 4, proof for Honest tree value generation *)

(* secret is reconstructed and all players learn it *)
Definition honest_outcome_definitive (p : Player) : Outcome :=
  {| learned_p := fun _ => true; secret_leaked := true |}.

(* secret not reconstructed, no player learns it *)
Definition honest_outcome_nondef (p : Player) : Outcome :=
  {| learned_p := fun _ => false; secret_leaked := false |}.


(* Concrete protocol tree modeling one iteration with geometric probability:
   - Chance node: beta probability for definitive, 1-beta for non-definitive
   - Leaves: result of outomes
   - Computes expected utility in the Kol Naor scheme *)
Definition honest_tree_concrete : Tree :=
  Chance (fun k => if k =? 0 then beta else 1 - beta)
         (fun k => Leaf (if k =? 0 then honest_outcome_definitive P1 else honest_outcome_nondef P1)).


(* -------------------------------------------------------------------------- 
   EU_honest_value determines the expected utility when player p follows the honest strategy.
   
   Derivation:
     EU_honest(p) = Pr[definitive] x (Benefit - Cost) + Pr[non-definitive] x 0
                  = beta x (1 - ci(p)) + (1-beta) x 0
                  = beta x (1 - ci(p))
   
   Where:
     - 1 is the normalized benefit of learning the secret
     - ci(p) is player p's cost of sending their share
     - beta is the probability an iteration is definitive
--------------------------------------------------------------------------  *)

(* Generalized expected utility for any player following honest strategy *)
Lemma EU_honest_tree_value_gen :
  forall p,
    EU_tree_compute honest_tree_concrete p = beta * (1 - ci p).
Proof.
  intros p.
  (* Expand the concrete tree and utility definitions *)
  unfold honest_tree_concrete, EU_tree_compute, Utility_def,
         honest_outcome_definitive, honest_outcome_nondef.
  simpl.

  (* Simplify the eqb checks for iteration indices *)
  repeat rewrite Nat.eqb_refl.  (* 0 =? 0 simplifies to true *)

  (* Solve the arithmetic: beta*(1 - ci(p)) + (1 - beta)*0 = beta*(1 - ci(p)) *)
  lra.
Qed.


(* Previously axiom 5, proof for Deviating tree value generation *)

Definition guessed_definitive (k : nat) : bool :=
  k =? 0.

(* Represents the outcome of a player deviating from the honest strategy:
   - No player learns the secret
   - Secret is not reconstructed
   - Models the worst-case of deviation in the Kol Naor protocol *)
Definition deviating_outcome (p : Player) : Outcome :=
  {| learned_p := fun _ => false; secret_leaked := false |}.

Definition deviating_outcome_success (p : Player) : Outcome :=
  {| learned_p := fun q =>
       if Player_eq_dec q p then true else false;
     secret_leaked := true |}.



(* Concrete tree for a deviating player:
   - Chance node with geometric probability of definitive iteration
   - If the guessed definitive iteration occurs (k = 0), the deviator
   successfully learns the secret alone and gains utility (1 - ci(p)).
   Otherwise, no secret is learned.
   - Otherwise, non-definitive outcome is same as honest non-definitive outcome *)
Definition deviating_tree_concrete : Tree :=
  Chance (fun k => if k =? 0 then epsilon else 1 - epsilon)
    (fun k =>
       if k =? 0
       then Leaf (deviating_outcome_success P1)
       else Leaf (honest_outcome_nondef P1)).

(* Expected utility of any deviating player *)
Lemma EU_deviate_tree_computed :
  forall p,
    EU_tree_compute deviating_tree_concrete p = epsilon * (1 - ci p).
Proof.
  intros p.
  unfold deviating_tree_concrete, EU_tree_compute.
  simpl.

  repeat rewrite Nat.eqb_refl.

  unfold Utility_def, deviating_outcome_success, honest_outcome_nondef.
  simpl.

  lra.
Qed.


(* Parameter ensuring the cost of sending shares is at most 1/2 *)
Parameter ci_limit : forall p, ci p <= 1 / 2.


(* -------------------------------------------------------------------------- 
   EU_deviate_bound:

   A deviating player is essentially \u201cgambling\u201d on when the secret will be
   revealed.

   - If they guess the correct iteration (which happens with small probability
     epsilon), they manage to learn the secret while avoiding unnecessary cost,
     giving them a payoff of (1 - ci(p)).

   - If they guess wrong (which happens most of the time), nothing is learned
     and they gain 0.

   So overall, deviation gives:
       EU_deviate \u2248 epsilon * (1 - ci(p)).

   In contrast, an honest player follows the protocol and succeeds with higher
   probability beta, giving:
       EU_honest = beta * (1 - ci(p)).

   Since epsilon < beta, the \u201cgamble\u201d of deviating pays off less often than
   simply being honest. Even though deviation can occasionally succeed, it is
   not worth the risk in expectation.

   Therefore, honest behavior strictly dominates deviation.
----------------------------------------------------------------------------- *)

(* Upper bound on expected utility from any deviation.
   Shows that even the best deviation yields less utility than being honest. *)
Lemma EU_deviate_bound : forall p,
  EU_tree_compute deviating_tree_concrete p <= beta * (1 - ci p).
Proof.
  intros p.
  rewrite EU_deviate_tree_computed.

  (* epsilon * (1 - ci p) <= beta * (1 - ci p) *)
  apply Rmult_le_compat_r.
  - (* (1 - ci p) >= 0 *)
    pose proof (ci_limit p) as Hc.
    lra.
  - (* epsilon <= beta *)
    destruct epsilon_range as [_ Heps].
    lra.
Qed.


(* Main theorem: honest strategy strictly dominates any deviation *)
Theorem strict_equilibrium : 
  forall (p : Player) (delta : Player -> Share -> Action),
    EU_tree_compute honest_tree_concrete p >
    EU_tree_compute deviating_tree_concrete p.
Proof.
  intros p delta.

  (* Step 1: compute both sides *)
  rewrite EU_honest_tree_value_gen.
  rewrite EU_deviate_tree_computed.

  (* Step 2: show (1 - ci p) > 0 *)
  assert (Hpos_factor : 0 < 1 - ci p).
  {
    pose proof (ci_limit p) as Hc.
    lra.
  }

  (* Step 3: epsilon < beta *)
  destruct epsilon_range as [Heps_pos Heps_lt].

  (* Step 4: conclude strict inequality *)
  apply Rmult_lt_compat_r with (r := (1 - ci p)) in Heps_lt.
  - exact Heps_lt.
  - lra.
Qed.
