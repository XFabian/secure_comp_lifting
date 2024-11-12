Set Implicit Arguments.
Require Import meta.base_definitions.
Require Import Unicode.Utf8.
Require Import List.
Import ListNotations.

Section independence.

Context {userlang : UserLanguage}. 
Context {NS : Semantics baseObs}.
Context {s_facts : sec_comp_facts}.

(* TODO Coercions exists as well. For X and y elements into xy elements so I do not
need to type as much *)
Definition independence {Obs : Type} (compiler : Compilable Component)
 (Y : Semantics  Obs) :=
    forall p : Component, rss p Y -> rss (compile p) Y.

Corollary self_independence :
    forall comp obs (Y : @Semantics _ obs), rssp NS comp Y -> 
    independence comp Y.
Proof.
    intros. intros p H1. unfold rssp in *. apply H. apply (ns_rss).
Qed.


(* Syntactic Independence *)

Inductive InstructionName :=
| StoreN 
| LoadN
| BeqzN
| JmpN
| AssignN
.

Lemma eq_instrName : forall (x y : InstructionName), {x = y} + {x <> y}.
Proof.
decide equality.
Qed.

Require Import List.
Require Import ListSet.


Parameter emitted_instr_of_compiler : (Compilable Component) -> set InstructionName.
Parameter spec_instr : forall obs, (Semantics obs) -> set InstructionName.


Definition syn_independece {obs : Type} (sem : Semantics obs)(comp : Compilable Component) := 
set_inter eq_instrName (emitted_instr_of_compiler comp) (spec_instr sem) =
empty_set InstructionName
/\
set_inter eq_instrName (emitted_instr_of_compiler comp) ([StoreN; LoadN; BeqzN; JmpN; AssignN]) =
empty_set InstructionName 
.



(* No instructions are added that add more speculative behaviour 
This is currently not proven. Lemma 1 in the paper *)
Lemma syn_ind_ind {obs1 obs2 : Type} (comp : Compilable Component) (Sem : Semantics obs1) (SemA : Semantics obs2) : 
rssp NS (comp) SemA -> syn_independece Sem comp -> independence comp Sem.
Proof.
intros Hrssp H. unfold independence.
unfold rssp in *. unfold rss in Hrssp.
 intros p Hs. unfold rss in *. unfold ss in *.
Admitted.
End independence.


Section trapped.
Context {userlang : UserLanguage}. 
Context {NS : @Semantics _ baseObs}.
Context {s_facts : sec_comp_facts}.


(* Definition 11. 
Our defintion differs slightly here. The defintion in hte paper contains the
rlb observation. However, note that this rlb observation is always safe!
We assume here that the speculative projection filters the rlb observation out. *)
Definition trapped_speculation {obs : Type} 
        (X : Semantics obs)(comp : Compilable Component) := 
     forall w T Tse, (X).(tbeh) w T -> Tse = (X).(spec_proj_taint) T
     -> Tse = [].

End trapped.

Section Lifting.

Context {userlangNew : UserLanguage}. 
Context {NS : @Semantics userlangNew baseObs}.
Context {obsx obsy : Type}.
Variable (X : Semantics obsx)
         (Y : Semantics obsy)
         (uObs : Type)
         (S_XY : Semantics uObs).
Context `{XY : @Combination userlangNew NS obsx obsy X Y uObs S_XY}.

(* Definition 9 *)
Definition crssp (compiler : Compilable Component) :=
    forall p, rss p NS /\ rss p Y -> rss (compiler.(compile) p) (S_XY). 


Definition xyObsS := xyObs obsx obsy.
Identity Coercion xyObs_obs : xyObsS >-> xyObs.
Definition xyObs_to_uObs (o : xyObsS) :=
        encode (xyObs_obs o). 


Set Printing Coercions.
Definition subtrace {Obs : Type} {X : @Semantics _ Obs} (T T' : X.(tTrace)) :=
    exists Ts Ts', T = Ts ++ T' ++ Ts'.


Definition safe_nesting (p :Program):=
forall T Txy t t', (S_XY).(tbeh) p Txy -> T = (S_XY).(spec_proj_taint) Txy ->  (forall T' T'',
subtrace T ([( xyObs_to_uObs startx, t)] ++ T' ++ [(xyObs_to_uObs rlbx, t)]) /\ 
@subtrace uObs (S_XY) T' ([(xyObs_to_uObs starty, t')] ++ T'' ++ [(xyObs_to_uObs rlby, t')]) ->
@is_safe _ _ S_XY ([(xyObs_to_uObs starty, t')] ++ T'' ++ [(xyObs_to_uObs rlby, t')])) 
/\ 
(* Other nesting direction *)
(forall T' T'',
subtrace T ([( xyObs_to_uObs starty, t)] ++ T' ++ [(xyObs_to_uObs rlby, t)]) /\ 
@subtrace uObs (S_XY) T' ([(xyObs_to_uObs startx, t')] ++ T'' ++ [(xyObs_to_uObs rlbx, t')]) ->
@is_safe _ _ S_XY ([(xyObs_to_uObs startx, t')] ++ T'' ++ [(xyObs_to_uObs rlbx, t')])) 
.


Definition safe_nesting_comp (compiler : Compilable Component) :=
    forall C A, safe_nesting (link A (compiler.(compile) C)).


(* Lemma 2. Trapped speculation implies safe nesting *)
Lemma trapped_and_safe_nesting (compiler : Compilable Component):
trapped_speculation S_XY compiler -> safe_nesting_comp compiler
.
Proof.
intros Ht C A. unfold safe_nesting.
intros. specialize (Ht _ _ _ H H0).
rewrite Ht in H0. split; intros; destruct H1;
unfold subtrace in H1; destruct H1 as (T1&T2&H3); rewrite Ht in H3.
    - exfalso. eapply app_cons_not_nil.  eapply H3.
    - exfalso. eapply app_cons_not_nil.  eapply H3.
Qed.




(* Start and rollback observations are always safe, since they cannot leak secret information *)
(* And for starty and rlbs as well *)
Hypotheses startx_safe : 
forall p o T t, S_XY.(tbeh) p T -> In o T -> o = (xyObs_to_uObs startx, t) -> S_XY.(is_safe_obs) (o).

Hypotheses rlbx_safe : 
forall p o T t, S_XY.(tbeh) p T -> In o T -> o = (xyObs_to_uObs rlbx, t) -> S_XY.(is_safe_obs) (o).

Hypotheses starty_safe : 
forall p o T t, S_XY.(tbeh) p T -> In o T -> o = (xyObs_to_uObs starty, t) -> S_XY.(is_safe_obs) (o).

Hypotheses rlby_safe : 
forall p o T t, S_XY.(tbeh) p T -> In o T -> o = (xyObs_to_uObs rlby, t) -> S_XY.(is_safe_obs) (o).



(* Here we enforece a certain structure on the traces generated by the speculative semantics
This follows Fig.2 in the paper. *)

(* A trace action is either in the speculative projection or in the non-speculatie projection *)
Hypothesis non_spec_spec_proj_complete : 
forall t (T : (S_XY).(tTrace)), In t T -> 
(exists so tb, t = (so, snd t) /\ b_project (S_XY) so = Some tb /\ 
In (tb, snd t) ((S_XY).(non_spec_proj_taint) T))
\/
In t ((S_XY).(spec_proj_taint) T).

(* Non-speculative observations are always safe *)
Hypotheses non_spec_obs_safe :
forall obs (Z : Semantics obs) t T,
In (t) (Z.(non_spec_proj_taint) T) -> NS.(is_safe_obs) t.



Definition incl_in_x (T T': S_XY.(tTrace)) := forall o, 
In o T' -> exists o', o =  (xyObs_to_uObs (xObs o'), snd o) /\ In (o', snd o) (spec_proj_x T). 

Definition incl_in_y (T T': S_XY.(tTrace)) := forall o, 
In o T' -> exists o', o =  (xyObs_to_uObs (yObs o'), snd o) /\ In (o', snd o) (spec_proj_y T). 


Inductive trace_shapex (T : S_XY.(tTrace)) : Prop  :=
| trace_introx : (exists T' T'' T''' t,  
T = [(xyObs_to_uObs startx, t)] ++ T' ++ T'' ++ T''' ++ [(xyObs_to_uObs rlbx, t)]  /\ 
trace_shapey T'' /\
 incl_in_x T T' /\ incl_in_x T T''' )  -> 
 trace_shapex  T
with 
trace_shapey (T : S_XY.(tTrace)) : Prop  := 
| trace_introy : (exists T' T'' T''' t, 
  T = [(xyObs_to_uObs starty, t)] ++ T' ++ T'' ++ T''' ++ [ (xyObs_to_uObs rlby, t)]
  /\ trace_shapex T'' /\ incl_in_y T T' /\ incl_in_y T T''' )   -> 
  trace_shapey T
.

(* Here, we enforce the structure on the trace according to Figure 2. *)
Hypothesis trace_shape_fullfilled1 : 
forall p T T', (S_XY).(tbeh) p T -> T'= (S_XY).(spec_proj_taint) T -> trace_shapex T' \/ 
trace_shapey T' .


Lemma obs_in_safe_trace_are_safe :
forall {obs1 obs2 : Type} (Z : Semantics obs1) (Z1 : Semantics obs2)T t, is_safe T -> In t T -> (Z1).(is_safe_obs) t.
Proof.
intros. induction T. inversion H0. cbn in H. destruct H.
apply in_inv in H0 as [H0 | H0]. 
- rewrite <- H0. auto.
- apply IHT; auto.
Qed.

(* Projections remain safe. *)
Hypotheses proj_trace_safe : forall {obs : Type} (Z : Semantics obs) T,
(is_safe) T -> (is_safe) (Z.(spec_proj_taint) T).
Hypotheses obs_in_beh :
forall obs o (Z : Semantics obs) p T, Z.(tbeh) p T -> In o (spec_proj_taint T) -> In o T.



Require Import Coq.Program.Equality.

(* Helper Lemma for Lifting Theorem *)
Lemma shape_test :
forall p (T : S_XY.(tTrace)) (A : Context) (comp : Compilable Component), 
S_XY.(tbeh) (link A (compile p)) T ->
rss (compile p) X -> rss (compile p) Y -> safe_nesting_comp comp -> 
forall t, In t T -> (S_XY).(is_safe_obs) t.
Proof.
intros.
apply non_spec_spec_proj_complete in H3.
destruct H3.
- destruct H3 as (uo&bo&Heq&Hbp&Hin). Print b_project.
  rewrite Heq.  eapply (equiv_is_safe_obs S_XY NS). instantiate (1:= ( bo)).
  cbn. apply non_spec_obs_safe in Hin. auto.
- remember (S_XY.(spec_proj_taint) T) as T'.
specialize (@trace_shape_fullfilled1 _ T T' H). 
destruct trace_shape_fullfilled1.
+ subst T'. reflexivity.
+ inversion H4.
destruct H5 as (T'' &T''' &T''''&t'&H5&H6&H7&H8).
assert (Hin:  In t (spec_proj_taint T)). {rewrite <- HeqT'. auto. }
rewrite H5 in H3. 
repeat  (apply in_app_or in H3; destruct H3).
++ (* Start Obs should be safe *)
    apply in_inv in H3 as [H3 | H3]. 2: inversion H3.  eapply startx_safe; eauto.
++ (* Part of x observations. So rely on Rss of compiled program for X*) 
    unfold rss in H0. unfold ss in H0.
    pose (proj_preservation_x _ T H) as Hpx.
    specialize (H0 A _ Hpx). specialize (H7 t H3).
    destruct H7 as (o'&Hr&Hin2).
    rewrite HeqT' in Hin2.
    apply proj_trace_safe in H0.  rewrite Hr. cbn.
    eapply (equiv_is_safe_obs S_XY X).  instantiate (1:= ( o')).
    eapply obs_in_safe_trace_are_safe. 2: eapply H0. eauto.
    rewrite spec_proj_x_comm.
    eapply Hin2.
++ (* Nesting case   *)
    unfold safe_nesting_comp in H2. specialize (H2 p A).
    unfold safe_nesting in H2.
    inversion H6. 
    destruct H9 as (T2'' &T2''' &T2''''&t2'&H10&H11).
    specialize (H2 T' T t' t2' H HeqT'). destruct H2 as [H2 _]. 
    specialize (H2 (T'' ++ T''' ++ T'''')).
    specialize (H2 (T2'' ++ T2''' ++ T2'''')).
    (* eapply (equiv_is_safe_obs S_XY X).  instantiate (1:= ( o')). *)
    eapply obs_in_safe_trace_are_safe. 3: eapply H3. eauto.
    rewrite H10.  
    assert ([(xyObs_to_uObs starty, t2')] ++ (T2'' ++ T2''' ++ T2'''') ++ [(xyObs_to_uObs rlby, t2')] = [(xyObs_to_uObs starty, t2')] ++ T2'' ++ T2''' ++ T2'''' ++ [(xyObs_to_uObs rlby, t2')]).
    { cbn. repeat rewrite <- app_assoc. reflexivity. }
    rewrite <- H9.
    apply H2. split.
    +++ unfold subtrace. exists [], []; cbn.
    rewrite app_nil_r. rewrite H5. cbn. repeat rewrite app_assoc. reflexivity.
    +++ unfold subtrace. exists T'', T''''.
    Search [app eq].  rewrite  H9, <- H10. reflexivity.
++  (* Part of x observation. Exact as above *)
    pose (proj_preservation_x _ T H) as Hpx.
    specialize (H0 A _ Hpx). specialize (H8 t H3).
    destruct H8 as (o'&Hr&Hin2).
    rewrite HeqT' in Hin2.
    apply proj_trace_safe in H0.  rewrite Hr. cbn.
    eapply (equiv_is_safe_obs S_XY X).  instantiate (1:= ( o')).
    eapply obs_in_safe_trace_are_safe. 2: eapply H0. eauto.
    rewrite spec_proj_x_comm.
    eapply Hin2.

++ (* rlbx observation, which is always safe*)  
   apply in_inv in H3 as [H3 | H3]. 2: inversion H3.  eapply rlbx_safe; eauto.
+ (* Should be analogous to above Just in y *)
    inversion H4.
    destruct H5 as (T'' &T''' &T''''&t'&H5&H6&H7&H8).
    assert (Hin:  In t (spec_proj_taint T)). {rewrite <- HeqT'. auto. }
    rewrite H5 in H3. 
    repeat  (apply in_app_or in H3; destruct H3).
    ++ (* Starty Obs*)
        apply in_inv in H3 as [H3 | H3]. 2: inversion H3.  eapply starty_safe; eauto.
    ++ (* Part of y Observeration*)
        unfold rss in H1. unfold ss in H1.
        pose (proj_preservation_y _ T H) as Hpy.
        specialize (H1 A _ Hpy). specialize (H7 t H3).
        destruct H7 as (o'&Hr&Hin2).
        rewrite HeqT' in Hin2.
        apply proj_trace_safe in H1.  rewrite Hr. cbn.
        eapply (equiv_is_safe_obs S_XY Y).  instantiate (1:= ( o')).
        eapply obs_in_safe_trace_are_safe. 2: eapply H1. eauto.
        rewrite spec_proj_y_comm.
        eapply Hin2.
    ++ (* Nesting. Same as above*)
        specialize (H2 p A).
        unfold safe_nesting in H2.
        inversion H6. 
        destruct H9 as (T2'' &T2''' &T2''''&t2'&H10&H11).
        specialize (H2 T' T t' t2' H HeqT'). destruct H2 as [_ H2].
        specialize  (H2 (T'' ++ T''' ++ T'''')).
        specialize (H2 (T2'' ++ T2''' ++ T2'''')).
        (* eapply (equiv_is_safe_obs S_XY X).  instantiate (1:= ( o')). *)
        eapply obs_in_safe_trace_are_safe. 3: eapply H3. eauto.
        rewrite H10.  
        assert ([(xyObs_to_uObs startx, t2')] ++ (T2'' ++ T2''' ++ T2'''') ++ [(xyObs_to_uObs rlbx, t2')] = [(xyObs_to_uObs startx, t2')] ++ T2'' ++ T2''' ++ T2'''' ++ [(xyObs_to_uObs rlbx, t2')]).
        { cbn. repeat rewrite <- app_assoc. reflexivity. }
        rewrite <- H9.
        apply H2. split.
        +++ unfold subtrace. exists [], []; cbn.
        rewrite app_nil_r. rewrite H5. cbn. repeat rewrite app_assoc. reflexivity.
        +++ unfold subtrace. exists T'', T''''.
        Search [app eq].  rewrite  H9, <- H10. reflexivity.
    ++ (* Part of y Observation. Same as above *)
        pose (proj_preservation_y _ T H) as Hpy.
        specialize (H1 A _ Hpy). specialize (H8 t H3).
        destruct H8 as (o'&Hr&Hin2).
        rewrite HeqT' in Hin2.
        apply proj_trace_safe in H1.  rewrite Hr. cbn.
        eapply (equiv_is_safe_obs S_XY Y).  instantiate (1:= ( o')).
        eapply obs_in_safe_trace_are_safe. 2: eapply H1. eauto.
        rewrite spec_proj_y_comm.
        eapply Hin2.
    ++ (* rlby obs*)
        apply in_inv in H3 as [H3 | H3]. 2: inversion H3.  eapply rlby_safe; eauto.
Qed.



Lemma is_safe_equiv : 
forall T, (forall t, In t T -> (S_XY).(is_safe_obs) t) <-> is_safe T.
Proof.
intros. split.
- induction T; cbn; intros; eauto.
    split.
    + apply H. now left.
    + apply IHT. intros. apply H. now right.
- induction T; cbn; intros.
    + inversion H0.
    + destruct H. destruct H0.
        ++ rewrite <-  H0. auto.
        ++ apply IHT; eauto.
Qed.

(* Theorem 4. Note that the prove follows the description *)
Theorem lift_comp_preservation `(compiler : (Compilable Component)): 
    @rssp _ NS obsx (compiler) X /\ safe_nesting_comp (compiler) /\ independence (compiler) Y ->
     crssp (compiler). 
 Proof.
     intros (Hrssp&Hsn&Hind). unfold rssp in Hrssp. unfold independence in Hind. intros p.
     intros (Hns& Hrss).
     (* Collect what we know *)
     specialize (Hind p Hrss).
     specialize (Hrssp p Hns).
     unfold rss. intros A. 
     unfold ss. intros.
     rewrite <- is_safe_equiv.
     eapply shape_test.
     - apply H. 
     - auto.
     - apply Hind.
     - apply Hsn.
 Qed.

End Lifting.