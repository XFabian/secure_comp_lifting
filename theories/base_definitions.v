Set Implicit Arguments.
Require Import Unicode.Utf8.
Require Import List.

Import ListNotations.

Require Import Program.Basics.
Open Scope program_scope.


Section comp.


Class UserLanguage := {
    Language: Type;
    Program : Type;
    Component : Type;
    Context : Type;
    link : Context -> Component -> Program;
    baseObs : Type;
    Taint : Type;
    is_safe_taint : Taint -> Prop;
    bTrace := list baseObs;
    btTrace := list (baseObs * Taint)%type;
}.


Context {userlang : UserLanguage}. 




Class Compilable (A : Type) := {
    compile : A -> A
}.

Context `{comp_comp : Compilable Component}.



Record Semantics (o : Type):= {
    Trace := list o;
    tObs := (o * Taint)%type;
    tTrace := list tObs;
    
    is_safe_obs := fun (t :tObs) => is_safe_taint (snd t);
    non_spec_proj : Trace -> bTrace;
    non_spec_proj_taint : tTrace -> btTrace;
    spec_proj : Trace -> Trace;
    spec_proj_taint : tTrace -> tTrace; 

    taint_proj := fun {A: Type}(x : list (A * Taint)) => map fst x;
    step : Program -> o -> Program -> Prop;
    tstep : Program -> tObs -> Program -> Prop;
    beh: Program -> Trace -> Prop;
    tbeh : Program -> tTrace -> Prop;

    (* Relationship to base Obs needs to be fulfilled
    The new obs does not "forget" observations *)
    
    b_inject : baseObs -> o;
    b_project : o -> option baseObs;
    bT_inject := fun T => map b_inject T;
    btT_inject := fun {B : Type} (T : list (baseObs * B)) => 
                    map (fun ot => (b_inject (fst ot), snd ot)) T;
    
    (* Relationship between base Obs and specObs, we do not lose information
    This is also the non-speculative projection *)
    inj_compatible : forall o, b_project (b_inject o) = Some o;

    trace_dec : forall (T1 T2 : tTrace), {T1 = T2} + {T1 <> T2};
     
    trace_exists : forall p, exists tT, tbeh p tT;
    
    beh_determinism : forall p T T', tbeh p T -> tbeh p T' -> T = T'

}.

(* Set Contextual Implicit. *)

Arguments tTrace : default implicits.

Arguments is_safe_obs : default implicits.

Arguments tbeh : default implicits.
Arguments non_spec_proj_taint : default implicits.
Arguments trace_dec : default implicits.
Arguments trace_exists : default implicits.
Arguments beh_determinism : default implicits.


Variable NS : Semantics baseObs.


Fixpoint is_safe {obs : Type} {X : Semantics obs} (T : tTrace X) := 
    match T with 
    | [] => True
    | x::xs => (X).(is_safe_obs) x /\ is_safe xs
    end.

Lemma equiv_is_safe_obs {obs1 obs2 : Type} (X: Semantics obs1) (Y : Semantics obs2): 
forall ox oy t, (X).(is_safe_obs) (ox, t) <-> (Y).(is_safe_obs) (oy, t).
Proof.
intros. split; unfold is_safe_obs; cbn; eauto.
Qed.

Parameter Policy : Type.
Parameter poly_sat : Policy -> Program -> Prop.
    
Definition low_equivalence (P : Policy) := fun s1 s2 : Program => poly_sat P s1 /\ poly_sat P s2.

Definition sni {obs : Type}(w : Program) (P : Policy) (G : @Semantics obs) := forall w', 
    low_equivalence P w w' /\ 
    forall T T', G.(tbeh) w T /\ G.(tbeh) w' T' /\
    G.(non_spec_proj_taint) T = G.(non_spec_proj_taint) T' ->
    T = T'.

Definition rsni {obs : Type} (P : Policy) (C : Component) (G : @Semantics obs) :=
    forall A : Context, sni (link A C) P G.

Definition rsnip {obs : Type} (compiler : Compilable Component) (P : Policy) (G : @Semantics obs) := forall p : Component,
    rsni P p NS -> rsni P ((compiler).(compile) p) G.

Definition ss  {obs : Type} (w : Program) (G : @Semantics obs) := 
    forall tT, G.(tbeh) w tT -> is_safe tT.

Definition rss {obs : Type} (C : Component) (G : @Semantics obs) := 
    forall A : Context, ss (link A C) G.

Definition rssp {Obs : Type} (compiler : Compilable Component) (G : @Semantics Obs) :=
    forall p : Component, rss p NS -> rss (compile p) G.


Class sec_comp_facts := {
    ns_rss : forall {NS' : @Semantics baseObs} p, rss p NS';
    rss_overapprox_rsni : forall {obs : Type} (G : @Semantics obs)
    (p : Component) (P : Policy), rss p G -> rsni P p G
}.


Definition leakage_order {obs1 obs2 : Type } (X1 : @Semantics obs1) 
(X2 : @Semantics obs2) := forall w w' T1 T1' T2 T2', 
X1.(tbeh) w T1 -> X1.(tbeh) w' T1' -> 
X2.(tbeh) w T2 -> X2.(tbeh) w' T2' -> T1 <> T1' -> T2 <> T2'.



Class leakage_facts := {
    non_spec_agree :
forall obs1 obs2  (X1 : @Semantics obs1) (X2 : @Semantics obs2) T T' T2 T2',
forall p p', X1.(tbeh) p T -> X1.(tbeh) p' T' -> X2.(tbeh) p T2 -> X2.(tbeh) p T2' ->
non_spec_proj_taint T = non_spec_proj_taint  T' 
<-> non_spec_proj_taint T2 = non_spec_proj_taint T2'
}.


Context (leak_facts : leakage_facts).


(* Contrapositive *)
Definition leakage_order4 {obs1 obs2 : Type } (X1 : @Semantics obs1) (X2 : @Semantics obs2) := forall w w'
 T1 T1' T2 T2', 
X1.(tbeh) w T1 -> X1.(tbeh) w' T1' -> 
X2.(tbeh) w T2 -> X2.(tbeh) w' T2' -> T2 = T2' -> T1 = T1'.


Lemma leak_eq : 
forall obs1 obs2 (X1 : @Semantics obs1) (X2 : @Semantics obs2), 
leakage_order X1 X2 <-> leakage_order4 X1 X2
.
Proof.
intros. split.
- intros H. intros w w' T1 T1' T2 T2'. unfold leakage_order in H.
specialize (H w w' T1 T1' T2 T2').
intros. specialize (H H0 H1 H2 H3). Print trace_dec.
destruct (trace_dec T1 T1').
    + auto.
    + specialize (H n). exfalso. intuition.
-  intros H. intros w w' T1 T1' T2 T2'. unfold leakage_order in H.
specialize (H w w' T1 T1' T2 T2').
intros. specialize (H H0 H1 H2 H3).
destruct (trace_dec T2 T2').
    + specialize (H e). exfalso. intuition.
    + auto.
Qed.

(* Theorem 2 in the paper *)
Theorem leakage_and_rsnip (comp : Compilable Component) (P : Policy) : 
∀ obs1 obs2 (X1 : @Semantics obs1) (X2 : @Semantics obs2),
rsnip comp P X2 -> leakage_order X1 X2 -> rsnip comp P X1 
.
Proof.
intros obs1 obs2 X1 X2 Hrsnip2 Hleak. intros C Hns A.
apply (leak_eq ) in Hleak.
specialize (Hleak (link A (compile C))). unfold sni.
intros. specialize (Hrsnip2 _ Hns). unfold rsni in Hrsnip2.
specialize (Hrsnip2 A). unfold sni in Hrsnip2. destruct (Hrsnip2 w') as 
(Hlow&Hr).
split; try auto.
intros.
destruct (trace_exists X2 (link A (compile C))) as [T2 H3].
destruct (trace_exists X2 w') as [T2' H4].

destruct H as (Hb1 & Hb2 & H5).
specialize (Hleak w' T T' T2 T2' Hb1 Hb2 H3 H4).
apply Hleak.
apply Hr.
repeat split; try auto.
eapply non_spec_agree. all: eauto.
Qed.

End comp.
(* Need that outside a section to take effect *)
Arguments tbeh : default implicits.
Arguments non_spec_proj_taint : default implicits.
Arguments trace_dec : default implicits.
Arguments tTrace : default implicits.
Arguments beh_determinism : default implicits.




Section comb.
Context {userlang : UserLanguage}. 
Context {NS : @Semantics userlang baseObs}.
Context {leak_facts : leakage_facts}.
Context {obsx obsy : Type}.
Variable (X : @Semantics _ obsx)
         (Y : @Semantics _ obsy).

(* Union of trace models which both rely on baseObs
Specified here but show that it fits to combined type specified by user
 *)
Inductive xyObs  :=
| xObs : obsx -> xyObs
| yObs : obsy -> xyObs
| startx 
| rlbx
| starty
| rlby
.
(* uObs is the Obs type defied by the user to instantiate the typeclass *)


Class Combination `(X : Semantics obsx) `(Y : Semantics obsy) 
(uObs : Type) `(XY : Semantics uObs):= 
{
    obs := xyObs;

    (* Relationship to NS_Semantics *)
    
    proj_pres_ns : forall p T, XY.(tbeh) p T -> 
                    (NS).(tbeh) p (XY.(non_spec_proj_taint) T);
    (* Relationship to base Semantics *)
    spec_proj_x : tTrace XY -> tTrace X;
    spec_proj_y : tTrace XY -> tTrace Y;

    spec_proj_safe_x : forall T, is_safe T -> is_safe (spec_proj_x T);
    spec_proj_safe_y : forall T, is_safe T -> is_safe (spec_proj_y T);
    proj_preservation_x : forall p T, XY.(tbeh) p T -> tbeh  p (spec_proj_x T);
    proj_preservation_y : forall p T, XY.(tbeh)  p T -> tbeh  p (spec_proj_y T);

    proj_preservation_x2 : forall p T, XY.(tbeh) p T = X.(tbeh) p (spec_proj_x T);
    proj_preservation_x3 : forall p T, XY.(tbeh) p T -> forall Tx, X.(tbeh) p Tx /\ Tx = spec_proj_x T;
    
    spec_proj_x_comm : forall (T : tTrace XY), (X).(spec_proj_taint) (spec_proj_x T) =
                                                  spec_proj_x  (XY.(spec_proj_taint) T);

    spec_proj_y_comm : forall (T : tTrace XY), (Y).(spec_proj_taint) (spec_proj_y T) =
                                                  spec_proj_y  (XY.(spec_proj_taint) T);

    (* Relationship obs and uobs *)
    encode : obs -> uObs;
    decode : uObs -> obs;
    (* Need to be isomorphic *)
    encode_decode : forall o, decode (encode o) = o /\ 
                    forall uo, encode (decode uo) = uo;
    (* This way taints are preserved and they obviously fulfill decode lemma*)
    encode_taint := fun (ot : obs * Taint) => (encode (fst ot), snd ot); 
    decode_taint := fun (ot : uObs * Taint) => (decode (fst ot), snd ot); 
   
    proj_pres_x : forall p Tx, X.(tbeh) p Tx -> exists Txy,
        XY.(tbeh) p Txy /\ spec_proj_x Txy = Tx;
    proj_pres_y : forall p Ty, Y.(tbeh) p Ty -> exists Txy,
        XY.(tbeh) p Txy /\ spec_proj_y Txy = Ty

}.


Variable uObs : Type.
Variable S_XY : @Semantics _ uObs.
Context {XY : Combination X Y S_XY}.


Lemma WFC_combination_and_leakage (XY1 : Combination X Y S_XY): 
leakage_order X S_XY /\ leakage_order Y S_XY.
Proof.
split.
- unfold leakage_order; intros. apply proj_pres_x in H.
 destruct H as (Txy&Hbxy&Hspecxy).
 apply proj_pres_x in H0.
 destruct H0 as (Txy'&Hbxy'&Hspecxy').
 intros Hex. apply H3. rewrite <- Hspecxy , <- Hspecxy'.
 pose (beh_determinism  w T2 Txy H1 Hbxy) as Heq.
 pose (beh_determinism  w' T2' Txy' H2 Hbxy') as Heq'.
 rewrite <- Heq, <- Heq'. f_equal. auto.
- unfold leakage_order; intros. apply proj_pres_y in H.
    destruct H as (Txy&Hbxy&Hspecxy).
    apply proj_pres_y in H0.
    destruct H0 as (Txy'&Hbxy'&Hspecxy').
    intros Hex. apply H3. rewrite <- Hspecxy , <- Hspecxy'.
    pose (beh_determinism  w T2 Txy H1 Hbxy) as Heq.
    pose (beh_determinism  w' T2' Txy' H2 Hbxy') as Heq'.
    rewrite <- Heq, <- Heq'. f_equal. auto.
Qed.


(* Corollary 1 *)
Corollary comb_compiler_contract_security (comp : Compilable Component): 
rssp NS comp S_XY -> rssp NS comp X /\ rssp NS comp Y.
Proof.
intros. unfold rssp in *. split; intros p Hns; specialize (H p Hns); clear Hns;
intros A tT Hb.
-  
  destruct (proj_pres_x (link A (compile p)) tT Hb) as [Txy [Hbxy Hspec]].
    specialize (H A Txy Hbxy).
    eapply spec_proj_safe_x in H. rewrite Hspec in H. auto.
- unfold rss in *. unfold ss in *.
destruct (proj_pres_y (link A (compile p)) tT Hb) as [Txy [Hbxy Hspec]].
  specialize (H A Txy Hbxy).
  eapply spec_proj_safe_y in H. rewrite Hspec in H. auto.
Qed.

(* Corollary 2 *)
Corollary comb_compiler_contract_security_negative 
(comp : Compilable Component): 
~ rssp NS comp X \/ ~ rssp NS comp Y -> ~ rssp NS comp S_XY.
Proof.
intros [H|H]; intros H1. 
- apply comb_compiler_contract_security in H1.
    destruct H1 as (Hx&Hy). intuition.
- apply comb_compiler_contract_security in H1.
    destruct H1 as (Hx&Hy). intuition.
Qed.


(* RSNIP versions. Not in paper. Only in TR. Corollary 9*)
Corollary comb_compiler_contract_security_sni (P : Policy) (comp : Compilable Component): 
rsnip NS comp P S_XY -> rsnip NS comp P X /\ rsnip NS comp P Y.
Proof.
intros. destruct (WFC_combination_and_leakage XY) as [Hx Hy]. split.
- eapply leakage_and_rsnip. apply leak_facts. apply H. apply Hx.
- eapply leakage_and_rsnip. apply leak_facts. apply H. apply Hy.
Qed.
(* Not in paper. Only in TR. Corollary 11 *)
Corollary comb_compiler_contract_security_sni_negative 
(P : Policy) (comp : Compilable Component): 
~ rsnip NS comp P X \/ ~rsnip NS comp P Y -> ~ rsnip NS comp P S_XY.
Proof.
intros [H |H ]; intros H1; apply comb_compiler_contract_security_sni in H1;
destruct H1 as (H2&H3); auto.
Qed.

End comb.


Arguments xyObs : default implicits.
Arguments Combination : default implicits.



