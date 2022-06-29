Require Import Classical.

(* symbol *)
Notation "∀ x .. y , P" := (forall x, .. (forall y, P) ..)
  (at level 200, x binder, y binder, right associativity,
  format "'[ ' '[ ' ∀ x .. y ']' , '/' P ']'") : type_scope.
Notation "∃ x .. y , P" := (exists x, .. (exists y, P) ..)
  (at level 200, x binder, y binder, right associativity,
  format "'[ ' '[ ' ∃ x .. y ']' , '/' P ']'") : type_scope.
Notation "'λ' x .. y , t" := (fun x => .. (fun y => t) ..)
  (at level 200, x binder, y binder, right associativity,
  format "'[ ' '[ ' 'λ' x .. y ']' , '/' t ']'").

Notation "x ∧ y" := (x /\ y)
  (at level 80, right associativity) : type_scope.
Notation "x ∨ y" := (x \/ y)
  (at level 85, right associativity) : type_scope.

Notation "x → y" := (x -> y)
  (at level 99, y at level 200, right associativity): type_scope.
Notation "x ↔ y" := (x <-> y) (at level 95, no associativity): type_scope.
Notation "x ≠ y" := (x <> y) (at level 70) : type_scope.

Ltac PreandH := match goal with H : ?a ∧ ?b |- _ => destruct H end.
Ltac andH := repeat PreandH.

Ltac PreandG := match goal with |- ?a ∧ ?b => split end.
Ltac andG := repeat PreandG.

Ltac PreorH := match goal with H : ?a ∨ ?b |- _ => destruct H end.
Ltac orH := repeat PreorH.

(* Some logic *)
(* Axiom classic : ∀ P, P ∨ ~P. *)
Ltac DC P := destruct (classic P).

Proposition NNPP : ∀ P, (~(~P) ↔ P).
Proof. intros; DC P; tauto. Qed.

Proposition inp : ∀ P Q : Prop, (P ↔ Q) → (~P → ~Q).
Proof. intros; intro. pose proof H1. elim H0. apply H; auto. Qed.

(* Class *)
Parameter Class : Type.

(* Two primitive(undefined) constants *)
Parameter In : Class → Class → Prop.
Notation "a ∈ A" := (In a A)(at level 70).
Notation "a ∉ A" := (~(a ∈ A))(at level 70).

Parameter Classifier : ∀ P : Class → Prop, Class.
Notation "\{ P \}" := (Classifier P)(at level 0).

(* Set theory *)
Axiom ExtAx : ∀ A B, (∀ x, x ∈ A ↔ x ∈ B) → A = B.
Ltac AppE := apply ExtAx; split; intros.

Definition Ensemble x := ∃ y, x ∈ y.
Ltac Ens := unfold Ensemble; eauto.
Ltac AssE x := assert (Ensemble x); Ens.

Axiom ClaAx : ∀ x P, x ∈ \{P\} ↔ Ensemble x ∧ P x.
Ltac AppCG := apply ClaAx; split; eauto.
Ltac AppC H := apply ClaAx in H as [_ H]; eauto.

Definition NoEmpty A := ∃ x, x ∈ A.
Notation "⦿ A" := (NoEmpty A) (at level 45).

Definition Empty := \{ λ x, x ≠ x \}.
Notation " ∅ " := Empty.

Fact EmptyNI : ∀ x, x ∉ ∅.
Proof. intros x H. AppC H. Qed.
Hint Resolve EmptyNI : Ens_hint.
Ltac exfalso0 := exfalso; eapply EmptyNI; eauto.

Fact EmptyEq : ∀ x, x = ∅ ↔ ~ (⦿ x).
Proof.
  split; intros. subst x. intros [x H]. exfalso0.
  AppE. elim H. exists x0; auto. exfalso0.
Qed.

Fact EmptyNE : ∀ x, x ≠ ∅ ↔ ⦿ x.
Proof.
  intros. pose proof EmptyEq. split; intros.
  apply (inp _ (~(⦿ x))) in H; auto. apply -> NNPP in H; auto.
  intro; apply H in H0; auto.
Qed.

Definition μ := \{ λ x, x = x \}.

Fact UniveI : ∀ x, Ensemble x → x ∈ μ.
Proof. intros. AppCG. Qed.
Hint Immediate UniveI : Ens_hint.

Ltac ens := auto with Ens_hint.
Ltac eens := eauto with Ens_hint.

Definition Singleton x := \{ λ z, x ∈ μ → z = x \}.
Notation "[ x ]" := (Singleton x) (at level 0, right associativity).

Fact SingI : ∀ x, Ensemble x → ∀ y, y = x → y ∈ [x].
Proof. intros. subst. AppCG. Qed.
Hint Resolve SingI : Ens_hint.

Fact SingE : ∀ x, Ensemble x → ∀ y, y ∈ [x] → y = x.
Proof. intros. AppC H0; ens. Qed.
Ltac sing H := apply SingE in H; try (subst; eauto).

Fact SingNI : ∀ x y, Ensemble y → x ≠ y → x ∉ [y].
Proof. intros * Hx Hn H. apply Hn. sing H. Qed.

Fact SingNE : ∀ x y, Ensemble x → y ∉ [x] → y ≠ x.
Proof. intros * Hx Hy Heq. apply Hy. ens. Qed.

Definition Included A B := ∀ x, x ∈ A → x ∈ B.
Notation "A ⊂ B" := (Included A B)(at level 70).

Axiom SubAx : ∀ x, Ensemble x → ∃ y, Ensemble y ∧ (∀z, z ⊂ x → z ∈ y).

Fact SubAxP : ∀ x, Ensemble x → ∀ z, z ⊂ x → Ensemble z.
Proof. intros. apply SubAx in H as [y []]. Ens. Qed.
Hint Resolve SubAxP : Ens_hint.

Fact IncRef : ∀ A, A ⊂ A.
Proof. intros * x; auto. Qed.

Fact IncAsym : ∀ A B, A ⊂ B → B ⊂ A → A = B.
Proof. intros. AppE; auto. Qed.

Fact IncTran : ∀ A B C, A ⊂ B → B ⊂ C → A ⊂ C.
Proof. intros * Ha Hb x Hx. auto. Qed.
Hint Resolve IncRef IncAsym IncTran : Ens_hint.

Definition PowerSet X := \{λ A, A ⊂ X \}.
Notation " cP( X )" := (PowerSet X)(at level 9, right associativity).

Fact PowerI : ∀ X, Ensemble X → ∀ Y, Y ⊂ X → Y ∈ cP(X).
Proof. intros. AppCG. eens. Qed.

Fact PowerE : ∀ X Y, Y ∈ cP(X) → Y ⊂ X.
Proof. intros. AppC H. Qed.
Ltac pow H := apply PowerE in H; eauto.

Fact PowerEns : ∀ X, Ensemble X → Ensemble cP(X).
Proof.
  intros. apply SubAx in H as [B [Hbe Hb]].
  assert (cP(X) ⊂ B). { intros z Hz. pow Hz. } eens.
Qed.
Hint Resolve PowerI PowerEns : Ens_hint.

Fact UniveEns : ~Ensemble μ.
Proof.
  set \{λ x, x ∉ x\} as R. assert (~Ensemble R).
  { DC (R ∈ R). pose proof H; AppC H. intro; elim H; AppCG. }
  assert (R ⊂ μ). intros z Hz. AssE z; ens. intro; eens.
Qed.

Fact SingEns : ∀ x, Ensemble x → Ensemble [x].
Proof.
  intros. assert ([x] ⊂ cP(x)). { intros z Hz. sing Hz. ens. }
  apply PowerEns in H; eens.
Qed.

Fact SingEns' : ∀ x, Ensemble [x] → Ensemble x.
Proof.
  intros. DC (Ensemble x); auto. assert ([x] = μ).
  { apply (inp _ (x ∈ μ)) in H0. AppE; AssE x0. ens. AppCG.
    intro; tauto. split; ens. intro; Ens. }
  rewrite H1 in H. pose proof UniveEns. tauto.
Qed.
Hint Resolve SingEns SingEns' : Ens_hint.

Definition Union A B := \{λ x, x ∈ A ∨ x ∈ B\}.
Notation "A ⋃ B" := (Union A B)(at level 65, right associativity).

Fact UnionI : ∀ x A, x ∈ A → ∀ B, x ∈ A ⋃ B.
Proof. intros. AppCG; Ens. Qed.

Fact UnionI' : ∀ x B, x ∈ B → ∀ A, x ∈ A ⋃ B.
Proof. intros. AppCG; Ens. Qed.
Hint Resolve UnionI UnionI' : Ens_hint.

Fact UnionE : ∀ x A B, x ∈ A ⋃ B → x ∈ A ∨ x ∈ B.
Proof. intros. AppC H. Qed.

Ltac PreunH := match goal with H : ?c ∈ ?a ⋃ ?b
  |- _ => apply UnionE in H as [] end.
Ltac unH := repeat PreunH.

Ltac PreunG := match goal with
  |- ?c ∈ ?a ⋃ ?b => apply UnionI end.
Ltac unG := repeat PreunG.

Fact UnionNE : ∀ x A B, x ∉ A ⋃ B → x ∉ A ∧ x ∉ B.
Proof. intros. split; intro; ens. Qed.

Fact UnionEns : ∀ x y, Ensemble (x ⋃ y) → Ensemble x ∧ Ensemble y.
Proof.
  intros. assert (x ⊂ x ⋃ y ∧ y ⊂ x ⋃ y).
  split; intros z Hz; ens. andH. split; eens.
Qed.

Axiom UnionAx : ∀ x y, Ensemble x → Ensemble y → Ensemble (x ⋃ y).
Axiom InfAx : ∃ y, Ensemble y ∧ ∅ ∈ y ∧ (∀ x, x ∈ y → (x ⋃ [x]) ∈ y).

Fact EmptyEns : Ensemble ∅.
Proof. destruct InfAx as [x [_ [He _]]]; Ens. Qed.
Hint Resolve EmptyEns UnionAx : Ens_hint.

Definition Inter A B := \{λ x, x ∈ A ∧ x ∈ B\}.
Notation "A ∩ B" := (Inter A B)(at level 60, right associativity).

Fact InterI : ∀ x A B, x ∈ A → x ∈ B → x ∈ A ∩ B.
Proof. intros. AppCG; Ens. Qed.
Hint Resolve InterI : Ens_hint.

Fact InterE : ∀ x A B, x ∈ A ∩ B → x ∈ A ∧ x ∈ B.
Proof. intros. AppC H. Qed.

Ltac PreinH := match goal with H : ?c ∈ ?a ∩ ?b
  |- _ => apply InterE in H as [] end.
Ltac inH := repeat PreinH.

Ltac PreinG := match goal with
  |- ?c ∈ ?a ∩ ?b => apply InterI end.
Ltac inG := repeat PreinG.

Axiom RegAx : ∀ x, x ≠ ∅ → ∃ y, y ∈ x ∧ x ∩ y = ∅.

Fact RegAxP : ∀ x, x ∉ x.
Proof.
  intros * Hp. AssE x. assert (x ∈ ([x] ∩ x)); ens. assert ([x] ≠ ∅).
  { apply EmptyNE. exists x; ens. } apply RegAx in H1 as [y []].
  sing H1. rewrite H2 in H0. exfalso0.
Qed.

Definition Setmin A B := \{λ x, x ∈ A ∧ x ∉ B\}.
Notation "A - B" := (Setmin A B).

Fact SetminI : ∀ x A B, x ∈ A → x ∉ B → x ∈ A - B.
Proof. intros. AppCG; Ens. Qed.
Hint Resolve SetminI : Ens_hint.

Fact SetminE : ∀ x A B, x ∈ A - B → x ∈ A ∧ x ∉ B.
Proof. intros. AppC H. Qed.

Ltac PresmH := match goal with H : ?c ∈ ?a - ?b
  |- _ => apply SetminE in H as [] end.
Ltac smH := repeat PresmH.

Ltac PresmG := match goal with
  |- ?c ∈ ?a - ?b => apply SetminI end.
Ltac smG := repeat PresmG.

Fact SetminSubI : ∀ A X, X - A ⊂ X.
Proof. intros * x Hx. smH; tauto. Qed.

Fact SetminSub2 : ∀ A B X, A ⊂ B → X - B ⊂ X - A.
Proof. intros * Hab z Hz. smH; ens. Qed.

Fact UnionSub : ∀ A B, B ⊂ A → A ⋃ B = A.
Proof. intros. AppE. unH; auto. ens. Qed.

Fact InterEqEmI : ∀ x U A, Ensemble x →
  U ∩ A - [x] = ∅ → x ∉ A → U ∩ A = ∅.
Proof.
  intros. assert (A - [x] = A). { AppE. smH; tauto.
  assert (x0 ∉ [x]). intro; sing H3. ens. } rewrite H2 in H0; auto.
Qed.

Fact InterSetmin : ∀ A B X, B ⊂ X → B ∩ X - A = ∅ → B ⊂ A.
Proof.
  intros * Hs Hp z Hz. assert (z ∉ X - A).
  { intro. assert (z ∈ B ∩ X - A); ens. rewrite Hp in H0; exfalso0. }
  DC(z ∈ A); auto. elim H; ens.
Qed.

Fact IdemU : ∀ A, A ⋃ A = A.
Proof. intros. AppE. unH; auto. ens. Qed.

Fact CommuU : ∀ A B, A ⋃ B = B ⋃ A.
Proof. intros. AppE; unH; ens. Qed.

Fact CommuI : ∀ A B, A ∩ B = B ∩ A.
Proof. intros. AppE; inH; ens. Qed.

Fact AssocU : ∀ A B C, (A ⋃ B) ⋃ C = A ⋃ (B ⋃ C).
Proof. intros. AppE; unH; ens. Qed.

Fact DistribuI : ∀ A B C, (A ⋃ B) ∩ C = (A ∩ C) ⋃ (B ∩ C).
Proof. intros. AppE. inH; unH; ens. unH; inH; ens. Qed.

Fact DistribuLI : ∀ A B C, A ∩ (B ⋃ C) = A ∩ B ⋃ A ∩ C.
Proof. intros. rewrite CommuI, DistribuI, CommuI, (CommuI A C); auto. Qed.

Fact EmptyU : ∀ A, A ⋃ ∅ = A.
Proof. intros. AppE. unH; auto. exfalso0. ens. Qed.

Fact TwoCompl : ∀ A X, A ⊂ X → X - (X - A) = A.
Proof.
  intros. AppE. smH. DC (x ∈ A); auto. elim H1; ens.
  smG; auto. intro; smH; auto.
Qed.

Definition EleU x := \{λ z, ∃ y, z ∈ y ∧ y ∈ x\}.
Notation "∪ x" := (EleU x)(at level 66).

Fact EleUI : ∀ x y z, x ∈ y → y ∈ z → x ∈ ∪z.
Proof. intros. AppCG; Ens. Qed.
Hint Resolve EleUI : Ens_hint.

Fact EleUE : ∀ x z, x ∈ ∪z → ∃ y, x ∈ y ∧ y ∈ z.
Proof. intros. AppC H. Qed.
Ltac eleU H := apply EleUE in H as [? []]; eauto.

Fact EleUSin : ∀ x, Ensemble x → ∪[x] = x.
Proof. intros. AppE. eleU H0; sing H1. eens. Qed.

Definition EleI x := \{λ z, ∀ y, y ∈ x → z ∈ y\}.
Notation "⋂ x" := (EleI x)(at level 66).

Fact EleISin : ∀ x, Ensemble x → ⋂[x] = x.
Proof.
  intros. AppE. AppC H0; apply H0; ens. AppCG; Ens. intros; sing H1.
Qed.
Hint Immediate EleUSin EleISin : Ens_hint.

Definition Unorder x y := [x] ⋃ [y].
Notation "[ x | y ] " := (Unorder x y) (at level 0).

Fact UnordEns : ∀ x y, Ensemble x → Ensemble y → Ensemble [x|y].
Proof. intros. unfold Unorder. ens. Qed.
Hint Resolve UnordEns : Ens_hint.

Fact unord1 : ∀ x y, Ensemble x → Ensemble y → ∪[x|y] = x ⋃ y.
Proof.
  intros. unfold Unorder. AppE. eleU H1; unH; sing H2; ens.
  unH; eapply EleUI; eauto; ens.
Qed.

Fact unord2 : ∀ x y, Ensemble x → Ensemble y → ⋂[x|y] = x ∩ y.
Proof.
  intros. unfold Unorder. AppE. AppC H1; ens.
  inH. AppCG; Ens. intros. unH; sing H3.
Qed.

Definition Order x y := [ [x] | [x | y] ].
Notation "[ x , y , .. , z ]" :=
  (Order .. (Order x y ) .. z ) (z at level 69).

Fact OrdEns : ∀ x y, Ensemble x → Ensemble y → Ensemble [x,y].
Proof. intros. unfold Order. ens. Qed.

Fact OrdEns0 : ∀ x y, Ensemble [x,y] → Ensemble x ∧ Ensemble y.
Proof.
  intros. apply UnionEns in H as [].
  apply SingEns', UnionEns in H0 as []; ens.
Qed.

Fact OrdEns1 : ∀ x y, Ensemble [x,y] → Ensemble x.
Proof. intros. apply OrdEns0 in H; tauto. Qed.

Fact OrdEns2 : ∀ x y, Ensemble [x,y] → Ensemble y.
Proof. intros. apply OrdEns0 in H; tauto. Qed.

Fact OrdEns3 : ∀ x y, Ensemble [x,y] → Ensemble [y,x].
Proof. intros. apply OrdEns0 in H as []. apply OrdEns; auto. Qed.
Hint Resolve OrdEns OrdEns3 : Ens_hint.

Ltac orde1 := match goal with H : Ensemble [?x,?y]
  |- Ensemble ?x => eapply OrdEns1; eauto end.
Ltac orde2 := match goal with H : Ensemble [?x,?y]
  |- Ensemble ?y => eapply OrdEns2; eauto end.
Ltac orde := try orde1; try orde2.

Fact ord1 : ∀ x y, Ensemble x → Ensemble y → ∪[x,y] = [x|y].
Proof.
  intros. unfold Order. rewrite unord1; ens.
  AppE; ens. unH; unfold Unorder; ens.
Qed.

Fact ord2 : ∀ x y, Ensemble x → Ensemble y → ⋂[x,y] = [x].
Proof.
  intros. unfold Order. rewrite unord2; ens.
  AppE. inH; auto. unfold Unorder; ens.
Qed.

Fact ord3 : ∀ x y, Ensemble x → Ensemble y → ∪(⋂[x,y]) = x.
Proof. intros. rewrite ord2; ens. Qed.

Fact ord4 : ∀ x y, Ensemble x → Ensemble y → ⋂(⋂[x,y]) = x.
Proof. intros. rewrite ord2; ens. Qed.

Fact ord5 : ∀ x y, Ensemble x → Ensemble y → ∪(∪[x,y]) = x ⋃ y.
Proof. intros. rewrite ord1, unord1; ens. Qed.

Fact ord6 : ∀ x y, Ensemble x → Ensemble y → ⋂(∪[x,y]) = x ∩ y.
Proof. intros. rewrite ord1, unord2; ens. Qed.

Definition π1 z := ⋂⋂z.
Definition π2 z := (⋂∪z)⋃(∪∪z)-(∪⋂z).

Fact ordFis : ∀ x y, Ensemble x → Ensemble y → π1 [x,y] = x.
Proof. intros. apply ord4; ens. Qed.

Fact ordSec : ∀ x y, Ensemble x → Ensemble y → π2 [x,y] = y.
Proof.
  intros. unfold π2. rewrite ord6, ord5, ord3; ens.
  assert ((x ⋃ y) - x = y - x). { AppE; smH; ens. unH. tauto. ens. }
  rewrite H1, CommuI. AppE; [|DC (x0 ∈ x); ens].
  unH. inH; auto. smH; auto.
Qed.
Hint Rewrite ordFis ordSec : ord_hint.
Ltac ordrewrite := autorewrite with ord_hint in *; try congruence.

Fact ordEq : ∀ x y a b, Ensemble x → Ensemble y →
  [x,y] = [a,b] ↔ x = a ∧ y = b.
Proof.
  split; intros; [|destruct H1; subst; auto]. assert (Ensemble [x,y]).
  eens. rewrite H1 in H2. apply OrdEns0 in H2 as [].
  rewrite <- (ordFis x y), H1, <- (ordSec x y), H1, ordFis, ordSec; auto.
Qed.

Fact ordNEq : ∀ x y a b, Ensemble x → Ensemble y →
  [x,y] ≠ [a,b] ↔ x ≠ a ∧ y ≠ b ∨ x ≠ a ∧ y = b ∨ x = a ∧ y ≠ b.
Proof.
  intros * Hx Hy. split; intro.
  - DC (x = a); [|DC (y = b); [right|]; left; auto]. right; right.
    andG; auto. intro. assert ([x,y] = [a,b]). subst; auto. auto.
  - orH; andH; intro; apply ordEq in H1; andH; auto.
Qed.

Notation " \{\ P \}\ " :=
  \{λ z, ∃ x y, z = [x,y] ∧ P x y \}(at level 0).
Ltac PP H a b := apply ClaAx in H as [_ [a [b [? H]]]]; subst; eauto.

Fact ClaAx' : ∀ x y P, [x,y] ∈ \{\P\}\ ↔ Ensemble [x,y] ∧ (P x y).
Proof.
  split; intros. AssE [x,y]. PP H a b. apply ordEq in H1 as []; orde.
  subst; auto. destruct H; AppCG; eauto.
Qed.
Ltac AppCG' := apply ClaAx'; split; eauto.
Ltac AppC' H := apply ClaAx' in H as [_ H]; eauto.

Definition Cartesian X Y := \{\ λ x y, x ∈ X ∧ y ∈ Y\}\.
Notation " X × Y " := (Cartesian X Y)(at level 2, right associativity).

Fact CProdI : ∀ A B a b, a ∈ A → b ∈ B → [a,b] ∈ A × B.
Proof. intros * Ha Hb. AppCG'. apply OrdEns; Ens. Qed.
Hint Resolve CProdI : Ens_hint.

Fact CProdE : ∀ A B a b, [a,b] ∈ A × B → a ∈ A ∧ b ∈ B.
Proof. intros. AppC' H. Qed.
Ltac cprod H := apply CProdE in H as []; eauto.

Definition Image A R := \{λ y, ∃ x, x ∈ A ∧ [x,y] ∈ R\}.
Notation "R \( A \) " := (Image A R)(at level 5).

Fact ImageI : ∀ x A, x ∈ A → ∀ y R, [x,y] ∈ R → y ∈ R\(A\).
Proof. intros. AssE [x,y]. AppCG; orde. Qed.
Hint Resolve ImageI : Ens_hint.

Fact ImageE : ∀ y A R, y ∈ R\(A\) → ∃ x, x ∈ A ∧ [x,y] ∈ R.
Proof. intros. AppC H. Qed.
Ltac image H := apply ImageE in H as [? []]; eauto.

Fact ImageSub : ∀ A B, A ⊂ B → ∀ R, R\(A\) ⊂ R\(B\).
Proof. intros * Hs * y Hy. image Hy; eens. Qed.

Definition OrigImage B R := \{λ x, ∃ y, y ∈ B ∧ [x,y] ∈ R\}.

Fact OriImI : ∀ y B, y ∈ B → ∀ x R, [x,y] ∈ R → x ∈ OrigImage B R.
Proof. intros. AssE [x,y]. AppCG; orde. Qed.
Hint Resolve OriImI : Ens_hint.

Fact OriImE : ∀ x B R, x ∈ OrigImage B R → ∃ y, y ∈ B ∧ [x,y] ∈ R.
Proof. intros. AppC H. Qed.
Ltac oriim H := apply OriImE in H as [? []]; eauto.

Fact OrigImageSub : ∀ A B, A ⊂ B → ∀ f, OrigImage A f ⊂ OrigImage B f.
Proof. intros * Hs * x Hx. oriim Hx. eens. Qed.

Definition Inverse R := \{\λ y x, [x,y] ∈ R \}\.
Notation "R ⁻¹" := (Inverse R)(at level 5).

Fact InverI : ∀ F x y, [x,y] ∈ F → [y,x] ∈ F⁻¹.
Proof. intros. AssE [x,y]. AppCG'; ens. Qed.
Hint Resolve InverI : Ens_hint.

Fact InverE : ∀ F x y, [y,x] ∈ F⁻¹ → [x,y] ∈ F.
Proof. intros. AppC' H. Qed.
Ltac inver H := apply InverE in H; eauto.

Definition Range R := \{λ y, ∃ x, [x,y] ∈ R\}.
Notation " ran( R )" := (Range R)(at level 5).

Fact ranI : ∀ R x y, [x,y] ∈ R → y ∈ ran(R).
Proof. intros. AssE [x,y]. AppCG; orde. Qed.
Hint Resolve ranI : Ens_hint.

Fact ranE : ∀ R y, y ∈ ran(R) → ∃ x, [x,y] ∈ R.
Proof. intros. AppC H. Qed.
Ltac ran H := apply ranE in H as [?]; eauto.

Definition Domain R := \{λ x, ∃ y, [x,y] ∈ R\}.
Notation " dom( R )" := (Domain R)(at level 5).

Fact domI : ∀ R x y, [x,y] ∈ R → x ∈ dom(R).
Proof. intros. AssE [x,y]. AppCG; orde. Qed.
Hint Resolve domI : Ens_hint.

Fact domE : ∀ R x, x ∈ dom(R) → ∃ y, [x, y] ∈ R.
Proof. intros. AppC H. Qed.
Ltac dom H := apply domE in H as [?]; eauto.

Fact domInv : ∀ R, dom(R⁻¹) = ran(R).
Proof.
  intros. AppE; [apply domE in H as [y Hp]|apply ranE in H as [w Hp]].
  apply InverE in Hp. eens. eens.
Qed.

Fact ranInv : ∀ R, ran(R⁻¹) = dom(R).
Proof. intros. AppE; [ran H|dom H]. inver H; eens. eens. Qed.

Fact dom_of_single_ord : ∀ a b,
  Ensemble a → Ensemble b → dom([[a,b]]) = [a].
Proof.
  intros. AppE. dom H1. sing H1; ens. symmetry in H1.
  apply ordEq in H1; auto; andH; ens. sing H1. eapply domI; ens.
Qed.

Fact ran_of_single_ord : ∀ a b,
  Ensemble a → Ensemble b → ran([[a,b]]) = [b].
Proof.
  intros. AppE. ran H1. sing H1; ens. symmetry in H1.
  apply ordEq in H1; auto; andH; ens. sing H1. eapply ranI; ens.
Qed.

Definition Composition R S : Class :=
  \{\ λ x z, ∃ y, [x,y] ∈ R ∧ [y,z] ∈ S \}\.
Notation "S ∘ R" := (Composition R S) (at level 50, no associativity).

Fact CompoI : ∀ R S x y t, [x,t] ∈ S → [t,y] ∈ R → [x,y] ∈ (R∘S).
Proof. intros. AssE [x,t]; AssE [t,y]. AppCG'. apply OrdEns; orde. Qed.
Hint Resolve CompoI : Ens_hint.

Fact CompoE : ∀ R S x y, [x,y] ∈ (R∘S) → ∃ t, [x,t] ∈ S ∧ [t,y] ∈ R.
Proof. intros. AppC' H. Qed.
Ltac compo H := apply CompoE in H as [? []]; eauto.

Fact CompoOrIm : ∀ R S B, OrigImage B (S∘R) = OrigImage (OrigImage B S) R.
Proof. intros. AppE; oriim H. compo H0; eens. oriim H; eens. Qed.

Definition IdenR X := \{\λ x y, x ∈ X ∧ y ∈ X ∧ x = y \}\.
Notation "∆ ( X )" := (IdenR X)(at level 5).

Fact IdentI : ∀ X a, a ∈ X → [a,a] ∈ ∆(X).
Proof. intros * Ha. AssE a. AppCG'; ens. Qed.
Hint Resolve IdentI : Ens_hint.

Fact IdentE : ∀ a b X, [a,b] ∈ ∆(X) → a ∈ X ∧ a = b.
Proof. intros. AppC' H; tauto. Qed.
Ltac ident H := apply IdentE in H as []; subst; eauto.

Fact IdentOri : ∀ U X, U ⊂ X → OrigImage U ∆(X) = U.
Proof. intros. AppE. oriim H0; ident H1. eens. Qed.

Definition Relation R X Y := R ⊂ X × Y.

Definition Mapping F X Y := Relation F X Y ∧
  (∀ x, x ∈ X → (∃ y, [x,y] ∈ F)) ∧
  (∀ x y1 y2, [x,y1] ∈ F → [x,y2] ∈ F → y1 = y2 ).

Definition Value F x := ⋂\{λ y, [x,y] ∈ F\}.
Notation "F [ x ]" := (Value F x)(at level 5).

Fact ValueP : ∀ f X Y, Mapping f X Y → ∀ x, x ∈ X → [x,f[x]] ∈ f.
Proof.
  intros * [Hr [He Hu]] * Hx. apply He in Hx as [y]. assert (y = f[x]).
  { AssE [x,y]. AppE. AppCG; Ens. intros; AppC H2. assert (y = y0).
    eapply Hu; eauto. subst; auto. AppC H1; apply H1; AppCG; orde. }
  subst; auto.
Qed.
Hint Resolve ValueP : Ens_hint.

Fact ValueP1 : ∀ f X Y, Mapping f X Y → ∀ x, x ∈ X → f[x] ∈ Y.
Proof. intros. assert ([x,f[x]] ∈ f). eens. apply H in H1. cprod H1. Qed.

Fact ValueP2 : ∀ f X Y,
  Mapping f X Y → ∀ x y, x ∈ X → [x,y] ∈ f → y = f[x].
Proof. intros. eapply H; eens. Qed.
Hint Resolve ValueP ValueP1 ValueP2 : Ens_hint.

Fact ValueIdenR : ∀ x X, x ∈ X → x = ∆(X)[x].
Proof.
  intros * Hx. AppE. AppCG; Ens. intros; AppC H0; ident H0.
  AppC H. apply H. AppCG; Ens. ens.
Qed.

Fact MapOri : ∀ f X Y, Mapping f X Y → ∀ B, OrigImage B f ⊂ X.
Proof. intros * Hf * x Hx. oriim Hx. apply Hf in H0. cprod H0. Qed.

Fact MapOriIm : ∀ B f X Y, Mapping f X Y → f\(OrigImage B f\) ⊂ B.
Proof.
  intros * Hf x Hx. image Hx. oriim H. assert (x = x1).
  eapply Hf; eauto. subst; auto.
Qed.

Fact MapOriSm : ∀ B f X Y, Mapping f X Y →
  OrigImage (Y - B) f = X - OrigImage B f.
Proof.
  intros * Hf. AppE.
  - oriim H. smH; smG. pose proof H0 as Hc. apply Hf in H0; cprod H0.
    intro. oriim H2. assert (x0 = x1). eapply Hf; eauto. subst; auto.
  - smH. eapply OriImI; [|eapply ValueP; eauto]. smG. eapply ValueP1;
    eauto. intro. elim H0. eapply OriImI; eauto. eapply ValueP; eauto.
Qed.

Fact MapDomSub : ∀ f X Y, Mapping f X Y →
  ∀ A, A ⊂ X → A ⊂ OrigImage f\(A\) f.
Proof. intros * Hf * Ha x Hx. eapply OriImI; eens. Qed.

Fact CompleOrIm : ∀ f X Y, Mapping f X Y → ∀ B, B ⊂ Y →
  OrigImage (Y - B) f = X - (OrigImage B f).
Proof.
  intros * Hf * Hb. AppE.
  - oriim H. assert (H0' := H0). apply Hf in H0. cprod H0. smG; auto.
    intro. oriim H2. assert (x0 = x1). eapply Hf; eauto. subst. smH; auto.
  - smH. assert ([x,f[x]] ∈ f); eens.
    assert (f[x] ∈ Y); eens. eapply OriImI; eens.
Qed.

Fact Mapping1 : ∀ F G X Y Z,
  Mapping F X Y → Mapping G Y Z → Relation (G∘F) X Z.
Proof.
  intros * Hf Hg c Hc. PP Hc x z; destruct Hc; andH.
  apply Hf in H; cprod H. apply Hg in H0; cprod H0. eens.
Qed.

Fact Mapping2 : ∀ F X Y, Mapping F X Y → dom(F) = X.
Proof. intros. AppE; eens. dom H0. apply H in H0. cprod H0. Qed.

Fact Mapping3 : ∀ F X Y, Mapping F X Y → ran(F) = F\(X\).
Proof.
  intros. AppE; [|image H0; eens]. ran H0. assert (x0 ∈ X).
  apply H in H0; cprod H0. eens.
Qed.

Fact IdenRelM : ∀ X, Mapping ∆(X) X X.
Proof.
  intros. repeat split; intros; eens. intros x Hx. PP Hx a b; andH; ens.
  AppC' H; AppC' H0; andH. subst; auto.
Qed.

Fact CompoMap : ∀ F G X Y Z,
  Mapping F X Y → Mapping G Y Z → Mapping (G ∘ F) X Z.
Proof.
  intros. repeat split; intros. eapply Mapping1; eauto.
  apply H in H1 as [y]; apply H in H1 as Hxy; cprod Hxy; eens. compo H1.
  compo H2. assert (x0 = x1). eapply H; eauto. subst. eapply H0; eauto.
Qed.

Theorem CompoMap' : ∀ F G X Y Z,
  Mapping F X Y → Mapping G Y Z → ∀ x, x ∈ X → (G ∘ F)[x] = G[F[x]].
Proof.
  intros. AppE; AppCG; Ens; intros; AppC H2. AppC H3. pose proof H3.
  apply H0 in H3; cprod H3. apply H2; AppCG; Ens; eens. AssE y. AppC H3.
  compo H3. assert (x1 = F[x]); eens. apply H2; AppCG; subst; auto.
Qed.

Definition FullM f X Y := Mapping f X Y ∧ f\(X\) = Y.
Definition MarkFamU φ Γ := \{λ x, ∃ γ, γ ∈ Γ ∧ x ∈ φ[γ]\}.
Definition MarkFamI φ Γ := \{λ x, ∀ γ, γ ∈ Γ → x ∈ φ[γ]\}.

Fact MarkFamEq : ∀ f Γ cA, FullM f Γ cA →
  MarkFamU f Γ = ∪cA ∧ MarkFamI f Γ = ⋂cA.
Proof.
  intros * [H Heq]. andG.
  - AppE; AppCG; Ens. AppC H0; destruct H0 as [n []];
    exists f[n]; andG; eens. eleU H0; rewrite <- Heq in H1; image H1.
    exists x1; andG; auto. erewrite <- ValueP2; eauto.
  - AppE; AppCG; Ens; AppC H0; intros. rewrite <- Heq in H1; image H1.
    apply H0 in H1 as Hx. erewrite ValueP2; eauto.
    apply H0; rewrite <- Heq; eens.
Qed.

(* Supplement *)
Definition exu (P : Class → Prop) :=
  (∃ x, P x) ∧ (∀ x y, P x → P y → x = y).
Notation "∃! x , P" := (exu (λ x, P)) (at level 200, x ident).

Definition is_relation R := ∀ z, z ∈ R → ∃ x y, z = [x,y].
Definition is_function F :=
  is_relation F ∧ ∀ x, x ∈ dom(F) → ∃! y, [x,y] ∈ F.

Fact func_ap : ∀ F x y, is_function F → [x,y] ∈ F → F[x] = y.
Proof.
  intros * Hf Hp. AssE [x,y]. AppE. AppC H0; apply H0; AppCG; orde.
  AppCG; Ens. intros. AppC H1. assert (y=y0).
  eapply Hf; eens. subst; auto.
Qed.

Fact func_dom : ∀ F x, is_function F → x ∈ dom(F) → [x,F[x]] ∈ F.
Proof.
  intros * Hf Hx. dom Hx. apply func_ap in H as Hap; auto. subst; auto.
Qed.
Hint Resolve func_ap func_dom : Ens_hint.

Fact sm_func : ∀ f g,
  is_function f → is_function g → is_function (f - g).
Proof.
  intros * Hf Hg. repeat split. intros z Hz; smH; apply Hf in H; auto.
  dom H. dom H; intros y1 y2 Hy1 Hy2; smH; eapply Hf; eens.
Qed.

Fact single_ord_is_func : ∀ a b,
  Ensemble a → Ensemble b → is_function ([[a,b]]).
Proof.
  intros. repeat split. intros x Hx; sing Hx; ens. dom H1.
  intros y1 y2 Hy1 Hy2. sing Hy1; ens. sing Hy2; ens.
  symmetry in Hy1, Hy2. apply ordEq in Hy1; auto.
  apply ordEq in Hy2; auto. andH. subst; auto.
Qed.

Definition single_rooted F := ∀ y, y ∈ ran(F) → ∃! x, [x,y] ∈ F.

Fact singrootE : ∀ F, single_rooted F → is_function F⁻¹.
Proof.
  intros. split; intros x Hx. PP Hx a b. split. dom Hx.
  intros. inver H0; inver H1. eapply H; eens.
Qed.

Fact inv_sr_iff_func : ∀ F,
  (is_relation F ∧ single_rooted F⁻¹) ↔ is_function F.
Proof.
  split; intros; split; try apply H. split. dom H0.
  intros; eapply H; eens. intros y Hy. ran Hy. split; eauto.
  intros. inver H1; inver H2. eapply H; eens.
Qed.

Definition injective F := is_function F ∧ single_rooted F.

Fact sm_injective : ∀ f g, injective f → injective g → injective (f - g).
Proof.
  intros * [Hf Hfs] [Hg Hgs]. split. apply sm_func; auto.
  intros y Hy. split. ran Hy. intros x1 x2 H1 H2; smH. eapply Hfs; eens.
Qed.

Fact single_ord_injective : ∀ a b,
  Ensemble a → Ensemble b → injective ([[a,b]]).
Proof.
  intros. split. apply single_ord_is_func; auto. split. ran H1.
  intros x1 x2 Hx1 Hx2. sing Hx1; ens.  sing Hx2; ens.
  symmetry in Hx1, Hx2. apply ordEq in Hx1; auto.
  apply ordEq in Hx2; auto. andH. subst; auto.
Qed.

Definition maps_into F A B := is_function F ∧ dom(F) = A ∧ ran(F) ⊂ B.
Notation "F : A => B" := (maps_into F A B) (at level 60).

Definition maps_onto F A B := is_function F ∧ dom(F) = A ∧ ran(F) = B.
Notation "F : A ==> B" := (maps_onto F A B) (at level 60).

Definition injection F A B :=
  injective F ∧ dom(F) = A ∧ ran(F) ⊂ B.
Notation "F : A <=> B" := (injection F A B) (at level 60).

Definition bijection F A B := injective F ∧ dom(F) = A ∧ ran(F) = B.
Notation "F : A <==> B" := (bijection F A B) (at level 60).

Corollary MapMapR : ∀ F A B, Mapping F A B → maps_into F A B.
Proof.
  intros; pose proof H as [Hr [He Ht]]. split; split. intros z Hz.
  apply H in Hz; PP Hz a b. intros; split. dom H0. intros; eens.
  eapply Mapping2; eauto. intros z Hz. ran Hz. apply H in H0. cprod H0.
Qed.

Corollary MapMapR1 : ∀ F A B, maps_into F A B → Mapping F A B.
Proof.
  intros; pose proof H as [Hr [He Ht]]. split. intros z Hz.
  pose proof Hz. apply Hr in Hz as [x [y Hz]]. subst; eens.
  split; intros. subst; dom H0. eapply Hr; eens.
Qed.

Fact bijection_is_func : ∀ F A B,
  bijection F A B ↔ maps_into F A B ∧ injective F ∧ ran(F) = B.
Proof.
  split. intros [Hi [Hd Hr]]. split; auto. destruct Hi.
  split; subst; ens. intros [[Hf [Hd _]] [Hi Hr]]. split; auto.
Qed.

Fact inv_bijection : ∀ F A B, bijection F A B → bijection F⁻¹ B A.
Proof.
  intros * [[Hf Hs] [Hd Hr]]. split; [| rewrite domInv, ranInv; auto].
  split. apply singrootE; auto. apply inv_sr_iff_func; auto.
Qed.

Fact single_ord_bijective : ∀ a b,
  Ensemble a → Ensemble b → bijection ([[a,b]]) ([a]) ([b]).
Proof.
  intros. split. apply single_ord_injective; auto. andG;
  [apply dom_of_single_ord|apply ran_of_single_ord]; auto.
Qed.

Fact func_sm_point : ∀ f A B a, maps_into f A B → a ∈ A →
  (∀ x, x ∈ A → x ≠ a → f[x] ≠ f[a]) →
  maps_into (f - [[a,f[a]]]) (A - [a]) (B - [f[a]]).
Proof.
  intros * [Hf [Hd Hr]] Ha Hp. assert (Hb : f[a] ∈ B).
  { apply Hr. subst. apply func_dom in Ha; eens. } AssE a; AssE f[a].
  rename H into Hae; rename H0 into Hbe.
  pose proof (single_ord_bijective a f[a] Hae Hbe) as [[Hf' _] [Hd' Hr']].
  assert (Hfs : is_function (f - [[a,f[a]]])).
  { apply sm_func; auto. } split; [|split]; auto.
  - AppE.
    + dom H. smH. smG. rewrite <- Hd; eens. apply SingNE in H0; ens.
      apply SingNI; auto. AssE [x,x0]; apply OrdEns0 in H1; andH.
      apply ordNEq in H0; auto. orH; andH; auto.
      apply func_ap in H; auto. subst; auto.
    + smH. apply SingNE in H0; auto. rewrite <- Hd in H; dom H.
      AssE [x,x0]; apply OrdEns0 in H1; andH. eapply domI. smG; eauto.
      apply SingNI; ens. apply ordNEq; auto. apply func_ap in H; auto.
      subst x0. DC (f[x] = f[a]); [right|]; left; auto.
  - intros y Hy. ran Hy. smH. smG. apply Hr; eens. apply SingNE in H0;
    ens. apply SingNI; auto. AssE [x,y]; apply OrdEns0 in H1; andH.
    apply func_ap in H as Hy; auto; subst y. apply ordNEq in H0; auto.
    orH; andH; auto. apply Hp; auto. subst; eens.
Qed.

Fact bijection_sm_point : ∀ f A B a, bijection f A B → a ∈ A →
  (∀ x, x ∈ A → x ≠ a → f[x] ≠ f[a]) →
  bijection (f - [[a,f[a]]]) (A - [a]) (B - [f[a]]).
Proof.
  intros * [Hf [Hd Hr]] Ha Hp. assert (Hb : f[a] ∈ B).
  { subst. apply func_dom in Ha; eens. apply Hf. } AssE a; AssE f[a].
  rename H into Hae; rename H0 into Hbe. assert (Hm : maps_into f A B).
  { split. apply Hf. andG; auto. rewrite Hr; ens. } pose proof
    (func_sm_point _ _ _ _ Hm Ha Hp) as [Hfu [Hud Hur]].
  pose proof (single_ord_bijective a f[a]) as [[Hs Hss] [Hsd Hsr]]; auto.
  split; [|andG]; auto. apply sm_injective; auto.
  apply single_ord_injective; auto.
  apply IncAsym; auto. intros y Hy.
  smH. rewrite <- Hr in H; ran H. apply SingNE in H0; ens. eapply ranI.
  smG; eauto. apply SingNI; ens. AssE [x,y]; apply OrdEns0 in H1; andH.
  apply ordNEq; auto. DC (x = a). right; right; auto. left; auto.
Qed.

(* natural number *)
Definition Suc n := n ⋃ [n].
Notation "n ⁺" := (Suc n) (at level 8).

Fact sucEns : ∀ n, Ensemble n → Ensemble n⁺.
Proof. intros. unfold Suc; ens. Qed.

Fact suc_has_n : ∀ n, Ensemble n → n ∈ n⁺.
Proof. intros. unfold Suc; ens. Qed.

Fact suc_inc_n : ∀ n, n ⊂ n⁺.
Proof. intros n x Hx. unfold Suc; ens. Qed.

Fact suc_neq_0 : ∀ n, Ensemble n → n⁺ ≠ ∅.
Proof.
  intros n Hn H. apply EmptyNE in H; auto.
  exists n. apply suc_has_n; auto.
Qed.
Hint Resolve sucEns suc_has_n suc_inc_n suc_neq_0 : Ens_hint.

Definition inductive A := ∅ ∈ A ∧ (∀ a, a ∈ A → a⁺ ∈ A).
Definition is_nat n := ∀ A, inductive A → n ∈ A.
Definition ω := \{λ n, is_nat n\}.

Fact ωEns : Ensemble ω.
Proof.
  destruct InfAx as [A [He Hp]]. assert (inductive A); auto.
  assert (ω ⊂ A). intros n Hn; AppC Hn. eens.
Qed.

Fact ω_has_0 : ∅ ∈ ω.
Proof. AppCG; ens. intros n []; auto. Qed.

Fact ω_has_suc : ∀ a, a ∈ ω → a⁺ ∈ ω.
Proof.
  intros. AssE a. AppC H. AppCG; ens. intros A Ha; apply Ha; auto.
Qed.
Hint Resolve ωEns ω_has_0 ω_has_suc : Ens_hint.

Fact ω_inductive : inductive ω.
Proof. split; ens. Qed.
Ltac ind := apply ω_inductive; eauto.

Fact ω_ind : ∀ A, A ⊂ ω → inductive A → A = ω.
Proof. intros. AppE; auto. AppC H1. Qed.

Ltac ω_induction n := pattern n;
  match goal with H : n ∈ ω |- ?G _ => let N := fresh "N" in
  set \{λ n, n ∈ ω ∧ G n\} as N; simpl in N; cut (N = ω);
  [intros ?Heq; rewrite <- Heq in H; AppC H; andH; auto|apply ω_ind;
    [intros ?t ?Ht; AppC Ht; andH; auto|split;
      [AppCG; [apply EmptyEns|]; split; [apply ω_has_0|]|]];
      [|intros ?k ?Hk; AppC Hk; destruct Hk as [?Hk ?IH]; AssE k;
      AppCG; [apply sucEns; Ens|]; split; [ind|]]]; clear N; simpl end.

Fixpoint iter (n : nat) {X : Type} (f : X → X) (x : X) :=
  match n with
  | O => x
  | S n' => f (iter n' f x)
  end.

(* 元语言自然数嵌入到集合论自然数（自动类型转换） *)
Coercion Embed n := iter n Suc ∅.

Fact pred : ∀ n, Embed n =
  match n with | O => ∅ | S n' => (Embed n')⁺ end.
Proof. intros. destruct n; auto. Qed.

Fact embed_ran : ∀ n : nat, n ∈ ω.
Proof. induction n; ens. ind. Qed.

Fact natEns : ∀ n : nat, Ensemble n.
Proof. intros. pose proof (embed_ran n). Ens. Qed.
Hint Immediate embed_ran natEns : Ens_hint.

Delimit Scope Nat_scope with n.
Open Scope Nat_scope.

Notation "a ≤ b" := (a ∈ b ∨ a = b) (at level 70) : Nat_scope.

Fact leq_iff_lt_suc : ∀ m n, m ∈ ω → n ∈ ω → m ≤ n ↔ m ∈ n⁺.
Proof.
  intros * Hm Hn. AssE n. unfold Suc. split; intros.
  destruct H0; subst; ens. unH; auto; sing H0.
Qed.

Close Scope Nat_scope.

Fact suc_has_0 : ∀ n, n ∈ ω → 0 ∈ n⁺.
Proof. intros. ω_induction n. ens. apply leq_iff_lt_suc; ens. Qed.
Hint Resolve suc_has_0 : Ens_hint.

Definition Equinumerous A B := ∃ F, bijection F A B.
Notation "A ≈ B" := (Equinumerous A B) (at level 70).

Fact eqnumSymm : ∀ A B, A ≈ B → B ≈ A.
Proof. intros * [f H]. exists (f⁻¹). apply inv_bijection; auto. Qed.

Definition Finite X := ∃ n, n ∈ ω ∧ X ≈ n.

Fact sin_finite : ∀ a, Ensemble a → Finite ([a]).
Proof.
  intros. exists 1. andG; ens. exists ([[a,∅]]). rewrite pred; unfold Suc.
  rewrite CommuU, EmptyU. apply single_ord_bijective; ens.
Qed.

Fact fin_image : ∀ f X Y, maps_into f X Y → Finite X → Finite f\(X\).
Admitted.

(* Topological Concepts *)

Definition Topology X cT := cT ⊂ cP(X) ∧
  X ∈ cT ∧ ∅ ∈ cT ∧ (∀ A B, A ∈ cT → B ∈ cT → A ∩ B ∈ cT) ∧
  (∀ cT1, cT1 ⊂ cT → ∪cT1 ∈ cT).

Fact TopologyP : ∀ X cT, Ensemble X → Topology X cT →
  ∀ cT1, ⦿ cT1 → Finite cT1 → cT1 ⊂ cT → ⋂cT1 ∈ cT.
Proof.
  intros * Hxe Htp * Hne [n [Hn He]] Hs. apply eqnumSymm in He as [f].
  apply bijection_is_func in H; andH. apply MapMapR1 in H.
  edestruct MarkFamEq as [_ Hp]. split; eauto.
  apply Mapping3 in H; subst; auto. rewrite <- Hp; clear Hp.
  generalize dependent f. generalize dependent cT1.
  ω_induction n; intros * Hne Hs * Hf Hi Hr.
  - destruct Hne as [A Ha], Hi as [_ Hi]. rewrite <- Hr in Ha. apply Hi in
      Ha. destruct Ha as [[x Ha] _]. apply Hf in Ha. cprod Ha; exfalso0.
  - assert (Hki : k ∈ k⁺). ens. assert (Hke : f[k] ∈ cT1).
    eapply ValueP1; eauto. assert (Hks : k ⁺ - [k] = k).
    { AppE. smH. AppC H0. orH; auto. sing H0. apply SingNE in H1; auto.
      elim H1; auto. smG. AppCG; Ens. apply SingNI; auto. intro.
      subst. apply RegAxP in H0; auto. } DC (k = ∅).
    { subst k; apply Hs. assert (MarkFamI f ∅ ⁺ = f[∅]).
      { AppE. AppC H0; apply H0; ens. AppCG; Ens. intros; AppC H1. orH.
      exfalso0. sing H1. } rewrite H0. eapply ValueP1; eens. }
    apply Mapping2 in Hf as Hfd. apply MapMapR in Hf as Hff.
    assert (Hfb : bijection f k⁺ cT1). apply bijection_is_func; auto.
    assert (Hp : ∀ x, x ∈ k⁺ → x ≠ k → f[x] ≠ f[k]).
    { intros. AppC H1. orH; [|sing H1].
      assert ([x,f[x]] ∈ f ∧ [k,f[k]] ∈ f). andG; eapply ValueP; eauto.
      AppCG; Ens. andH. intro. rewrite H5 in H3. assert (x = k).
      eapply Hi; eauto. rewrite Hr; auto. auto. }
    pose proof (bijection_sm_point _ _ _ _ Hfb Hki Hp) as Hfb'.
    set (f-[[k,f[k]]]) as f'. assert (MarkFamI f k⁺ = MarkFamI f' k∩f[k]).
    { apply IncAsym; intros x Hx; AssE x; AppCG.
      - AppC Hx. andG; [|apply Hx; ens]. AppCG; intros. AppCG; intros.
        AppC H3. AppC H3; andH. eapply ValueP2 in H3; eauto;
        [|AppCG; Ens]. subst; apply Hx; AppCG; Ens.
      - inH. intros. AppC H4; orH; [|sing H4]. DC (γ = k).
        subst; apply RegAxP in H4; elim H4. AppC H2.
        assert ([γ,f[γ]] ∈ f ∧ [k,f[k]] ∈ f).
        { andG; eapply ValueP; eauto. AppCG; Ens. }
        destruct H6 as [Hgc Hkc]. assert (Ensemble f[γ] ∧ Ensemble f[k]).
        { AssE [γ,f[γ]]; AssE [k,f[k]]. apply OrdEns2 in H6.
          apply OrdEns2 in H7; auto. } destruct H6 as [Hgb Hkb].
        apply H2 in H4 as Hg. AppC Hg. apply Hg. AppCG. AppCG; andG; Ens.
        apply SingNI; ens. intro. apply ordEq in H6; andH; Ens. }
    rewrite H1. apply Htp; [|apply Hs; eapply ValueP1; eens].
    apply bijection_is_func in Hfb'; andH. apply MapMapR1 in H2.
    rewrite Hks in H2. apply (IH (cT1 - [f[k]])); auto;
    [|intros A Ha; smH; auto]. destruct Hne as [A Ha]. rewrite <- Hr in Ha.
    exists f[∅]. smG. eapply ValueP1; eens. apply SingNI; Ens. intro.
    assert ([∅,f[∅]] ∈ f ∧ [k,f[k]] ∈ f). andG; eapply ValueP; eens.
    andH. rewrite H5 in H6. assert (k = ∅).
    eapply Hi; revgoals; eauto. rewrite Hr; auto. auto.
Qed.

(* Neighborhood and neighborhood system *)
Definition TNeigh x U X cT := Topology X cT ∧ x ∈ X ∧ U ⊂ X ∧
  ∃ V, V ∈ cT ∧ x ∈ V ∧ V ⊂ U.
Definition TNeighS x X cT := \{λ U, TNeigh x U X cT\}.

Fact TNeighP : ∀ x U X cT,
  Topology X cT → x ∈ U → U ∈ cT → TNeigh x U X cT.
Proof.
  intros. assert (U ⊂ X). apply H in H1; pow H1.
  red; andG; auto. exists U; andG; ens.
Qed.

Fact TNeighP1 : ∀ x U X cT,
  Ensemble X → TNeigh x U X cT ↔ U ∈ TNeighS x X cT.
Proof. split; intros. AppCG. eapply SubAxP; eauto. apply H0. AppC H0. Qed.

Definition EleUx x U cT := ∪\{λ V, x ∈ U ∧ V ∈ cT ∧ x ∈ V ∧ V ⊂ U \}.

Lemma Le_NeFa : ∀ U, U = ∪(\{λ t, ∃ x, x ∈ U ∧ t = [x]\}).
Proof.
  intro. AppE; AssE x. AppCG. exists [x]. andG; ens. AppCG; ens.
  eleU H. AppC H1; destruct H1; andH. subst. sing H; Ens.
Qed.

Fact Neighbor_F : ∀ U X cT, Ensemble X → Topology X cT → U ⊂ X →
  (U ∈ cT ↔ ∀ x, x ∈ U → U ∈ TNeighS x X cT).
Proof.
  intros * Hxe Ht Hs. split; intros Hp.
  - intros. apply TNeighP1, TNeighP; auto.
  - DC (U = ∅). subst; apply Ht. set (∪(\{λ t, ∃ x, x ∈ U ∧
      t = EleUx x U cT\})) as Hmi.
    assert (H1 : ∪(\{λ t, ∃ x, x ∈ U ∧ t = [x]\}) ⊂ Hmi).
    { intros z Hz; eleU Hz. AppC H1; destruct H1; andH. subst.
      sing H0; Ens. apply Hp in H1 as Hu. AppC Hu. AppCG; Ens.
      exists (EleUx x0 U cT). andG. AppCG; Ens. destruct Hu as
        [_ [_ [_ [V [Hv []]]]]]. exists V. andG; auto. AppCG; Ens. AppCG.
      apply (SubAxP U); eens. intros z Hz. eleU Hz. AppC H2; andH; auto. }
    rewrite <- Le_NeFa in H1. assert (H2 : Hmi ⊂ U).
    { intros z Hz. eleU Hz. AppC H2; destruct H2; andH.
      subst. eleU H0; AppC H3; andH; auto. } assert (U = Hmi). eens.
    rewrite H0. apply Ht; intros V Hv. AppC Hv; destruct Hv; andH.
    subst V. apply Ht. intros z Hz; AppC Hz; tauto.
Qed.

Fact Neighbors_Fa : ∀ x X cT, Ensemble X → Topology X cT → x ∈ X →
  ∀ U V, U ∈ TNeighS x X cT → V ∈ TNeighS x X cT → U ∩ V ∈ TNeighS x X cT.
Proof.
  intros * Hxe Ht Hx * Hu Hv.
  apply TNeighP1 in Hu as [_ [_ [Hux [U0 [Ho1 []]]]]]; auto.
  apply TNeighP1 in Hv as [_ [_ [Hvx [V0 [Ho2 []]]]]]; auto.
  apply TNeighP1; auto. red; andG; auto. intros z Hz; inH; auto.
  exists (U0 ∩ V0). andG; ens. apply Ht; auto. intros z Hz; inH; ens.
Qed.

Fact Neighbors_Fb : ∀ x X cT, Ensemble X → Topology X cT → x ∈ X →
  ∀ U V, U ∈ TNeighS x X cT → V ⊂ X → U ⊂ V → V ∈ TNeighS x X cT.
Proof.
  intros * Hxe Ht Hx * Hu Hv Huv.
  apply TNeighP1 in Hu as [_ [_ [Hux [U0 [Ho1 []]]]]]; auto.
  apply TNeighP1; auto. red; andG; auto. exists U0; andG; eens.
Qed.

Fact Neighbors_Fc : ∀ x X cT, Ensemble X → Topology X cT → x ∈ X →
  ∀ U, U ∈ TNeighS x X cT → ∃ V, V ∈ TNeighS x X cT ∧ V ⊂ U ∧
  (∀ y, y ∈ V → V ∈ TNeighS y X cT).
Proof.
  intros. apply TNeighP1 in H2 as [_[_[Hu [V [Ho []]]]]]; auto. exists V.
  andG; auto. apply TNeighP1, TNeighP; auto. apply Neighbor_F; eens.
Qed.

(* Derived, Closed, Closure *)
Definition Cluster x A X cT := Topology X cT ∧ A ⊂ X ∧ x ∈ X ∧
  ∀ U, TNeigh x U X cT → U ∩ (A - [x]) ≠ ∅.
Definition Derived A X cT := \{λ x, Cluster x A X cT\}.
Definition Closed A X cT := Topology X cT ∧ A ⊂ X ∧ Derived A X cT ⊂ A.
Definition Closure A X cT := A ⋃ Derived A X cT.

Fact DerivedP : ∀ A X cT, Derived A X cT ⊂ X.
Proof. intros * x Hx. AppC Hx. apply Hx. Qed.

Fact ClosureP : ∀ A X cT, A ⊂ X → Closure A X cT ⊂ X.
Proof.
  intros * Ha x Hx. AppC Hx; orH; auto. apply DerivedP in H; auto.
Qed.

Fact DerivedP1 : ∀ x A X cT, Cluster x A X cT ↔ x ∈ Derived A X cT.
Proof. split; intros. AppCG; exists X; apply H. AppC H. Qed.

Fact DerivedP2 : ∀ x A X cT, Topology X cT → A ⊂ X → x ∈ X →
  x ∉ Derived A X cT → ∃ U, TNeigh x U X cT ∧ U ∩ (A - [x]) = ∅.
Proof.
  intros * Ht Hs Hx Hp. DC (∃ U, TNeigh x U X cT ∧ U ∩ (A - [x]) = ∅).
  auto. elim Hp; apply DerivedP1; red; andG; eauto.
Qed.

Fact Derived_Fa : ∀ A B X cT,
  B ⊂ X → A ⊂ B → Derived A X cT ⊂ Derived B X cT.
Proof.
  intros * Hb Hs x Hx. apply DerivedP1 in Hx. red in Hx; andH.
  apply DerivedP1. red; andG; auto. intros U Hu. apply H2 in Hu.
  apply EmptyNE in Hu as [y]. inH; smH.
  apply EmptyNE. exists y; inG; smG; auto.
Qed.

Fact Derived_Fb : ∀ A B X cT, Ensemble X → A ⊂ X → B ⊂ X →
  Derived (A ⋃ B) X cT = Derived A X cT ⋃ Derived B X cT.
Proof.
  intros * Hxe Ha Hb. apply IncAsym.
  - intros x Hx. pose proof Hx as Hx'. apply DerivedP1 in Hx as
      [Ht [_ [Hx _]]]. DC (x ∈ Derived A X cT ⋃ Derived B X cT); auto.
    apply UnionNE in H; andH. apply DerivedP2 in H as [U [Hun Hu]];
    apply DerivedP2 in H0 as [V [Hvn Hv]]; auto.
    assert (x ∉ Derived (A ⋃ B) X cT).
    { intro. apply DerivedP1 in H as [_ [_ [_ Hp]]]. set (U ∩ V) as D.
      assert (D ∈ TNeighS x X cT). apply Neighbors_Fa; auto;
      apply TNeighP1; auto. apply TNeighP1, Hp in H; auto.
      assert (D ∩ (A ⋃ B) - [x] = ∅).
      { assert ((A ⋃ B) - [x] = A - [x] ⋃ B - [x]). AppE. smH; unH; ens.
        unH; smH; smG; ens. rewrite H0, DistribuLI. AppE; [|exfalso0].
        rewrite <- Hu, <- (EmptyU (U ∩ A - [x])), <- Hv.
        unH;inH;smH;AppC H1; andH; [unG|apply UnionI']; inG; smG; auto. }
       auto. } tauto.
  - assert (Derived A X cT ⊂ Derived (A ⋃ B) X cT ∧
      Derived B X cT ⊂ Derived (A ⋃ B) X cT).
    { andG; apply Derived_Fa; intros x Hx; unH; ens. }
    andH; intros x Hx; unH; auto.
Qed.

Fact Derived_Fc : ∀ A X cT, Ensemble X → A ⊂ X →
  Derived (Derived A X cT) X cT ⊂ A ⋃ Derived A X cT.
Proof.
  intros * Hxe Ha x Hx. pose proof Hx as Hx'. apply DerivedP1 in Hx as
    [Ht [_ [Hx _]]]. DC (x ∈ A ⋃ Derived A X cT); auto. exfalso.
  apply UnionNE in H as [Hxa Hxd]. apply DerivedP2 in Hxd as
    [U [Hun Hue]]; auto. apply TNeighP1 in Hun as Hun'; auto.
  apply Neighbors_Fc in Hun' as [V [Hvn [Hvu Hp]]]; auto.
  apply Neighbor_F in Hp as Hp'; auto; [|apply TNeighP1 in Hvn; auto;
  eapply IncTran; eauto; apply Hun]. assert (V ∩ A - [x] = ∅).
  { AppE; [|exfalso0]. rewrite <- Hue. inH; smH. inG; smG; auto. }
  assert (V ∩ A = ∅). { eapply InterEqEmI; revgoals; eauto; Ens. }
  assert (∀ y, y ∈ V → y ∉ A).
  { intros * Hy H1. assert (y ∈ V ∩ A); ens. rewrite H0 in H2. exfalso0. }
  assert (∀ y, y ∈ V → V ∩ A - [y] = ∅).
  { intros. AppE; [|exfalso0]. inH; smH. apply H1 in H3; tauto. }
  assert (∀ y, y ∈ V → y ∉ Derived A X cT).
  { intros * Hy H3. apply H2 in Hy as Hyp. apply DerivedP1 in H3.
    apply Hp, TNeighP1, H3 in Hy; auto. }
  assert (V ∩ Derived A X cT - [x] = ∅).
  { AppE; [|exfalso0]. inH; smH. exfalso. apply H3 in H4; auto. }
  apply DerivedP1 in Hx' as [_ [_ [_ Hx']]].
  AppC Hvn. apply Hx' in Hvn; auto.
Qed.

Fact Closed_F1 : ∀ A X cT, Ensemble X → Topology X cT → A ⊂ X →
  Closed A X cT ↔ X - A ∈ cT.
Proof.
  intros * Hxe Ht Hs. pose proof (SetminSubI A X). split; intros Hp.
  - eapply Neighbor_F; eauto. intros. smH. assert (x ∉ Derived A X cT).
    { intro. apply Hp in H2; tauto. } apply DerivedP2 in H2 as
      [U [Hun Hue]]; auto. apply InterEqEmI in Hue; Ens. 
    apply TNeighP1; auto. red; andG; auto. destruct Hun as
      [_ [_ [Hu [V [Hv [Hxv Hvu]]]]]]. exists V. andG; auto.
    eapply IncTran; eauto. intros z Hz. smG; auto. intro.
    assert (z ∈ U ∩ A); ens. rewrite Hue in H3; exfalso0.
  - red; andG; auto. intros x Hx. DC (x ∈ A); auto. exfalso.
    assert (x ∈ X - A). { AppC Hx. smG; auto. apply Hx. }
    eapply Neighbor_F, TNeighP1 in H1; eauto. pose proof Hx.
    apply DerivedP1 in Hx as [_ [_ [_ Hx]]]. apply Hx in H1.
    assert (X-A ∩ A-[x] = ∅). AppE; [|exfalso0]; inH; smH; tauto. auto.
Qed.

Corollary Co_ClFa1 : ∀ A X cT,
  Ensemble X → Topology X cT → A ⊂ X → A ∈ cT → Closed (X - A) X cT.
Proof.
  intros. apply Closed_F1; auto.
  apply SetminSubI. rewrite TwoCompl; auto.
Qed.

Fact Closed_F2 : ∀ A X cT, Topology X cT → A ⊂ X →
  Closed A X cT ↔ A = Closure A X cT.
Proof.
  intros * Ht Hs. split.
  - intros [_ [_ Hp]]. unfold Closure. AppE; [|unH]; ens.
  - intros. red; andG; auto. rewrite H at 2; intros z HZ; AppCG; Ens.
Qed.

Fact Closure_Fa : ∀ A X cT, A ⊂ Closure A X cT.
Proof. intros * x Hx. AppCG; Ens. Qed.

Fact Closure_Fb : ∀ A B X cT, Ensemble X → Topology X cT →
  A ⊂ X → B ⊂ X → Closure (A ⋃ B) X cT = Closure A X cT ⋃ Closure B X cT.
Proof.
  intros * Hxe Ht Ha Hb. unfold Closure. rewrite Derived_Fb,
    AssocU, (CommuU B), <- AssocU,
    <- AssocU, AssocU, (CommuU _ B); auto.
Qed.

Fact Closure_Fc : ∀ A X cT, Ensemble X → Topology X cT → A ⊂ X →
  Closure (Closure A X cT) X cT = Closure A X cT.
Proof.
  intros * He Ht Hs. unfold Closure at 2. rewrite Closure_Fb; auto;
  [|apply DerivedP]. unfold Closure. rewrite AssocU,
    <- (AssocU (Derived A X cT) _ _), IdemU,
    <- AssocU, UnionSub; auto. apply Derived_Fc; auto.
Qed.

Fact Re1_CloClo : ∀ A X cT, Ensemble X → Topology X cT → A ⊂ X →
  Closed (Closure A X cT) X cT.
Proof.
  intros * Hxe Ht Hs. apply Closed_F2; auto.
  apply ClosureP; auto. rewrite Closure_Fc; auto.
Qed.

Fact Re2_CloClo : ∀ A B X cT, Topology X cT →
  A ⊂ B → Closed B X cT → Closure A X cT ⊂ B.
Proof.
  intros * Ht Hab Hb z Hz. AppC Hz; orH; auto.
  eapply Derived_Fa in H; eauto; apply Hb; auto.
Qed.

(* Interior *)
Definition Interiorp x A X cT := TNeigh x A X cT.
Definition Interior A X cT := \{λ x, Interiorp x A X cT \}.

Fact Interior_F : ∀ A X cT, Ensemble X → Topology X cT → A ⊂ X →
  Interior A X cT = X - (Closure (X - A) X cT).
Proof.
  intros * Hxe Ht Hs. apply IncAsym; intros x Hx.
  - AppC Hx. assert (Hx' := Hx).
    destruct Hx as [_ [Hx [_ [V [Hv [Hxv Hva]]]]]]. apply Hva in Hxv.
    AppCG; andG; Ens. intro. AppC H; orH. smH; auto. apply DerivedP1 in H.
    apply H in Hx'. elim Hx'. AppE. inH; smH; tauto. exfalso0.
  - smH. apply UnionNE in H0 as [Hxi Hc]. apply DerivedP2 in Hc as
      [V [Hnv Hc]]; auto; [|apply SetminSubI]. apply InterEqEmI in Hc; Ens.
    apply InterSetmin in Hc; [|apply Hnv]. AppCG; Ens.
    eapply TNeighP1, Neighbors_Fb; eauto. apply TNeighP1; auto.
Qed.

(* Base, SubBase, TNeighBase, TNeighSubBase *)
Definition Base cB X cT := Topology X cT ∧ cB ⊂ cT ∧
  ∀ U, U ∈ cT → ∃ cB1, cB1 ⊂ cB ∧ U = ∪cB1.
Definition SubBase cS X cT := Topology X cT ∧ cS ⊂ cT ∧
  Base (\{λ U, ∃ cN, ⦿ cN ∧ Finite cN ∧ cN ⊂ cS ∧ U = ⋂cN\}) X cT.
Definition TNeighBase x cVx X cT :=
  Topology X cT ∧ x ∈ X ∧ cVx ⊂ TNeighS x X cT ∧
  (∀ U, U ∈ TNeighS x X cT → ∃ V, V ∈ cVx ∧ V ⊂ U).
Definition TNeighSubBase x cWx X cT :=
  Topology X cT ∧ x ∈ X ∧ cWx ⊂ TNeighS x X cT ∧ TNeighBase x
  (\{λ U, ∃ cN, ⦿ cN ∧ Finite cN ∧ cN ⊂ cWx ∧ U = ⋂cN\}) X cT.

Fact BaseP : ∀ X cT, Topology X cT → Base cT X cT.
Proof.
  split; andG; ens. intros. exists [U]. andG. intros z Hz.
  sing Hz; Ens. rewrite EleUSin; Ens.
Qed.

Fact NeFiSuP1 : ∀ cS,
  cS ⊂ \{λ U, ∃ cN, ⦿ cN ∧ Finite cN ∧ cN ⊂ cS ∧ U = ⋂cN\}.
Proof.
  intros * U Hu; AssE U. AppCG. exists [U]. andG. exists U; ens.
  apply sin_finite; auto. intros x Hx; sing Hx. rewrite EleISin; auto.
Qed.

Fact NeFiSuP2 : ∀ X cT, Ensemble X → Topology X cT →
  \{λ U, ∃ cN, ⦿ cN ∧ Finite cN ∧ cN ⊂ cT ∧ U = ⋂cN\} = cT.
Proof.
  intros. apply IncAsym; [|apply NeFiSuP1].
  intros U Hu. AppC Hu. destruct Hu as [cN [Hn [Hfi []]]].
  subst. eapply TopologyP; eauto.
Qed.

Fact TNeighBaseP : ∀ x X cT, Ensemble X → Topology X cT → x ∈ X →
  TNeighBase x (TNeighS x X cT) X cT.
Proof.
  intros. split; andG; ens. intros.
  apply Neighbors_Fc in H2 as [V [Hv []]]; eauto.
Qed.

(* 6 Continuous Functions *)
Definition TContinuF f X Y cT cT1 := Mapping f X Y ∧
  Topology X cT ∧ Topology Y cT1 ∧ ∀ U, U ∈ cT1 → OrigImage U f ∈ cT.

Fact ContinuF_Pa : ∀ X cT, Topology X cT → TContinuF ∆(X) X X cT cT.
Proof.
  intros. red; andG; auto. apply IdenRelM.
  intros. apply H in H0 as Hs; pow Hs. rewrite IdentOri; auto.
Qed.

Fact ContinuF_Pb : ∀ f g X Y Z cT1 cT2 cT3,
  Topology X cT1 → Topology Y cT2 → Topology Z cT3 →
  TContinuF f X Y cT1 cT2 → TContinuF g Y Z cT2 cT3 →
  TContinuF (g∘f) X Z cT1 cT3.
Proof.
  intros * Ht1 Ht2 Ht3. unfold TContinuF; intros; andH.
  andG; auto. eapply CompoMap; eauto.
  intros; apply H3, H6 in H7; rewrite CompoOrIm; auto.
Qed.

Definition TContinu f X Y x cT cT1 :=
  Topology X cT ∧ Topology Y cT1 ∧ Mapping f X Y ∧ x ∈ X ∧
  ∀ U, TNeigh f[x] U Y cT1 → TNeigh x (OrigImage U f) X cT.

Fact Continu_Pa : ∀ x X cT, x ∈ X → Topology X cT →
  TContinu ∆(X) X X x cT cT.
Proof.
  intros. red; andG; auto. apply IdenRelM. unfold TNeigh; intros; andH.
  destruct H4 as [V[Hv[]]]. andG; auto. rewrite IdentOri; auto. exists V.
  andG; [auto|erewrite <- ValueIdenR in H4|rewrite IdentOri]; auto.
Qed.

Fact Continu_Pb : ∀ f g X Y Z x cT1 cT2 cT3, x ∈ X →
  TContinu f X Y x cT1 cT2 → TContinu g Y Z f[x] cT2 cT3 →
  TContinu (g∘f) X Z x cT1 cT3.
Proof.
  unfold TContinu; intros; andH. andG; auto. eapply CompoMap; eauto.
  intros U Hp. rewrite CompoOrIm. apply H9, H5.
  eapply CompoMap' in H; eauto. rewrite <- H; auto.
Qed.

Fact Re_Continu : ∀ f X Y cT cT1, Ensemble X →
  Topology X cT → Topology Y cT1 → Mapping f X Y →
  TContinuF f X Y cT cT1 ↔ ∀ x, x ∈ X → TContinu f X Y x cT cT1.
Proof.
  intros * Hxe Htx Hty Hf. unfold TContinuF, TContinu. split; intros Hp.
  - andH. intros x Hx. andG; auto. intros * [_ [_ [Hu [V [Hv []]]]]].
    red; andG; auto. eapply MapOri; eauto. exists (OrigImage V f).
    andG; eens. apply OrigImageSub; auto.
  - andG; auto. intros * Hu. apply Hty in Hu as Hs; pow Hs.
    assert (Hux : OrigImage U f ⊂ X). eapply MapOri; eauto.
    eapply Neighbor_F; eauto. intros. apply TNeighP1; auto.
    apply Hp; auto. pose proof H as Hx. oriim H. assert (x0 = f[x]).
    eens. red; andG; eens. exists U; andG; ens. subst; auto.
Qed.

(* Theorem 1 *)
Theorem Theorem1a : ∀ X Y cT cT1 f,
  Ensemble X → Ensemble Y → TContinuF f X Y cT cT1 →
  ∀ B, Closed B Y cT1 → Closed (OrigImage B f) X cT.
Proof.
  intros * Hxe Hye [Hf [Hx [Hy Hp]]] * Hb. assert (Hbs : B ⊂ Y). apply Hb.
  eapply Closed_F1 in Hb; auto. apply Hp in Hb. erewrite CompleOrIm
    in Hb; eauto. apply Closed_F1; auto. eapply MapOri; eauto.
Qed.

Theorem Theorem1b : ∀ X Y cT cT1 f,
  Ensemble Y → Topology X cT → Topology Y cT1 → Mapping f X Y →
  (∀ B, Closed B Y cT1 → Closed (OrigImage B f) X cT) →
  (∀ A, A ⊂ X → f\(Closure A X cT\) ⊂ Closure f\(A\) Y cT1).
Proof.
  intros * Hye Hx Hy Hf Hp * Ha.
  assert (H1 : f\(A\) ⊂ Closure f\(A\) Y cT1).
  { intros z Hz. AppCG; Ens. } eapply OrigImageSub in H1.
  assert (A ⊂ OrigImage (Closure f \(A\) Y cT1) f).
  { eapply IncTran; revgoals; eauto. eapply MapDomSub; eauto. }
  assert (H2 : Closed (Closure f\(A\) Y cT1) Y cT1).
  { apply Re1_CloClo; auto. intros z Hz; image Hz.
    apply Hf in H2; cprod H2. }
  assert (H3 : Closure A X cT ⊂ OrigImage (Closure f\(A\) Y cT1) f).
  { apply Re2_CloClo; auto. } eapply ImageSub in H3.
  eapply IncTran; eauto. eapply MapOriIm; eauto.
Qed.

Theorem Theorem1c : ∀ X Y cT cT1 f, Mapping f X Y →
  (∀ A, A ⊂ X → f\(Closure A X cT\) ⊂ Closure f\(A\) Y cT1) →
  (∀ B, B ⊂ Y → Closure (OrigImage B f) X cT ⊂
  OrigImage (Closure B Y cT1) f).
Proof.
  intros * Hf Hp * Hb. assert (OrigImage B f ⊂ X).
  eapply MapOri; eauto. apply Hp in H.
  assert (Closure f\(OrigImage B f\) Y cT1 ⊂ Closure B Y cT1).
  { intros z Hz. AppC Hz; orH; AppCG; Ens; [left|right;
    eapply Derived_Fa in H0; eauto]; eapply MapOriIm; eauto. }
  assert (f\(Closure (OrigImage B f) X cT\) ⊂ Closure B Y cT1).
  eapply IncTran; eauto. eapply OrigImageSub in H1.
  eapply IncTran; eauto. eapply MapDomSub; eauto.
  eapply ClosureP, MapOri; eauto.
Qed.

Theorem Theorem1d : ∀ X Y cT cT1 f, Ensemble X → Ensemble Y →
  Topology X cT → Topology Y cT1 → Mapping f X Y →
  (∀ B, B ⊂ Y → Closure (OrigImage B f) X cT ⊂
  OrigImage (Closure B Y cT1) f) → TContinuF f X Y cT cT1.
Proof.
  intros * Hxe Hye Hx Hy Hf Hp. red; andG; auto. intros * Hu.
  assert (Hsu : U ⊂ Y). apply Hy in Hu; pow Hu.
  assert (Huo : OrigImage (Y - U) f ⊂ X ∧ OrigImage U f ⊂ X).
  andG; eapply MapOri; eauto. assert (Huo' : X - OrigImage U f ⊂ X).
  apply SetminSubI. eapply Co_ClFa1 in Hu as Hc; eauto.
  pose proof SetminSubI U Y as Hsu'. apply Hp in Hsu'.
  assert (Hr : OrigImage (Closure (Y - U) Y cT1) f ⊂ OrigImage (Y-U) f).
  eapply OrigImageSub; intros z Hz; AppC Hz;orH;auto; apply Hc in H;auto.
  assert (Heq : Closure (OrigImage (Y - U) f) X cT = OrigImage (Y - U) f).
  { eapply IncAsym. eapply IncTran; eauto.
    apply Closure_Fa. } symmetry in Heq.
  apply Closed_F2 in Heq; auto; [|eapply MapOri; eauto].
  erewrite CompleOrIm in Heq; eauto. apply Closed_F1 in Heq; eauto.
  rewrite TwoCompl in Heq; auto. eapply MapOri; eauto.
Qed.

(* Theorem 2 *)
Theorem Theorem2a : ∀ X Y cT cT1 f, Ensemble X → Ensemble Y →
  TContinuF f X Y cT cT1 → ∀ B, B ⊂ Y →
  OrigImage (Interior B Y cT1) f ⊂ Interior (OrigImage B f) X cT.
Proof.
  intros * Hxe Hye Ht * Hb. assert (Hp : ∀B, B ⊂ Y →
    Closure (OrigImage B f) X cT ⊂ OrigImage (Closure B Y cT1) f).
  { apply Theorem1c. apply Ht. apply Theorem1b; try apply Ht.
    auto. apply Theorem1a; auto. }
  pose proof (SetminSubI B Y) as Hbc. apply Hp in Hbc.
  apply (SetminSub2 _ _ X) in Hbc. repeat rewrite Interior_F; auto;
  try apply Ht; [|intros x Hx; oriim Hx; apply Ht in H0; cprod H0].
  rewrite (MapOriSm (Closure (Y - B) Y cT1) f X Y),
    <- (MapOriSm B f X Y); auto; apply Ht.
Qed.

Theorem Theorem2b : ∀ X Y cT cT1 f, Ensemble X → Ensemble Y →
  Topology X cT → Topology Y cT1 → Mapping f X Y → (∀ B, B ⊂ Y →
  OrigImage (Interior B Y cT1) f ⊂ Interior (OrigImage B f) X cT) →
  TContinuF f X Y cT cT1.
Proof.
  intros * Hxe Hye Hx Hy Hf Hp. apply Theorem1d; auto.
  intros B Hb; pose proof (SetminSubI B Y) as Hbc. apply Hp in Hbc.
  rewrite Interior_F, Interior_F, TwoCompl in Hbc; auto;
  [|eapply MapOri; eauto|apply SetminSubI].
  rewrite (MapOriSm (Closure B Y cT1) f X Y), <-
    (MapOriSm (Y - B) f X Y), TwoCompl in Hbc; auto.
  eapply SetminSub2 in Hbc. rewrite TwoCompl, TwoCompl in Hbc;
  auto; [|apply ClosureP]; eapply MapOri; eauto.
Qed.

(* Theorem 3 *)
Lemma LeTh3 : ∀ f cB X Y, Ensemble X → Mapping f X Y → ⦿ cB →
  OrigImage (⋂cB) f = ⋂\{λ U, ∃ B, B ∈ cB ∧ U = OrigImage B f\}.
Proof.
  intros * Hxe Hf [C Hc]. assert (Hp : ∀ B, B ∈ cB →
    OrigImage B f ∈ \{λ U, ∃ B, B ∈ cB ∧ U = OrigImage B f \}).
  { intros. AppCG. eapply MapOri in Hf. eens. } AppE.
  - AssE x. oriim H; AppC H. AppCG. intros A Ha.
    AppC Ha; destruct Ha as [B []]. subst; eens.
  - AppC H. apply Hp, H in Hc. oriim Hc. eapply OriImI; eauto.
    AppCG; Ens. intros B Hb. apply Hp in Hb. apply H in Hb. oriim Hb.
    assert (x0 = x1). eapply Hf; eauto. subst; auto.
Qed.

Lemma Le1Th3 : ∀ f cN X Y, Ensemble X → Mapping f X Y → Finite cN →
  Finite \{λ U, ∃ B : Class, B ∈ cN ∧ U = OrigImage B f \}.
Proof.
  intros * Hxe Hf Hfi. set (\{\λ U V, U ∈ cN ∧ V = OrigImage U f\}\) as g.
  assert (Hg : maps_onto g cN \{λ U ,∃ B, B ∈ cN ∧ U = OrigImage B f\}).
  { pose proof MapOri as Hs. split; andG. split. intros z Hz; PP Hz a b.
    - intros; dom H. AppC' H; andH. split. exists x0; AppCG'; subst.
      apply OrdEns. Ens. eens. intros. AppC' H1; AppC' H2; andH. subst; auto.
    - AppE. dom H; AppC' H. tauto. AppCG; Ens.
      exists (OrigImage x f). AppCG'. apply OrdEns. Ens. eens.
    - AppE; AssE x. ran H; AppC' H; AppCG. AppC H; destruct H; andH.
      AssE x0. AppCG; exists x0; AppCG'; ens. } destruct Hg as [Hg [Hgd Hgr]].
  assert (maps_into g cN \{λ U ,∃ B, B ∈ cN ∧ U = OrigImage B f\}).
  { split; andG; auto. intros y Hy. rewrite Hgr in Hy; auto. } rewrite <- Hgr.
  erewrite Mapping3. eapply fin_image; eauto. apply MapMapR1; eauto.
Qed.

Lemma Le3Th3 : ∀ f cB X Y, Ensemble X → Mapping f X Y →
  OrigImage (∪cB) f = ∪\{λ U, ∃ B, B ∈ cB ∧ U = OrigImage B f\}.
Proof.
  intros * Hxe Hf. AppE.
  - AssE x. oriim H; eleU H. AppCG. exists (OrigImage x1 f).
    andG; AppCG; eauto. eapply MapOri in Hf; eens.
  - eleU H. AppC H0; destruct H0 as [B []]. subst. oriim H; eens.
Qed.

Theorem Theorem3a : ∀ X Y cT cT1 f, Ensemble Y → Topology X cT →
  Topology Y cT1 → Mapping f X Y → TContinuF f X Y cT cT1 →
  (∃ cS, SubBase cS Y cT1 ∧ (∀ S, S ∈ cS → OrigImage S f ∈ cT)).
Proof.
  intros * Hye Ht Ht1 Hf Htf. exists cT1. andG. split; andG; ens.
  erewrite NeFiSuP2; eauto. apply BaseP; auto. apply Htf.
Qed.

Theorem Theorem3b : ∀ X Y cT cT1 f, Ensemble X →
  Topology X cT → Topology Y cT1 → Mapping f X Y →
  (∃ cS, SubBase cS Y cT1 ∧ (∀ S, S ∈ cS → OrigImage S f ∈ cT)) →
  (∃ cB, Base cB Y cT1 ∧ (∀ B, B ∈ cB → OrigImage B f ∈ cT)).
Proof.
  intros * Hxe Ht Ht1 Hf [cS [Hbs Hp]].
  exists (\{λ U, ∃ cN, ⦿ cN ∧ Finite cN ∧ cN ⊂ cS ∧ U = ⋂cN\}).
  andG. apply Hbs. intros. AppC H; destruct H as [cN [Hne [Hfi [Hsub Heq]]]].
  subst. erewrite LeTh3; eauto. eapply TopologyP; eauto.
  - destruct Hne as [B]. exists (OrigImage B f).
    AppCG. eapply MapOri in Hf; eens.
  - set (\{\λ U V, U ∈ cN ∧ V = OrigImage U f\}\) as g.
    assert (Hg : maps_onto g cN \{λ U ,∃ B, B ∈ cN ∧ U = OrigImage B f\}).
    { split; andG. split. intros z Hz; PP Hz a b.
      - intros; dom H. AppC' H; andH. split. exists x0; AppCG'; subst.
        apply OrdEns; Ens. intros. AppC' H1; AppC' H2; andH. subst; auto.
      - AppE. dom H; AppC' H. tauto. AppCG; Ens. exists (OrigImage x f).
        AppCG'. apply OrdEns; Ens.
      - AppE; AssE x. ran H; AppC' H; AppCG. AppC H; destruct H; andH.
        AssE x0. AppCG; exists x0; AppCG'; ens. } destruct Hg as [Hg [Hgd Hgr]].
    assert (maps_into g cN \{λ U ,∃ B, B ∈ cN ∧ U = OrigImage B f\}).
    { split; andG; auto. intros y Hy. rewrite Hgr in Hy; auto. }
    rewrite <- Hgr. erewrite Mapping3. eapply fin_image; eauto.
    apply MapMapR1; eauto.
  - intros A Ha. AppC Ha. destruct Ha; andH. subst. apply Hp; auto.
Qed.

Theorem Theorem3c : ∀ X Y cT cT1 f, Ensemble X →
  Topology X cT → Topology Y cT1 → Mapping f X Y →
  (∃ cB, Base cB Y cT1 ∧ (∀ B, B ∈ cB → OrigImage B f ∈ cT)) →
  TContinuF f X Y cT cT1.
Proof.
  intros * Hxe Ht Ht1 Hf [cB [Hbs Hp]]. split; andG; auto. intros.
  apply Hbs in H as [cB1 []]. subst. erewrite Le3Th3; eauto.
  apply Ht. intros A Ha. AppC Ha. destruct Ha; andH. subst. apply Hp; auto.
Qed.

(* Theorem 4 *)
Lemma LeTh4 : ∀ x X cT, Ensemble X → Topology X cT → x ∈ X →
  ∀ cT1, ⦿ cT1 → Finite cT1 → (∀ B, B ∈ cT1 → TNeigh x B X cT) →
  TNeigh x (⋂cT1) X cT.
Proof.
  intros * Hxe Htp Hx * Hne [n [Hn He]] Hb. apply eqnumSymm in He as [f].
  apply bijection_is_func in H; andH. apply MapMapR1 in H.
  edestruct MarkFamEq as [_ Hp]. split; eauto.
  apply Mapping3 in H; subst; auto. rewrite <- Hp; clear Hp.
  generalize dependent f. generalize dependent cT1.
  ω_induction n; intros * Hne Hs * Hf Hi Hr.
  - destruct Hne as [A Ha], Hi as [_ Hi]. rewrite <- Hr in Ha. apply Hi in
      Ha. destruct Ha as [[y Ha] _]. apply Hf in Ha. cprod Ha; exfalso0.
  - assert (Hki : k ∈ k⁺). ens. assert (Hke : f[k] ∈ cT1).
    eapply ValueP1; eauto. assert (Hks : k ⁺ - [k] = k).
    { AppE. smH. AppC H0. orH; auto. sing H0. apply SingNE in H1; auto.
      elim H1; auto. smG. AppCG; Ens. apply SingNI; auto. intro.
      subst. apply RegAxP in H0; auto. } DC (k = ∅).
    { subst k; apply Hs. assert (MarkFamI f ∅ ⁺ = f[∅]).
      { AppE. AppC H0; apply H0; ens. AppCG; Ens. intros; AppC H1. orH.
      exfalso0. sing H1. } rewrite H0. eapply ValueP1; eens. }
    apply Mapping2 in Hf as Hfd. apply MapMapR in Hf as Hff.
    assert (Hfb : bijection f k⁺ cT1). apply bijection_is_func; auto.
    assert (Hp : ∀ x0, x0 ∈ k⁺ → x0 ≠ k → f[x0] ≠ f[k]).
    { intros. AppC H1. orH; [|sing H1].
      assert ([x0,f[x0]] ∈ f ∧ [k,f[k]] ∈ f). andG; eapply ValueP; eauto.
      AppCG; Ens. andH. intro. rewrite H5 in H3. assert (x0 = k).
      eapply Hi; eauto. rewrite Hr; auto. auto. }
    pose proof (bijection_sm_point _ _ _ _ Hfb Hki Hp) as Hfb'.
    set (f-[[k,f[k]]]) as f'. assert (MarkFamI f k⁺ = MarkFamI f' k∩f[k]).
    { apply IncAsym; intros y Hy; AssE y; AppCG.
      - AppC Hy. andG; [|apply Hy; ens]. AppCG; intros. AppCG; intros.
        AppC H3. AppC H3; andH. eapply ValueP2 in H3; eauto;
        [|AppCG; Ens]. subst; apply Hy; AppCG; Ens.
      - inH. intros. AppC H4; orH; [|sing H4]. DC (γ = k).
        subst; apply RegAxP in H4; elim H4. AppC H2.
        assert ([γ,f[γ]] ∈ f ∧ [k,f[k]] ∈ f).
        { andG; eapply ValueP; eauto. AppCG; Ens. }
        destruct H6 as [Hgc Hkc]. assert (Ensemble f[γ] ∧ Ensemble f[k]).
        { AssE [γ,f[γ]]; AssE [k,f[k]]. apply OrdEns2 in H6.
          apply OrdEns2 in H7; auto. } destruct H6 as [Hgb Hkb].
        apply H2 in H4 as Hg. AppC Hg. apply Hg. AppCG. AppCG; andG; Ens.
        apply SingNI; ens. intro. apply ordEq in H6; andH; Ens. }
    rewrite H1. apply TNeighP1; auto. apply Neighbors_Fa; auto;
    [|apply TNeighP1; auto]. apply bijection_is_func in Hfb'; andH.
    apply MapMapR1 in H2. rewrite Hks in H2. apply TNeighP1; auto.
    apply (IH (cT1 - [f[k]])); auto; [|intros A Ha; smH; auto].
    destruct Hne as [A Ha]. rewrite <- Hr in Ha.
    exists f[∅]. smG. eapply ValueP1; eens. apply SingNI; Ens. intro.
    assert ([∅,f[∅]] ∈ f ∧ [k,f[k]] ∈ f). andG; eapply ValueP; eens.
    andH. rewrite H5 in H6. assert (k = ∅).
    eapply Hi; revgoals; eauto. rewrite Hr; auto. auto.
Qed.

Theorem Theorem4a : ∀ x X Y cT cT1 f, Ensemble Y →
  Topology X cT → Topology Y cT1 → Mapping f X Y → x ∈ X →
  TContinu f X Y x cT cT1 →
  (∃ cW_fx, TNeighSubBase f[x] cW_fx Y cT1 ∧
  (∀ W, W ∈ cW_fx → TNeigh x (OrigImage W f) X cT )).
Proof.
  intros * Hye Ht Ht1 Hf Hx Hp. assert (Hv : f[x] ∈ Y).
  eapply ValueP1; eauto. exists (TNeighS f[x] Y cT1).
  andG; [|intros; AppC H; apply Hp; auto]. split; andG; ens.
  assert (\{λ U, ∃ cN, ⦿ cN ∧ Finite cN ∧
    cN ⊂ TNeighS f[x] Y cT1 ∧ U = ⋂cN\} = TNeighS f[x] Y cT1).
  { apply IncAsym; [|apply NeFiSuP1].
    intros U Hu. AppC Hu; destruct Hu as [cN [Hn [Hfi []]]].
    subst. apply TNeighP1; auto. apply LeTh4; auto.
    intros. apply H, TNeighP1 in H0; auto. }
  rewrite H. apply TNeighBaseP; auto.
Qed.

Theorem Theorem4b : ∀ x X Y cT cT1 f, Ensemble X →
  Topology X cT → Topology Y cT1 → Mapping f X Y → x ∈ X →
  (∃ cW_fx, TNeighSubBase f[x] cW_fx Y cT1 ∧
  (∀ W, W ∈ cW_fx → TNeigh x (OrigImage W f) X cT )) →
  (∃ cV_fx, TNeighBase f[x] cV_fx Y cT1 ∧
  (∀ V, V ∈ cV_fx → TNeigh x (OrigImage V f) X cT )).
Proof.
  intros * Hxe Ht Ht1 Hf Hx [cW_fx [Hw Hp]].
  exists (\{λ t, ∃ cN, ⦿ cN ∧ Finite cN ∧ cN ⊂ cW_fx ∧ t = ⋂cN\}).
  andG. apply Hw. intros. AppC H; destruct H as [cN [Hn [Hfi []]]].
  subst. erewrite LeTh3; eauto. eapply LeTh4; auto.
  - destruct Hn as [A Hn]. exists (OrigImage A f). AppCG.
    eapply MapOri in Hf; eens.
  - eapply Le1Th3; eauto.
  - intros. AppC H0; destruct H0; andH. subst. apply Hp; auto.
Qed.

Theorem Theorem4c : ∀ x X Y cT cT1 f, Ensemble X → Ensemble Y →
  Topology X cT → Topology Y cT1 → Mapping f X Y → x ∈ X →
  (∃ cV_fx, TNeighBase f[x] cV_fx Y cT1 ∧
  (∀ V, V ∈ cV_fx → TNeigh x (OrigImage V f) X cT )) →
  TContinu f X Y x cT cT1.
Proof.
  intros * Hxe Hye Ht Ht1 Hf Hx [cV_fx [Hv Hp]]. split; andG; auto.
  intros. apply TNeighP1, Hv in H as [V []]; auto.
  apply Hp, TNeighP1 in H; auto. assert (OrigImage U f ∈ TNeighS x X cT).
  { eapply Neighbors_Fb; eauto. eapply MapOri; eauto.
    apply OrigImageSub; auto. } apply TNeighP1 in H1; auto.
Qed.
