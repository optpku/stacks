/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import stacks_project.Chap67.Lemma_67_19_5_UniversallyInjective
public import stacks_project.Chap78.Definition_78_4_1_PreRelation

/-!
# Set-theoretic (pre-)equivalence relations

A pre-relation on an algebraic space is a set-theoretic pre-equivalence relation when the
relation on algebraically closed field-valued points, allowing a field-extension witness, is
an equivalence relation. It is a set-theoretic equivalence relation when this holds and the
defining map is universally injective.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- The morphism of algebraic spaces over `S` induced by a field extension `K/k`. -/
def fieldExtensionOverMap {S : Scheme.{u}} {k : Type u} (K : Type u)
    [Field k] [Field K] [Algebra k K] (σ : Spec (.of k) ⟶ S) :
    ofOver (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k K)) ≫ σ)) ⟶
      ofOver (Over.mk σ) :=
  ofOverHomMk (Spec.map (CommRingCat.ofHom (algebraMap k K))) rfl

/-- `fieldExtensionOverMap` is `ofOverHomMk` of `Spec.map` of the algebra map. -/
theorem fieldExtensionOverMap_eq {S : Scheme.{u}} {k : Type u} (K : Type u)
    [Field k] [Field K] [Algebra k K] (σ : Spec (.of k) ⟶ S) :
    fieldExtensionOverMap K σ =
      ofOverHomMk (Spec.map (CommRingCat.ofHom (algebraMap k K))) rfl :=
  sorry

/-- Restriction of a `B`-point along a field extension `K/k`. -/
def restrictAlongFieldExtension {S : Scheme.{u}} {B : AlgebraicSpace S} {Y : Over B}
    {k : Type u} (K : Type u) [Field k] [Field K] [Algebra k K] {σ : Spec (.of k) ⟶ S}
    {τ : ofOver (Over.mk σ) ⟶ B} (f : Over.mk τ ⟶ Y) :
    Over.mk (fieldExtensionOverMap K σ ≫ τ) ⟶ Y :=
  (Over.homMk (fieldExtensionOverMap K σ) :
      Over.mk (fieldExtensionOverMap K σ ≫ τ) ⟶ Over.mk τ) ≫ f

/-- Restriction along `K/k` is precomposition with `fieldExtensionOverMap` in `Over B`. -/
theorem restrictAlongFieldExtension_comp {S : Scheme.{u}} {B : AlgebraicSpace S}
    {Y : Over B} {k : Type u} (K : Type u) [Field k] [Field K] [Algebra k K]
    {σ : Spec (.of k) ⟶ S} {τ : ofOver (Over.mk σ) ⟶ B} (f : Over.mk τ ⟶ Y) :
    restrictAlongFieldExtension K f = Over.homMk (fieldExtensionOverMap K σ) rfl ≫ f :=
  sorry

namespace PreRelation

/-- The set-theoretic relation `~_R` on `U(k)`: `x` and `y` are related when some field
extension `K/k` carries an `R(K)`-point with source `x` and target `y`. -/
def setTheoreticPointRel {S : Scheme.{u}} {B : AlgebraicSpace S} {U : Over B}
    (P : PreRelation U) {k : Type u} [Field k] [IsAlgClosed k] {σ : Spec (.of k) ⟶ S}
    (τ : ofOver (Over.mk σ) ⟶ B) (x y : Over.mk τ ⟶ U) : Prop :=
  ∃ (K : Type u) (_ : Field K) (_ : Algebra k K)
    (r : Over.mk (fieldExtensionOverMap K σ ≫ τ) ⟶ P.left),
    r ≫ P.s = restrictAlongFieldExtension K x ∧
      r ≫ P.t = restrictAlongFieldExtension K y

/-- Two algebraically closed `k`-points over `B` are related by `~_R` exactly when they
lift, after a field extension `K/k`, to a point of the source of the pre-relation. -/
theorem setTheoreticPointRel_iff {S : Scheme.{u}} {B : AlgebraicSpace S} {U : Over B}
    (P : PreRelation U) {k : Type u} [Field k] [IsAlgClosed k] {σ : Spec (.of k) ⟶ S}
    (τ : ofOver (Over.mk σ) ⟶ B) (x y : Over.mk τ ⟶ U) :
    P.setTheoreticPointRel τ x y ↔
      ∃ (K : Type u) (_ : Field K) (_ : Algebra k K)
        (r : Over.mk (fieldExtensionOverMap K σ ≫ τ) ⟶ P.left),
        r ≫ P.s = restrictAlongFieldExtension K x ∧
          r ≫ P.t = restrictAlongFieldExtension K y :=
  sorry

/-- A pre-relation is a set-theoretic pre-equivalence relation when `~_R` is an
equivalence relation on `U(k)` for every algebraically closed field `k` over `B`. -/
def IsSetTheoreticPreEquivalence {S : Scheme.{u}} {B : AlgebraicSpace S} {U : Over B}
    (P : PreRelation U) : Prop :=
  ∀ {k : Type u} [Field k] [IsAlgClosed k] {σ : Spec (.of k) ⟶ S}
    (τ : ofOver (Over.mk σ) ⟶ B), Equivalence (P.setTheoreticPointRel τ)

/-- The pointwise characterization of a set-theoretic pre-equivalence relation. -/
theorem isSetTheoreticPreEquivalence_iff {S : Scheme.{u}} {B : AlgebraicSpace S}
    {U : Over B} (P : PreRelation U) :
    IsSetTheoreticPreEquivalence P ↔
      ∀ {k : Type u} [Field k] [IsAlgClosed k] {σ : Spec (.of k) ⟶ S}
        (τ : ofOver (Over.mk σ) ⟶ B), Equivalence (P.setTheoreticPointRel τ) :=
  sorry

/-- A pre-relation is a set-theoretic equivalence relation when its defining map is
universally injective and it is a set-theoretic pre-equivalence relation. -/
class IsSetTheoreticEquivalence {S : Scheme.{u}} {B : AlgebraicSpace S} {U : Over B}
    (P : PreRelation U) : Prop where
  /-- The defining map `j` is universally injective. -/
  universallyInjective : UniversallyInjective P.hom.left
  /-- The pre-relation is a set-theoretic pre-equivalence relation. -/
  isSetTheoreticPreEquivalence : IsSetTheoreticPreEquivalence P

/-- A set-theoretic equivalence relation is universally injective. -/
instance instUniversallyInjective {S : Scheme.{u}} {B : AlgebraicSpace S} {U : Over B}
    {P : PreRelation U} [IsSetTheoreticEquivalence P] :
    UniversallyInjective P.hom.left :=
  IsSetTheoreticEquivalence.universallyInjective

/-- A pre-relation is a set-theoretic equivalence relation iff it is universally injective
and a set-theoretic pre-equivalence relation. -/
theorem isSetTheoreticEquivalence_iff {S : Scheme.{u}} {B : AlgebraicSpace S}
    {U : Over B} (P : PreRelation U) :
    IsSetTheoreticEquivalence P ↔
      UniversallyInjective P.hom.left ∧ IsSetTheoreticPreEquivalence P :=
  sorry

/-- The two defining conditions of a set-theoretic equivalence relation. -/
theorem isSetTheoreticEquivalence_spec {S : Scheme.{u}} {B : AlgebraicSpace S}
    {U : Over B} (P : PreRelation U) [IsSetTheoreticEquivalence P] :
    UniversallyInjective P.hom.left ∧ IsSetTheoreticPreEquivalence P :=
  sorry

end PreRelation

end AlgebraicGeometry.AlgebraicSpace
