module

public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.PreRelation
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.UniversallyInjective
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Pullback
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.PreRelation.Pairings
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Lambda
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.RelativeConditions

/-!
# Set-theoretic (pre-)equivalence relations

A pre-relation on an algebraic space is a set-theoretic pre-equivalence relation when the
relation on algebraically closed field-valued points, allowing a field-extension witness, is
an equivalence relation. It is a set-theoretic equivalence relation when this holds and the
defining map is universally injective.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits
open scoped Cardinal

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

/-- A pre-equivalence relation is a set-theoretic pre-equivalence relation. -/
theorem isSetTheoreticPreEquivalence_of_isPreEquivalence {S : Scheme.{u}}
    {B : AlgebraicSpace S} {U : Over B} (P : PreRelation U)
    (hP : P.IsPreEquivalence) : P.IsSetTheoreticPreEquivalence :=
  sorry

/-- An internal equivalence relation is a set-theoretic equivalence relation. -/
instance isSetTheoreticEquivalence_of_isEquivalenceRelation {S : Scheme.{u}}
    {B : AlgebraicSpace S} {U : Over B} (P : PreRelation U)
    [IsEquivalenceRelation P.t P.s] : P.IsSetTheoreticEquivalence :=
  sorry

/-- A pre-relation is a set-theoretic equivalence relation exactly when its defining map
is universally injective and its point image contains the images of the diagonal, flip,
and transitivity pairings. -/
theorem isSetTheoreticEquivalence_iff_universallyInjective_containsListImages
    {S : Scheme.{u}} {B : AlgebraicSpace S} {U : Over B} (P : PreRelation U) :
    IsSetTheoreticEquivalence P ↔
      UniversallyInjective P.hom.left ∧
        Set.range (Points.map (diagonalPairing U).left) ⊆ Set.range (Points.map P.hom.left) ∧
        Set.range (Points.map P.flipHom.left) ⊆ Set.range (Points.map P.hom.left) ∧
        Set.range (Points.map P.compPair.left) ⊆ Set.range (Points.map P.hom.left) :=
  sorry

/-- A pre-relation is a set-theoretic equivalence relation exactly when its point map is
injective and its image is an equivalence relation over every algebraically closed field
whose cardinality exceeds the cardinal bound of its source. -/
theorem isSetTheoreticEquivalence_iff_injectiveEquivOnLargeFieldPoints
    {S : Scheme.{u}} {B : AlgebraicSpace S} {U : Over B} (P : PreRelation U) :
    IsSetTheoreticEquivalence P ↔
      ∀ {k : Type u} [Field k] [IsAlgClosed k] {σ : Spec (.of k) ⟶ S}
        (τ : ofOver (Over.mk σ) ⟶ B),
        lambda P.left.left < #k →
          Function.Injective (P.pointMap (Over.mk τ)) ∧
            Equivalence (P.pointRel (Over.mk τ)) :=
  sorry

/-- If its defining map is decent, locally separated, or quasi-separated, a pre-relation
is a set-theoretic equivalence relation exactly when its point map is injective and its
image is an equivalence relation over every algebraically closed field over the base. -/
theorem isSetTheoreticEquivalence_iff_injectiveEquivOnFieldPoints
    {S : Scheme.{u}} {B : AlgebraicSpace S} {U : Over B} (P : PreRelation U)
    (h_decent_or_separated :
      Decent P.hom.left ∨ LocallySeparated P.hom.left ∨ QuasiSeparated P.hom.left) :
    IsSetTheoreticEquivalence P ↔
      ∀ {k : Type u} [Field k] [IsAlgClosed k] {σ : Spec (.of k) ⟶ S}
        (τ : ofOver (Over.mk σ) ⟶ B),
        Function.Injective (P.pointMap (Over.mk τ)) ∧
          Equivalence (P.pointRel (Over.mk τ)) :=
  sorry

end PreRelation

end AlgebraicGeometry.AlgebraicSpace
