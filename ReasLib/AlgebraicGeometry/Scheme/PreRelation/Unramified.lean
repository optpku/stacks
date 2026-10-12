/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.IsIso
public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyInjective
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import ReasLib.AlgebraicGeometry.Scheme.FieldValuedPoint
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Unramified.Cancellation
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Unramified.Diagonal
public import ReasLib.AlgebraicGeometry.Scheme.PreRelation

/-!
# Unramified pre-relations

This module gives a geometric-point criterion for an unramified pre-relation to define an
internal equivalence relation.
-/

@[expose] public section

open CategoryTheory Limits

universe u

namespace AlgebraicGeometry.Scheme.PreRelation

/-- If the first projection of a pre-relation is unramified, then its defining morphism is
unramified. -/
theorem unramifiedHomLeft {S : Scheme.{u}} {U : Over S} (P : PreRelation U)
    [Unramified P.t.left] : Unramified P.hom.left := by
  have hComposite : Unramified (P.hom.left ≫ (prod.fst (X := U)).left) := by
    simpa [PreRelation.t] using (inferInstance : Unramified P.t.left)
  exact @AlgebraicGeometry.Unramified.of_comp _ _ _ P.hom.left (prod.fst (X := U)).left
    hComposite

/-- Injectivity of the point map on algebraically closed field-valued points forces the diagonal
of the defining morphism of a pre-relation to be surjective. -/
theorem diagonalSurjectiveOfPointMapInjective {S : Scheme.{u}} {U : Over S} (P : PreRelation U)
    (h_injective : ∀ (p : FieldValuedPoint S) [IsAlgClosed p.K],
      Function.Injective (P.pointMap p.over)) :
    Surjective (pullback.diagonal P.hom.left) := by
  rw [surjective_iff]
  intro z
  let k := (pullback P.hom.left P.hom.left).residueField z
  let L := AlgebraicClosure k
  let φ : Spec (.of k) ⟶ pullback P.hom.left P.hom.left :=
    (pullback P.hom.left P.hom.left).fromSpecResidueField z
  let e : Spec (.of L) ⟶ Spec (.of k) :=
    Spec.map (CommRingCat.ofHom (algebraMap k L))
  let ψ : Spec (.of L) ⟶ pullback P.hom.left P.hom.left :=
    e ≫ φ
  let p : FieldValuedPoint S :=
    { K := L
      hom := ψ ≫ pullback.fst P.hom.left P.hom.left ≫ P.left.hom }
  let r₁ : p.over ⟶ P.left :=
    Over.homMk (ψ ≫ pullback.fst P.hom.left P.hom.left)
  have hBase :
      ψ ≫ pullback.snd P.hom.left P.hom.left ≫ P.left.hom = p.hom := by
    simpa [p, ψ, Category.assoc] using
      (congrArg (fun h ↦ ψ ≫ h ≫ (U ⨯ U).hom) (pullback.condition (f := P.hom.left)
        (g := P.hom.left))).symm
  let r₂ : p.over ⟶ P.left :=
    Over.homMk (ψ ≫ pullback.snd P.hom.left P.hom.left) hBase
  have hTarget :
      r₁ ≫ P.t = r₂ ≫ P.t := by
    apply Over.OverMorphism.ext
    change ψ ≫ pullback.fst P.hom.left P.hom.left ≫ P.t.left =
      ψ ≫ pullback.snd P.hom.left P.hom.left ≫ P.t.left
    simpa [r₁, r₂, PreRelation.t, Category.assoc] using
      congrArg (fun h ↦ ψ ≫ h ≫ (prod.fst (X := U)).left)
        (pullback.condition (f := P.hom.left) (g := P.hom.left))
  have hSource :
      r₁ ≫ P.s = r₂ ≫ P.s := by
    apply Over.OverMorphism.ext
    change ψ ≫ pullback.fst P.hom.left P.hom.left ≫ P.s.left =
      ψ ≫ pullback.snd P.hom.left P.hom.left ≫ P.s.left
    simpa [r₁, r₂, PreRelation.s, Category.assoc] using
      congrArg (fun h ↦ ψ ≫ h ≫ (prod.snd (X := U)).left)
        (pullback.condition (f := P.hom.left) (g := P.hom.left))
  have hPointMap :
      P.pointMap p.over r₁ = P.pointMap p.over r₂ := by
    rw [P.pointMap_apply, P.pointMap_apply]
    exact Prod.ext hTarget hSource
  have hr : r₁ = r₂ := h_injective p hPointMap
  have hEqualized' :
      @Eq (p.over.left ⟶ P.left.left)
        (ψ ≫ pullback.fst P.hom.left P.hom.left)
        (ψ ≫ pullback.snd P.hom.left P.hom.left) :=
    congrArg Over.Hom.left hr
  have hEqualized :
      ψ ≫ pullback.fst P.hom.left P.hom.left =
        ψ ≫ pullback.snd P.hom.left P.hom.left := by
    change @Eq
      ((Over.mk (ψ ≫ pullback.fst P.hom.left P.hom.left ≫ P.left.hom)).left ⟶ P.left.left)
      (ψ ≫ pullback.fst P.hom.left P.hom.left)
      (ψ ≫ pullback.snd P.hom.left P.hom.left)
    exact hEqualized'
  have hDiagonal :
      ψ = (ψ ≫ pullback.fst P.hom.left P.hom.left) ≫ pullback.diagonal P.hom.left := by
    apply pullback.hom_ext
    · simp [Category.assoc]
    · simpa [Category.assoc] using hEqualized.symm
  have hDiagonalApply :
      pullback.diagonal P.hom.left
          ((ψ ≫ pullback.fst P.hom.left P.hom.left) (IsLocalRing.closedPoint L)) =
        ψ (IsLocalRing.closedPoint L) := by
    rw [← Scheme.Hom.comp_apply]
    exact (congrArg (fun f ↦ f (IsLocalRing.closedPoint L)) hDiagonal).symm
  have hClosedPointMap :
      (e ≫ φ) (IsLocalRing.closedPoint L) = φ (IsLocalRing.closedPoint k) := by
    rw [Scheme.Hom.comp_apply]
    congr 1
    exact Subsingleton.elim _ _
  refine ⟨(ψ ≫ pullback.fst P.hom.left P.hom.left) (IsLocalRing.closedPoint L), ?_⟩
  calc
    pullback.diagonal P.hom.left
        ((ψ ≫ pullback.fst P.hom.left P.hom.left) (IsLocalRing.closedPoint L)) =
        ψ (IsLocalRing.closedPoint L) := hDiagonalApply
    _ = (e ≫ φ) (IsLocalRing.closedPoint L) := rfl
    _ = φ (IsLocalRing.closedPoint k) := hClosedPointMap
    _ = z := by
      dsimp [φ, k]
      exact Scheme.fromSpecResidueField_apply z
        (IsLocalRing.closedPoint ((pullback P.hom.left P.hom.left).residueField z))

/-- If one endpoint of a pre-relation is unramified and its point map is injective on
algebraically closed field-valued points, then its defining morphism is monic. -/
theorem monoHomOfPointMapInjective {S : Scheme.{u}} {U : Over S} (P : PreRelation U)
    [Unramified P.t.left]
    (h_injective : ∀ (p : FieldValuedPoint S) [IsAlgClosed p.K],
      Function.Injective (P.pointMap p.over)) :
    Mono P.hom := by
  have hOpen : IsOpenImmersion (pullback.diagonal P.hom.left) :=
    @AlgebraicGeometry.isOpenImmersion_diagonal_of_unramified _ _ P.hom.left
      (unramifiedHomLeft P)
  have hSurj : Surjective (pullback.diagonal P.hom.left) :=
    diagonalSurjectiveOfPointMapInjective P h_injective
  have hIso : IsIso (pullback.diagonal P.hom.left) :=
    (AlgebraicGeometry.isIso_iff_isOpenImmersion_and_surjective _).mpr ⟨hOpen, hSurj⟩
  have hMonoLeft : Mono P.hom.left :=
    (pullback.isIso_diagonal_iff P.hom.left).mp hIso
  exact Over.mono_of_mono_left P.hom (hk := hMonoLeft)

/-- Explicit identity, inverse, and composition morphisms satisfying the endpoint equations
assemble an unramified pre-relation with injective geometric point maps into a concrete internal
equivalence relation. -/
noncomputable def equivalenceRelationOfUnramified {S : Scheme.{u}} {U : Over S}
    (P : PreRelation U) [Unramified P.t.left]
    (h_injective : ∀ (p : FieldValuedPoint S) [IsAlgClosed p.K],
      Function.Injective (P.pointMap p.over))
    (e : U ⟶ P.left) (i : P.left ⟶ P.left) (c : pullback P.s P.t ⟶ P.left)
    (e_t : e ≫ P.t = 𝟙 U) (e_s : e ≫ P.s = 𝟙 U)
    (i_t : i ≫ P.t = P.s) (i_s : i ≫ P.s = P.t)
    (c_t : c ≫ P.t = pullback.fst P.s P.t ≫ P.t)
    (c_s : c ≫ P.s = pullback.snd P.s P.t ≫ P.s) :
    EquivalenceRelation P.t P.s where
  right_cancellation :=
    (@PreRelation.instJointlyMono₂ _ _ P (monoHomOfPointMapInjective P h_injective)).right_cancellation
  r := e
  s := i
  c := PullbackCone.mk (pullback.fst P.s P.t) (pullback.snd P.s P.t)
    pullback.condition
  isLimit := pullbackIsPullback P.s P.t
  t := c
  reflexivity₁ := e_t
  reflexivity₂ := e_s
  symmetry₁ := i_t
  symmetry₂ := i_s
  transitivity₁ := c_t
  transitivity₂ := c_s

/-- An unramified pre-relation whose relation on every algebraically closed field-valued point
is an equivalence relation, and whose identity, inverse, and composition morphisms satisfy the
endpoint equations, is an internal equivalence relation. -/
theorem isEquivalenceRelation_of_unramified {S : Scheme.{u}} {U : Over S} (P : PreRelation U)
    [Unramified P.t.left] [Unramified P.s.left]
    (h_points : ∀ (p : FieldValuedPoint S) [IsAlgClosed p.K],
      Function.Injective (P.pointMap p.over) ∧ Equivalence (P.pointRel p.over))
    (e : U ⟶ P.left) (i : P.left ⟶ P.left) (c : pullback P.s P.t ⟶ P.left)
    (e_t : e ≫ P.t = 𝟙 U) (e_s : e ≫ P.s = 𝟙 U)
    (i_t : i ≫ P.t = P.s) (i_s : i ≫ P.s = P.t)
    (c_t : c ≫ P.t = pullback.fst P.s P.t ≫ P.t)
    (c_s : c ≫ P.s = pullback.snd P.s P.t ≫ P.s) :
    IsEquivalenceRelation P.t P.s :=
  (equivalenceRelationOfUnramified P (fun p _ ↦ (h_points p).1)
    e i c e_t e_s i_t i_s c_t c_s).isEquivalenceRelation

end AlgebraicGeometry.Scheme.PreRelation
