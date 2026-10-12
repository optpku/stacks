/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.CommSq
public import stacks_project.Chap67.Definition_67_13_2_InverseImage
public import stacks_project.Chap67.Lemma_67_13_5_Complement
public import stacks_project.Chap67.Lemma_67_28_8_FinitePresentation
public import stacks_project.Chap67.Lemma_67_30_5_Flat

/-!
# Formal glueing of algebraic spaces along a closed immersion

A quasi-compact quasi-separated morphism `f : Y ⟶ X` of algebraic spaces, together with a
finite-presentation closed immersion `i : Z ⟶ X` such that `inverseImageTo f i` is an
isomorphism and `f` is flat at every point of the inverse image, determines the restriction
`restrictToComplement f i` of `f` to the open complements of `Z` and of `inverseImageι f i`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Opposite

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- The composite of the complement inclusion of `inverseImageι f i` with `f` misses the
closed image of `i`. -/
theorem restrictToComplement_misses {S : Scheme.{u}} {X Y Z : AlgebraicSpace S}
    (f : Y ⟶ X) (i : Z ⟶ X) [IsClosedImmersion i] :
    ∀ (W : (Over S)ᵒᵖ)
      (t : (closedImmersionComplement (inverseImageι f i)).functorOfPoints.obj W),
      missesClosedImage i ((closedImmersionComplementι (inverseImageι f i) ≫ f).app W t) :=
  sorry

/-- The restriction of `f : Y ⟶ X` to the open complements of `i` and of
`inverseImageι f i`. -/
def restrictToComplement {S : Scheme.{u}} {X Y Z : AlgebraicSpace S}
    (f : Y ⟶ X) (i : Z ⟶ X) [IsClosedImmersion i] :
    closedImmersionComplement (inverseImageι f i) ⟶ closedImmersionComplement i where
  app W := TypeCat.ofHom fun t ↦
    ⟨(closedImmersionComplementι (inverseImageι f i) ≫ f).app W t,
      restrictToComplement_misses f i W t⟩
  naturality := sorry

/-- The underlying map of `restrictToComplement f i` on sections is the composite
`closedImmersionComplementι (inverseImageι f i) ≫ f`. -/
theorem restrictToComplement_eq {S : Scheme.{u}} {X Y Z : AlgebraicSpace S}
    (f : Y ⟶ X) (i : Z ⟶ X) [IsClosedImmersion i] {W : (Over S)ᵒᵖ}
    (t : (closedImmersionComplement (inverseImageι f i)).functorOfPoints.obj W) :
    (closedImmersionComplementι i).app W ((restrictToComplement f i).app W t) =
      (closedImmersionComplementι (inverseImageι f i) ≫ f).app W t :=
  sorry

/-- The square with vertices the two complements, `Y`, and `X` commutes:
`restrictToComplement f i ≫ closedImmersionComplementι i =
closedImmersionComplementι (inverseImageι f i) ≫ f`. -/
theorem restrictToComplement_comp {S : Scheme.{u}} {X Y Z : AlgebraicSpace S}
    (f : Y ⟶ X) (i : Z ⟶ X) [IsClosedImmersion i] :
    restrictToComplement f i ≫ closedImmersionComplementι i =
      closedImmersionComplementι (inverseImageι f i) ≫ f :=
  sorry

/-- The commutative square of complement inclusions over `f`. -/
theorem restrictToComplementCommSq {S : Scheme.{u}} {X Y Z : AlgebraicSpace S}
    (f : Y ⟶ X) (i : Z ⟶ X) [IsClosedImmersion i] :
    CommSq (restrictToComplement f i) (closedImmersionComplementι (inverseImageι f i))
      (closedImmersionComplementι i) f :=
  sorry

/-- The standing formal-glueing hypotheses on `f : Y ⟶ X` and a finite-presentation
closed immersion `i : Z ⟶ X`: `inverseImageTo f i` is an isomorphism and `f` is flat at
every point of `pointsImage (inverseImageι f i)`. -/
class IsFormalGlueing {S : Scheme.{u}} {X Y Z : AlgebraicSpace S}
    (f : Y ⟶ X) (i : Z ⟶ X)
    [QuasiCompact f] [QuasiSeparated f] [IsClosedImmersion i] [FinitePresentation i] : Prop where
  /-- The comparison `inverseImageTo f i` is an isomorphism. -/
  [inverseImageTo_isIso : IsIso (inverseImageTo f i)]
  /-- `f` is flat at every point of the inverse image of `i`. -/
  flatAt_inverseImage :
    ∀ x : Points Y, x ∈ pointsImage (inverseImageι f i) → FlatAt f x

namespace IsFormalGlueing

/-- Pack an isomorphism `inverseImageTo f i` together with pointwise flatness on
`pointsImage (inverseImageι f i)` into the formal-glueing situation. -/
theorem of {S : Scheme.{u}} {X Y Z : AlgebraicSpace S} (f : Y ⟶ X) (i : Z ⟶ X)
    [QuasiCompact f] [QuasiSeparated f] [IsClosedImmersion i] [FinitePresentation i]
    [IsIso (inverseImageTo f i)]
    (h : ∀ x : Points Y, x ∈ pointsImage (inverseImageι f i) → FlatAt f x) :
    IsFormalGlueing f i :=
  sorry

/-- Formal glueing is the conjunction of an isomorphism `inverseImageTo f i` and
pointwise flatness of `f` on `pointsImage (inverseImageι f i)`. -/
theorem iff {S : Scheme.{u}} {X Y Z : AlgebraicSpace S} (f : Y ⟶ X) (i : Z ⟶ X)
    [QuasiCompact f] [QuasiSeparated f] [IsClosedImmersion i] [FinitePresentation i] :
    IsFormalGlueing f i ↔
      IsIso (inverseImageTo f i) ∧
        ∀ x : Points Y, x ∈ pointsImage (inverseImageι f i) → FlatAt f x :=
  sorry

/-- The two extra conditions of the formal-glueing situation. -/
theorem spec {S : Scheme.{u}} {X Y Z : AlgebraicSpace S} (f : Y ⟶ X) (i : Z ⟶ X)
    [QuasiCompact f] [QuasiSeparated f] [IsClosedImmersion i] [FinitePresentation i]
    [IsFormalGlueing f i] :
    IsIso (inverseImageTo f i) ∧
      ∀ x : Points Y, x ∈ pointsImage (inverseImageι f i) → FlatAt f x :=
  sorry

/-- Formal glueing implies flatness of `f` at every point of
`pointsImage (inverseImageι f i)`. -/
theorem flatAt {S : Scheme.{u}} {X Y Z : AlgebraicSpace S} (f : Y ⟶ X) (i : Z ⟶ X)
    [QuasiCompact f] [QuasiSeparated f] [IsClosedImmersion i] [FinitePresentation i]
    [IsFormalGlueing f i] {x : Points Y}
    (hx : x ∈ pointsImage (inverseImageι f i)) : FlatAt f x :=
  sorry

/-- The identity on `X` is a formal-glueing morphism relative to any finite-presentation
closed immersion `i : Z ⟶ X`. -/
instance id {S : Scheme.{u}} {X Z : AlgebraicSpace S} (i : Z ⟶ X)
    [IsClosedImmersion i] [FinitePresentation i] : IsFormalGlueing (𝟙 X) i :=
  sorry

/-- A globally flat morphism with isomorphic inverse image along `i` is a formal-glueing
morphism. -/
instance of_flat {S : Scheme.{u}} {X Y Z : AlgebraicSpace S} (f : Y ⟶ X) (i : Z ⟶ X)
    [QuasiCompact f] [QuasiSeparated f] [IsClosedImmersion i] [FinitePresentation i]
    [IsIso (inverseImageTo f i)] [Flat f] : IsFormalGlueing f i :=
  sorry

end IsFormalGlueing

end AlgebraicGeometry.AlgebraicSpace
