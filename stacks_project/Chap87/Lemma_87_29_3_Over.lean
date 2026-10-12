/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.MorphismProperty.Comma
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
public import stacks_project.Chap87.Lemma_87_24_4_FiniteType

/-!
# Affine finite-type slice of a formal algebraic space

The category of morphisms `φ : U ⟶ Y` of affine formal algebraic spaces that
are of finite type is the full subcategory of the finite-type slice
`finiteTypeComma Y` on domains that admit a directed affine thickening
presentation.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry CategoryTheory.MorphismProperty
open AlgebraicGeometry.FormalAlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AffineFormalAlgebraicSpace

variable {S : Scheme.{u}}

/-- The finite-type slice of functors of points over `Y`: morphisms that are
representable by algebraic spaces and of finite type. -/
abbrev finiteTypeComma (Y : (Over S)ᵒᵖ ⥤ Type u) :=
  MorphismProperty.Over (@FormalAlgebraicSpace.FiniteType S) ⊤ Y

/-- `finiteTypeComma Y` is the finite-type slice
`MorphismProperty.Over (@FormalAlgebraicSpace.FiniteType S) ⊤ Y`. -/
theorem finiteTypeComma_def (Y : (Over S)ᵒᵖ ⥤ Type u) :
    finiteTypeComma Y =
      MorphismProperty.Over (@FormalAlgebraicSpace.FiniteType S) ⊤ Y :=
  sorry

/-- The object property selecting finite-type slice objects whose domain is an
affine formal algebraic space, presented as a directed affine thickening
colimit. -/
def isAffineFiniteTypeDomain (Y : (Over S)ᵒᵖ ⥤ Type u) :
    ObjectProperty (finiteTypeComma Y) :=
  fun U ↦
    ∃ (Λ : Type u) (_ : Preorder Λ) (_ : IsDirected Λ (· ≤ ·)) (D : Λ ⥤ Over S),
      FormalAlgebraicSpace.IsDirectedAffineThickeningColimit D U.left

/-- An object of the finite-type slice over `Y` lies in
`isAffineFiniteTypeDomain Y` if and only if its domain is a directed affine
thickening colimit. -/
theorem isAffineFiniteTypeDomain_iff {Y : (Over S)ᵒᵖ ⥤ Type u}
    {U : finiteTypeComma Y} :
    isAffineFiniteTypeDomain Y U ↔
      ∃ (Λ : Type u) (_ : Preorder Λ) (_ : IsDirected Λ (· ≤ ·)) (D : Λ ⥤ Over S),
        FormalAlgebraicSpace.IsDirectedAffineThickeningColimit D U.left :=
  sorry

/-- The category of morphisms `φ : U ⟶ Y` of affine formal algebraic spaces that
are of finite type. -/
abbrev AffineFiniteTypeOver (Y : (Over S)ᵒᵖ ⥤ Type u) :=
  (isAffineFiniteTypeDomain Y).FullSubcategory

/-- `AffineFiniteTypeOver Y` is the full subcategory of `finiteTypeComma Y` on
affine formal algebraic space domains. -/
theorem AffineFiniteTypeOver_def (Y : (Over S)ᵒᵖ ⥤ Type u) :
    AffineFiniteTypeOver Y = (isAffineFiniteTypeDomain Y).FullSubcategory :=
  sorry

/-- Construct an object of `AffineFiniteTypeOver Y` from a finite-type morphism
of affine formal algebraic spaces into `Y`. -/
def AffineFiniteTypeOver.mk {Y : (Over S)ᵒᵖ ⥤ Type u}
    {U : (Over S)ᵒᵖ ⥤ Type u} (φ : U ⟶ Y)
    [FormalAlgebraicSpace.FiniteType φ]
    (hU :
      ∃ (Λ : Type u) (_ : Preorder Λ) (_ : IsDirected Λ (· ≤ ·)) (D : Λ ⥤ Over S),
        FormalAlgebraicSpace.IsDirectedAffineThickeningColimit D U) :
    AffineFiniteTypeOver Y where
  obj := MorphismProperty.Over.mk ⊤ φ inferInstance
  property := hU

/-- The underlying functor of points of `AffineFiniteTypeOver.mk φ hU` is the
domain of `φ`. -/
theorem AffineFiniteTypeOver.mk_left {Y : (Over S)ᵒᵖ ⥤ Type u}
    {U : (Over S)ᵒᵖ ⥤ Type u} (φ : U ⟶ Y)
    [FormalAlgebraicSpace.FiniteType φ]
    (hU :
      ∃ (Λ : Type u) (_ : Preorder Λ) (_ : IsDirected Λ (· ≤ ·)) (D : Λ ⥤ Over S),
        FormalAlgebraicSpace.IsDirectedAffineThickeningColimit D U) :
    (AffineFiniteTypeOver.mk φ hU).obj.left = U :=
  sorry

/-- The structural morphism of `AffineFiniteTypeOver.mk φ hU` is `φ`. -/
theorem AffineFiniteTypeOver.mk_hom {Y : (Over S)ᵒᵖ ⥤ Type u}
    {U : (Over S)ᵒᵖ ⥤ Type u} (φ : U ⟶ Y)
    [FormalAlgebraicSpace.FiniteType φ]
    (hU :
      ∃ (Λ : Type u) (_ : Preorder Λ) (_ : IsDirected Λ (· ≤ ·)) (D : Λ ⥤ Over S),
        FormalAlgebraicSpace.IsDirectedAffineThickeningColimit D U) :
    (AffineFiniteTypeOver.mk φ hU).obj.hom = φ :=
  sorry

/-- The structural morphism of an object of `AffineFiniteTypeOver Y` is of
finite type. -/
instance instFiniteType_affineFiniteTypeOver {Y : (Over S)ᵒᵖ ⥤ Type u}
    (U : AffineFiniteTypeOver Y) :
    FormalAlgebraicSpace.FiniteType U.obj.hom :=
  U.obj.prop

/-- The domain of an object of `AffineFiniteTypeOver Y` is a directed affine
thickening colimit. -/
theorem exists_isDirectedAffineThickeningColimit_affineFiniteTypeOver
    {Y : (Over S)ᵒᵖ ⥤ Type u} (U : AffineFiniteTypeOver Y) :
    ∃ (Λ : Type u) (_ : Preorder Λ) (_ : IsDirected Λ (· ≤ ·)) (D : Λ ⥤ Over S),
      FormalAlgebraicSpace.IsDirectedAffineThickeningColimit D U.obj.left :=
  U.property

end AlgebraicGeometry.AffineFormalAlgebraicSpace
