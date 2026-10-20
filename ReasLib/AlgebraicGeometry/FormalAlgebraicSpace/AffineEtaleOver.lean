/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.MorphismProperty.Comma
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
public import ReasLib.AlgebraicGeometry.FormalAlgebraicSpace.EtaleOver

/-!
# Affine étale slice of a formal algebraic space

The category of morphisms `φ : U ⟶ Y` of affine formal algebraic spaces that
are representable by algebraic spaces and étale is the full subcategory of the
étale slice `etaleComma Y` on domains that admit a directed affine thickening
presentation.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry CategoryTheory.MorphismProperty
open AlgebraicGeometry.FormalAlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AffineFormalAlgebraicSpace

variable {S : Scheme.{u}}

/-- The object property selecting étale slice objects whose domain is an affine
formal algebraic space, presented as a directed affine thickening colimit. -/
def isAffineFormalDomain (Y : (Over S)ᵒᵖ ⥤ Type u) :
    ObjectProperty (etaleComma Y) :=
  fun U =>
    ∃ (Λ : Type u) (_ : Preorder Λ) (_ : IsDirected Λ (· ≤ ·)) (D : Λ ⥤ Over S),
      FormalAlgebraicSpace.IsDirectedAffineThickeningColimit D U.left

/-- An object of the étale slice over `Y` lies in `isAffineFormalDomain Y` if and
only if its domain is a directed affine thickening colimit. -/
theorem isAffineFormalDomain_iff {Y : (Over S)ᵒᵖ ⥤ Type u} {U : etaleComma Y} :
    isAffineFormalDomain Y U ↔
      ∃ (Λ : Type u) (_ : Preorder Λ) (_ : IsDirected Λ (· ≤ ·)) (D : Λ ⥤ Over S),
        FormalAlgebraicSpace.IsDirectedAffineThickeningColimit D U.left :=
  Iff.rfl

/-- The category of morphisms `φ : U ⟶ Y` of affine formal algebraic spaces that
are representable by algebraic spaces and étale. -/
abbrev AffineEtaleOver (Y : (Over S)ᵒᵖ ⥤ Type u) :=
  (isAffineFormalDomain Y).FullSubcategory

/-- `AffineEtaleOver Y` is the full subcategory of `etaleComma Y` on affine
formal algebraic space domains. -/
theorem AffineEtaleOver_def (Y : (Over S)ᵒᵖ ⥤ Type u) :
    AffineEtaleOver Y = (isAffineFormalDomain Y).FullSubcategory :=
  rfl

/-- Construct an object of `AffineEtaleOver Y` from an étale morphism of affine
formal algebraic spaces into `Y`. -/
def AffineEtaleOver.mk {Y : (Over S)ᵒᵖ ⥤ Type u} {U : (Over S)ᵒᵖ ⥤ Type u}
    (φ : U ⟶ Y) [FormalAlgebraicSpace.Etale φ]
    (hU :
      ∃ (Λ : Type u) (_ : Preorder Λ) (_ : IsDirected Λ (· ≤ ·)) (D : Λ ⥤ Over S),
        FormalAlgebraicSpace.IsDirectedAffineThickeningColimit D U) :
    AffineEtaleOver Y where
  obj := MorphismProperty.Over.mk ⊤ φ inferInstance
  property := hU

/-- The underlying functor of points of `AffineEtaleOver.mk φ hU` is the domain
of `φ`. -/
@[simp]
theorem AffineEtaleOver.mk_left {Y : (Over S)ᵒᵖ ⥤ Type u}
    {U : (Over S)ᵒᵖ ⥤ Type u} (φ : U ⟶ Y) [FormalAlgebraicSpace.Etale φ]
    (hU :
      ∃ (Λ : Type u) (_ : Preorder Λ) (_ : IsDirected Λ (· ≤ ·)) (D : Λ ⥤ Over S),
        FormalAlgebraicSpace.IsDirectedAffineThickeningColimit D U) :
    (AffineEtaleOver.mk φ hU).obj.left = U :=
  rfl

/-- The structural morphism of `AffineEtaleOver.mk φ hU` is `φ`. -/
@[simp]
theorem AffineEtaleOver.mk_hom {Y : (Over S)ᵒᵖ ⥤ Type u}
    {U : (Over S)ᵒᵖ ⥤ Type u} (φ : U ⟶ Y) [FormalAlgebraicSpace.Etale φ]
    (hU :
      ∃ (Λ : Type u) (_ : Preorder Λ) (_ : IsDirected Λ (· ≤ ·)) (D : Λ ⥤ Over S),
        FormalAlgebraicSpace.IsDirectedAffineThickeningColimit D U) :
    (AffineEtaleOver.mk φ hU).obj.hom = φ :=
  rfl

/-- The structural morphism of an object of `AffineEtaleOver Y` is étale. -/
instance instEtale_affineEtaleOver {Y : (Over S)ᵒᵖ ⥤ Type u}
    (U : AffineEtaleOver Y) : FormalAlgebraicSpace.Etale U.obj.hom :=
  U.obj.prop

/-- The domain of an object of `AffineEtaleOver Y` is a directed affine
thickening colimit. -/
theorem exists_isDirectedAffineThickeningColimit_affineEtaleOver
    {Y : (Over S)ᵒᵖ ⥤ Type u} (U : AffineEtaleOver Y) :
    ∃ (Λ : Type u) (_ : Preorder Λ) (_ : IsDirected Λ (· ≤ ·)) (D : Λ ⥤ Over S),
      FormalAlgebraicSpace.IsDirectedAffineThickeningColimit D U.obj.left :=
  U.property

end AlgebraicGeometry.AffineFormalAlgebraicSpace
