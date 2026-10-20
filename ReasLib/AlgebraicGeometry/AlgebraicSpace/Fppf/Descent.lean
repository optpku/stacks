/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.MorphismProperty.Comma
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Fppf.InverseImage
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.Flat
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.LocallyOfFinitePresentation
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Surjective

/-!
# Small-étale / big-fppf iso-comma comparison of algebraic spaces

The iso-comma of `a_X⁻¹` and `f_big,fppf⁻¹`, together with the comparison
functor sending an étale sheaf on `Y` to the triple
`(f_small⁻¹ ℱ, a_Y⁻¹ ℱ, can)`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.MorphismProperty AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.Etale
open scoped MorphismOfTopoiIn

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Etale.SmallToBig

variable {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)

/-- The iso-comma of `a_X⁻¹` and `f_big,fppf⁻¹`, whose objects are triples
`(𝒢, ℋ, α)` with `𝒢` an étale sheaf on `X`, `ℋ` an fppf sheaf on `Y`, and
`α : a_X⁻¹ 𝒢 ⟶ f_big,fppf⁻¹ ℋ` an isomorphism. -/
abbrev fppfSmallIsoComma :=
  (isomorphisms _).Comma
    ((fppfComparison X)⁻¹) ((CategoryTheory.Over.Site.morphismOfTopoi.{u + 1, u + 1, u + 1} (fppfTopology S) f)⁻¹) ⊤ ⊤

/-- An étale sheaf on `X`, an fppf sheaf on `Y`, and a specified isomorphism
`a_X⁻¹ 𝒢 ≅ f_big,fppf⁻¹ ℋ` determine an object of `fppfSmallIsoComma f`. -/
noncomputable def fppfSmallIsoComma.mk
    (G : Sheaf (smallEtaleTopology X) (Type (u + 1)))
    (H : Sheaf (overFppfTopology Y) (Type (u + 1)))
    (α : ((fppfComparison X)⁻¹).obj G ≅ ((CategoryTheory.Over.Site.morphismOfTopoi.{u + 1, u + 1, u + 1} (fppfTopology S) f)⁻¹).obj H) :
    fppfSmallIsoComma f where
  left := G
  right := H
  hom := α.hom
  prop := inferInstance

/-- The comparison functor `Sh(Y_étale) ⥤ fppfSmallIsoComma f` sending `ℱ` to
`(f_small⁻¹ ℱ, a_Y⁻¹ ℱ, can)`. -/
noncomputable def fppfSmallIsoCommaFunctor :
    Sheaf (smallEtaleTopology Y) (Type (u + 1)) ⥤ fppfSmallIsoComma f :=
  MorphismProperty.Comma.lift
    { obj F :=
        { left := ((smallEtaleMorphismOfTopoi f)⁻¹).obj F
          right := ((fppfComparison Y)⁻¹).obj F
          hom := ((fppfSmallInverseImageSquare f).symm.app F).hom }
      map φ :=
        { left := ((smallEtaleMorphismOfTopoi f)⁻¹).map φ
          right := ((fppfComparison Y)⁻¹).map φ
          w := (fppfSmallInverseImageSquare f).symm.hom.naturality φ } }
    (fun F ↦ Iso.isIso_hom ((fppfSmallInverseImageSquare f).symm.app F))
    (fun _ ↦ trivial) (fun _ ↦ trivial)

/-- The left component of `fppfSmallIsoCommaFunctor f` is inverse image along
`f_small`. -/
theorem fppfSmallIsoCommaFunctor_obj_left
    (F : Sheaf (smallEtaleTopology Y) (Type (u + 1))) :
    ((fppfSmallIsoCommaFunctor f).obj F).left = ((smallEtaleMorphismOfTopoi f)⁻¹).obj F :=
  rfl

/-- The right component of `fppfSmallIsoCommaFunctor f` is inverse image along
`a_Y`. -/
theorem fppfSmallIsoCommaFunctor_obj_right
    (F : Sheaf (smallEtaleTopology Y) (Type (u + 1))) :
    ((fppfSmallIsoCommaFunctor f).obj F).right = ((fppfComparison Y)⁻¹).obj F :=
  rfl

/-- The structural map of `fppfSmallIsoCommaFunctor f` is the canonical
isomorphism `can` from the inverse-image square. -/
theorem fppfSmallIsoCommaFunctor_obj_hom
    (F : Sheaf (smallEtaleTopology Y) (Type (u + 1))) :
    ((fppfSmallIsoCommaFunctor f).obj F).hom =
      ((fppfSmallInverseImageSquare f).symm.app F).hom :=
  rfl

/-- For a flat, locally finitely presented, surjective morphism of algebraic spaces,
the canonical functor from small étale sheaves on the target to compatible small
étale sheaves on the source and big fppf sheaves on the target is an equivalence. -/
noncomputable instance fppfSmallIsoCommaFunctor_isEquivalence
    [Flat f] [LocallyOfFinitePresentation f] [Surjective f] :
    (fppfSmallIsoCommaFunctor f).IsEquivalence := sorry

end AlgebraicGeometry.AlgebraicSpace.Etale.SmallToBig

end

end
