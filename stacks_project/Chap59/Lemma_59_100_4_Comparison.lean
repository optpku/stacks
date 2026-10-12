/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.MorphismProperty.Comma
public import stacks_project.Chap59.Lemma_59_100_3_Comparison

/-!
# Small-étale / big-fppf iso-comma comparison

The iso-comma of `a_X⁻¹` and `f_big,fppf⁻¹`, together with the comparison
functor sending an étale sheaf on `Y` to the triple
`(f_small⁻¹ ℱ, a_Y⁻¹ ℱ, can)`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.MorphismProperty AlgebraicGeometry
open AlgebraicGeometry.Scheme
open AlgebraicGeometry.Scheme.Etale
open scoped MorphismOfTopoiIn

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Etale.SmallToBig

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- The iso-comma of `a_X⁻¹` and `f_big,fppf⁻¹`, whose objects are triples
`(𝒢, ℋ, α)` with `𝒢` an étale sheaf on `X`, `ℋ` an fppf sheaf on `Y`, and
`α : a_X⁻¹ 𝒢 ⟶ f_big,fppf⁻¹ ℋ` an isomorphism. -/
abbrev fppfSmallIsoComma :=
  (isomorphisms _).Comma
    ((fppfComparison X)⁻¹) ((Fppf.Big.morphismOfTopoi f)⁻¹) ⊤ ⊤

/-- Source-facing constructor for an object of `fppfSmallIsoComma f` from a
triple `(𝒢, ℋ, α)` with `α` an isomorphism. -/
noncomputable def fppfSmallIsoComma.mk
    (G : Sheaf X.smallEtaleTopology (Type (u + 1)))
    (H : Sheaf (Scheme.fppfTopology.over Y) (Type (u + 1)))
    (α : ((fppfComparison X)⁻¹).obj G ≅ ((Fppf.Big.morphismOfTopoi f)⁻¹).obj H) :
    fppfSmallIsoComma f where
  left := G
  right := H
  hom := α.hom
  prop := inferInstance

section TypeSheaves

variable [HasSheafify X.smallEtaleTopology (Type (u + 1))]
variable [HasSheafify Y.smallEtaleTopology (Type (u + 1))]

/-- Underlying comma functor sending `ℱ` to the triple
`(f_small⁻¹ ℱ, a_Y⁻¹ ℱ, can)`, before restricting to isomorphisms. -/
noncomputable def fppfSmallIsoCommaToComma :
    Sheaf Y.smallEtaleTopology (Type (u + 1)) ⥤
      Comma ((fppfComparison X)⁻¹) ((Fppf.Big.morphismOfTopoi f)⁻¹) where
  obj F :=
    { left := ((smallMorphism f)⁻¹).obj F
      right := ((fppfComparison Y)⁻¹).obj F
      hom := ((fppfSmallInverseImageSquare f).symm.app F).hom }
  map φ :=
    { left := ((smallMorphism f)⁻¹).map φ
      right := ((fppfComparison Y)⁻¹).map φ
      w := (fppfSmallInverseImageSquare f).symm.hom.naturality φ }

/-- The comparison functor `Sh(Y_étale) ⥤ fppfSmallIsoComma f` sending `ℱ` to
`(f_small⁻¹ ℱ, a_Y⁻¹ ℱ, can)`. -/
noncomputable def fppfSmallIsoCommaFunctor :
    Sheaf Y.smallEtaleTopology (Type (u + 1)) ⥤ fppfSmallIsoComma f :=
  MorphismProperty.Comma.lift (fppfSmallIsoCommaToComma f)
    (fun F ↦ Iso.isIso_hom ((fppfSmallInverseImageSquare f).symm.app F))
    (fun _ ↦ trivial) (fun _ ↦ trivial)

/-- The left component of `fppfSmallIsoCommaFunctor f` is inverse image along
`f_small`. -/
theorem fppfSmallIsoCommaFunctor_obj_left
    (F : Sheaf Y.smallEtaleTopology (Type (u + 1))) :
    ((fppfSmallIsoCommaFunctor f).obj F).left = ((smallMorphism f)⁻¹).obj F :=
  sorry

/-- The right component of `fppfSmallIsoCommaFunctor f` is inverse image along
`a_Y`. -/
theorem fppfSmallIsoCommaFunctor_obj_right
    (F : Sheaf Y.smallEtaleTopology (Type (u + 1))) :
    ((fppfSmallIsoCommaFunctor f).obj F).right = ((fppfComparison Y)⁻¹).obj F :=
  sorry

/-- The structural map of `fppfSmallIsoCommaFunctor f` is the canonical
isomorphism `can` from the inverse-image square. -/
theorem fppfSmallIsoCommaFunctor_obj_hom
    (F : Sheaf Y.smallEtaleTopology (Type (u + 1))) :
    ((fppfSmallIsoCommaFunctor f).obj F).hom =
      ((fppfSmallInverseImageSquare f).symm.app F).hom :=
  sorry

end TypeSheaves

end AlgebraicGeometry.Scheme.Etale.SmallToBig

end

end
