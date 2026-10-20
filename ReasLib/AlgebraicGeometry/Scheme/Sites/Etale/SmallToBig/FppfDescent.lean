module

public import Mathlib.CategoryTheory.MorphismProperty.Comma
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.SmallToBig.FppfPushforward
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap

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

/-- An étale sheaf `𝒢` on `X`, an fppf sheaf `ℋ` on `Y`, and an isomorphism
`a_X⁻¹ 𝒢 ≅ f_big,fppf⁻¹ ℋ` determine an object of `fppfSmallIsoComma f`. -/
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

/-- The comparison functor `Sh(Y_étale) ⥤ fppfSmallIsoComma f` sending `ℱ` to
`(f_small⁻¹ ℱ, a_Y⁻¹ ℱ, can)`. -/
noncomputable def fppfSmallIsoCommaFunctor :
    Sheaf Y.smallEtaleTopology (Type (u + 1)) ⥤ fppfSmallIsoComma f :=
  MorphismProperty.Comma.lift
    { obj F :=
        { left := ((smallMorphism f)⁻¹).obj F
          right := ((fppfComparison Y)⁻¹).obj F
          hom := ((fppfSmallInverseImageSquare f).symm.app F).hom }
      map φ :=
        { left := ((smallMorphism f)⁻¹).map φ
          right := ((fppfComparison Y)⁻¹).map φ
          w := (fppfSmallInverseImageSquare f).symm.hom.naturality φ } }
    (fun F ↦ Iso.isIso_hom ((fppfSmallInverseImageSquare f).symm.app F))
    (fun _ ↦ trivial) (fun _ ↦ trivial)

/-- The left component of `fppfSmallIsoCommaFunctor f` is inverse image along
`f_small`. -/
theorem fppfSmallIsoCommaFunctor_obj_left
    (F : Sheaf Y.smallEtaleTopology (Type (u + 1))) :
    ((fppfSmallIsoCommaFunctor f).obj F).left = ((smallMorphism f)⁻¹).obj F :=
  rfl

/-- The right component of `fppfSmallIsoCommaFunctor f` is inverse image along
`a_Y`. -/
theorem fppfSmallIsoCommaFunctor_obj_right
    (F : Sheaf Y.smallEtaleTopology (Type (u + 1))) :
    ((fppfSmallIsoCommaFunctor f).obj F).right = ((fppfComparison Y)⁻¹).obj F :=
  rfl

/-- The structural map of `fppfSmallIsoCommaFunctor f` is the canonical
isomorphism `can` from the inverse-image square. -/
theorem fppfSmallIsoCommaFunctor_obj_hom
    (F : Sheaf Y.smallEtaleTopology (Type (u + 1))) :
    ((fppfSmallIsoCommaFunctor f).obj F).hom =
      ((fppfSmallInverseImageSquare f).symm.app F).hom :=
  rfl

/-- For a flat, locally finitely presented, surjective morphism of schemes,
the comparison from small étale sheaves on the target to compatible small étale
and big fppf sheaves is an equivalence. -/
noncomputable instance fppfSmallIsoCommaFunctor_isEquivalence
    [Flat f] [LocallyOfFinitePresentation f] [Surjective f] :
    (fppfSmallIsoCommaFunctor f).IsEquivalence := sorry

end TypeSheaves

end AlgebraicGeometry.Scheme.Etale.SmallToBig

end

end
