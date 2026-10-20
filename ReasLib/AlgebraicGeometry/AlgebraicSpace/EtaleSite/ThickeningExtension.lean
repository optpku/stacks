module

public import Mathlib.CategoryTheory.Equivalence
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs
public import Mathlib.CategoryTheory.MorphismProperty.Comma
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtaleSite.Localization
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtaleSite.Thickening
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Thickening.FirstOrder

/-!
# Étale extension along thickenings of algebraic spaces

The equivalence of spaces-étale sites along a thickening constructs an étale
extension, its closed immersion, and comparison maps from cartesian étale lifts.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace Limits

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- The object of `Y'_spaces,étale` obtained as the inverse image of an étale
morphism `Z ⟶ Y` along a thickening `Y ⊂ Y'`. -/
noncomputable def etaleExtendObj {S : Scheme.{u}} {Y Z Y' : AlgebraicSpace S}
    (fZY : Z ⟶ Y) (iY : Y ⟶ Y') [Etale fZY] [IsThickening iY] :
    spacesEtaleSite Y' :=
  (spacesEtalePullback iY).inv.obj (spacesEtaleSite.mk fZY)

/-- The algebraic space `Z'` obtained by étale inverse image of `Z ⟶ Y` along a
thickening `Y ⊂ Y'`. -/
noncomputable abbrev etaleExtend {S : Scheme.{u}} {Y Z Y' : AlgebraicSpace S}
    (fZY : Z ⟶ Y) (iY : Y ⟶ Y') [Etale fZY] [IsThickening iY] :
    AlgebraicSpace S :=
  (etaleExtendObj fZY iY).left

/-- The chosen étale extension morphism `Z' ⟶ Y'` along a thickening
`Y ⊂ Y'`, unique up to the canonical identification of étale lifts. -/
noncomputable abbrev etaleExtendHom {S : Scheme.{u}} {Y Z Y' : AlgebraicSpace S}
    (fZY : Z ⟶ Y) (iY : Y ⟶ Y') [Etale fZY] [IsThickening iY] :
    etaleExtend fZY iY ⟶ Y' :=
  (etaleExtendObj fZY iY).hom

/-- The closed immersion `Z ⊂ Z'` induced by the counit identification
`Y ×_{Y'} Z' ≅ Z`. -/
noncomputable def etaleExtendImmersion {S : Scheme.{u}} {Y Z Y' : AlgebraicSpace S}
    (fZY : Z ⟶ Y) (iY : Y ⟶ Y') [Etale fZY] [IsThickening iY] :
    Z ⟶ etaleExtend fZY iY :=
  ((spacesEtalePullback iY).objObjPreimageIso (spacesEtaleSite.mk fZY)).inv.left ≫
    pullback.fst (etaleExtendHom fZY iY) iY

/-- The underlying space of `etaleExtendObj` is `etaleExtend`. -/
@[simp]
theorem etaleExtendObj_left {S : Scheme.{u}} {Y Z Y' : AlgebraicSpace S}
    (fZY : Z ⟶ Y) (iY : Y ⟶ Y') [Etale fZY] [IsThickening iY] :
    (etaleExtendObj fZY iY).left = etaleExtend fZY iY :=
  rfl

/-- The structural morphism of `etaleExtendObj` is `etaleExtendHom`. -/
@[simp]
theorem etaleExtendHom_eq {S : Scheme.{u}} {Y Z Y' : AlgebraicSpace S}
    (fZY : Z ⟶ Y) (iY : Y ⟶ Y') [Etale fZY] [IsThickening iY] :
    (etaleExtendObj fZY iY).hom = etaleExtendHom fZY iY :=
  rfl

/-- The ambient morphism of étale inverse image is étale. -/
instance etaleExtendHom_etale {S : Scheme.{u}} {Y Z Y' : AlgebraicSpace S}
    (fZY : Z ⟶ Y) (iY : Y ⟶ Y') [Etale fZY] [IsThickening iY] :
    Etale (etaleExtendHom fZY iY) :=
  (etaleExtendObj fZY iY).prop

/-- Étale inverse image realises the fibre product identification
`Z = Y ×_{Y'} Z'`. -/
theorem etaleExtend_isPullback {S : Scheme.{u}} {Y Z Y' : AlgebraicSpace S}
    (fZY : Z ⟶ Y) (iY : Y ⟶ Y') [Etale fZY] [IsThickening iY] :
    IsPullback (etaleExtendImmersion fZY iY) fZY (etaleExtendHom fZY iY) iY :=
  sorry

/-- The closed immersion of étale inverse image along a first-order thickening
is again a first-order thickening. -/
instance etaleExtendImmersion_isFirstOrderThickening
    {S : Scheme.{u}} {Y Z Y' : AlgebraicSpace S}
    (fZY : Z ⟶ Y) (iY : Y ⟶ Y') [Etale fZY] [IsFirstOrderThickening iY] :
    IsFirstOrderThickening (etaleExtendImmersion fZY iY) :=
  sorry

/-- The comparison morphism over `Y'` from an étale cartesian lift to the
canonical inverse-image object. -/
noncomputable def etaleExtendCompare {S : Scheme.{u}} {Y Z Y' Z' : AlgebraicSpace S}
    (fZY : Z ⟶ Y) (iY : Y ⟶ Y') (iZ : Z ⟶ Z') (fZ' : Z' ⟶ Y')
    [Etale fZY] [IsThickening iY] [Etale fZ']
    (h : IsPullback iZ fZY fZ' iY) :
    Z' ⟶ etaleExtend fZY iY :=
  ((spacesEtalePullback iY).asEquivalence.unit.app (spacesEtaleSite.mk fZ') ≫
      (spacesEtalePullback iY).inv.map
        (MorphismProperty.Over.isoMk h.isoPullback.symm
          (IsPullback.isoPullback_inv_snd h)).hom).left

/-- The comparison morphism of an étale cartesian lift lies over `Y'`. -/
theorem etaleExtendCompare_comp {S : Scheme.{u}} {Y Z Y' Z' : AlgebraicSpace S}
    (fZY : Z ⟶ Y) (iY : Y ⟶ Y') (iZ : Z ⟶ Z') (fZ' : Z' ⟶ Y')
    [Etale fZY] [IsThickening iY] [Etale fZ']
    (h : IsPullback iZ fZY fZ' iY) :
    etaleExtendCompare fZY iY iZ fZ' h ≫ etaleExtendHom fZY iY = fZ' :=
  sorry

/-- The comparison morphism of an étale cartesian lift identifies the closed
immersions from `Z`. -/
theorem etaleExtendCompare_immersion {S : Scheme.{u}} {Y Z Y' Z' : AlgebraicSpace S}
    (fZY : Z ⟶ Y) (iY : Y ⟶ Y') (iZ : Z ⟶ Z') (fZ' : Z' ⟶ Y')
    [Etale fZY] [IsThickening iY] [Etale fZ']
    (h : IsPullback iZ fZY fZ' iY) :
    iZ ≫ etaleExtendCompare fZY iY iZ fZ' h = etaleExtendImmersion fZY iY :=
  sorry

/-- A morphism of thickenings over `Y'` from an étale cartesian lift to the
canonical inverse-image object is the comparison morphism. -/
theorem etaleExtendCompare_unique {S : Scheme.{u}} {Y Z Y' Z' : AlgebraicSpace S}
    (fZY : Z ⟶ Y) (iY : Y ⟶ Y') (iZ : Z ⟶ Z') (fZ' : Z' ⟶ Y')
    [Etale fZY] [IsThickening iY] [Etale fZ']
    (h : IsPullback iZ fZY fZ' iY) (g : Z' ⟶ etaleExtend fZY iY)
    (h_over : g ≫ etaleExtendHom fZY iY = fZ')
    (h_immersion : iZ ≫ g = etaleExtendImmersion fZY iY) :
    g = etaleExtendCompare fZY iY iZ fZ' h :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
