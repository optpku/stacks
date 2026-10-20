/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Homology.ShortComplex.Exact
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Conormal.Basic
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.PresentationRestriction
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Pullback
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Pullback.Sections
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Pullback.Differentials
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Etale.OpenImmersion

/-!
# The conormal sequence of an immersion of algebraic spaces

For an immersion `i : Z ⟶ X` of algebraic spaces over `B`, the canonical
conormal map induced by `d_{X/B}` and the canonical comparison on relative
differentials form a right-exact sequence

  `C_{Z/X} ⟶ i^* Ω_{X/B} ⟶ Ω_{Z/B} ⟶ 0`.

`C_{Z/X}` is the coborder pullback of `I / I²` along `IsImmersion.liftCoborder i`.
The first arrow is induced on that closed immersion by `d_{U/B}`, then
transported to `i^* Ω_{X/B}` along the explicit étale-restriction inverse of
the open-immersion differentials comparison, `pullbackCompIso`, and `eqToIso` of
`liftCoborder_comp`. The second arrow is `Hom.Differentials.comparison` of the
identity square on `B`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.Hom
open Sheaf.InternalModule
open PresheafOfModules.DifferentialsConstruction

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Hom.Conormal.Differentials

variable {S : Scheme.{u}} {B X Z : AlgebraicSpace S}
variable (i : Z ⟶ X) [IsImmersion i] (f : X ⟶ B)

/-- The `𝒪`-linear map `I ⟶ Ω_{U/B} / I Ω_{U/B}` induced by `d_{U/B}` on the
coborder closed immersion of `i`. -/
def toQuotientDifferentials :
    idealSheaf (IsImmersion.liftCoborder i) ⟶
      Modules.quotientByIdeal (idealSheafSubobject (IsImmersion.liftCoborder i))
        (relativeDifferentials ((IsImmersion.coborderRange i).ι ≫ f)) :=
  homOfUnderlying (structureSheaf (IsImmersion.coborderRange i).X)
    (((ToInternal.underlying (structureSheaf (IsImmersion.coborderRange i).X)).map
        (idealSheafι (IsImmersion.liftCoborder i))) ≫
      (Modules.unitCarrierIso (IsImmersion.coborderRange i).X).hom ≫
      universalDerivation_typeHom ((IsImmersion.coborderRange i).ι ≫ f) ≫
      ((ToInternal.underlying (structureSheaf (IsImmersion.coborderRange i).X)).map
        (Modules.quotientByIdeal.π (idealSheafSubobject (IsImmersion.liftCoborder i))
          (relativeDifferentials ((IsImmersion.coborderRange i).ι ≫ f)))))
    sorry sorry

/-- The coborder derivation `I ⟶ Ω / IΩ` annihilates the ideal-sheaf action
`I ⊗ I ⟶ I`. -/
theorem toQuotientDifferentials_comp_action :
    Modules.idealAction (idealSheafSubobject (IsImmersion.liftCoborder i))
        (idealSheaf (IsImmersion.liftCoborder i)) ≫
      toQuotientDifferentials i f =
      0 :=
  sorry

/-- The coborder quotient map `I / I² ⟶ Ω_{U/B} / I Ω_{U/B}` induced by
`d_{U/B}`. -/
def coborderQuotientMap :
    Modules.quotientByIdeal (idealSheafSubobject (IsImmersion.liftCoborder i))
        (idealSheaf (IsImmersion.liftCoborder i)) ⟶
      Modules.quotientByIdeal (idealSheafSubobject (IsImmersion.liftCoborder i))
        (relativeDifferentials ((IsImmersion.coborderRange i).ι ≫ f)) :=
  cokernel.desc
    (Modules.idealAction (idealSheafSubobject (IsImmersion.liftCoborder i))
      (idealSheaf (IsImmersion.liftCoborder i)))
    (toQuotientDifferentials i f) (toQuotientDifferentials_comp_action i f)

/-- `coborderQuotientMap` is cokernel descent of `toQuotientDifferentials`. -/
theorem coborderQuotientMap_eq :
    coborderQuotientMap i f =
      cokernel.desc
        (Modules.idealAction (idealSheafSubobject (IsImmersion.liftCoborder i))
          (idealSheaf (IsImmersion.liftCoborder i)))
        (toQuotientDifferentials i f) (toQuotientDifferentials_comp_action i f) :=
  rfl

/-- The adjoint `C_{Z/X} ⟶ j^* Ω_{U/B}` of the coborder quotient map composed
with `F / I F ⟶ j_* j^* F`. -/
def coborderMap :
    Hom.conormalSheaf i ⟶
      (Modules.pullback (IsImmersion.liftCoborder i)).obj
        (relativeDifferentials ((IsImmersion.coborderRange i).ι ≫ f)) :=
  ((Modules.pullbackPushforwardAdjunction (IsImmersion.liftCoborder i)).homEquiv
      (Modules.quotientByIdeal (idealSheafSubobject (IsImmersion.liftCoborder i))
        (idealSheaf (IsImmersion.liftCoborder i)))
      ((Modules.pullback (IsImmersion.liftCoborder i)).obj
        (relativeDifferentials ((IsImmersion.coborderRange i).ι ≫ f)))).symm
    (coborderQuotientMap i f ≫
      Modules.quotientByIdealComparison (IsImmersion.liftCoborder i)
        (relativeDifferentials ((IsImmersion.coborderRange i).ι ≫ f)))

/-- `coborderMap` is the adjunction transpose of
`coborderQuotientMap ≫ quotientByIdealComparison`. -/
theorem coborderMap_eq :
    coborderMap i f =
      ((Modules.pullbackPushforwardAdjunction (IsImmersion.liftCoborder i)).homEquiv
          (Modules.quotientByIdeal (idealSheafSubobject (IsImmersion.liftCoborder i))
            (idealSheaf (IsImmersion.liftCoborder i)))
          ((Modules.pullback (IsImmersion.liftCoborder i)).obj
            (relativeDifferentials ((IsImmersion.coborderRange i).ι ≫ f)))).symm
        (coborderQuotientMap i f ≫
          Modules.quotientByIdealComparison (IsImmersion.liftCoborder i)
            (relativeDifferentials ((IsImmersion.coborderRange i).ι ≫ f))) :=
  rfl

/-- The canonical comparison `i^* Ω_{X/B} ⟶ j^* Ω_{U/B}` along the coborder open
immersion, transported through the successive-pullback isomorphism. -/
def coborderDifferentialsComparison :
    (Modules.pullback i).obj (relativeDifferentials f) ⟶
      (Modules.pullback (IsImmersion.liftCoborder i)).obj
        (relativeDifferentials ((IsImmersion.coborderRange i).ι ≫ f)) :=
  (eqToIso (congrArg Modules.pullback (IsImmersion.liftCoborder_comp i))).inv.app
      (relativeDifferentials f) ≫
    (Modules.pullbackCompIso (IsImmersion.liftCoborder i)
        (IsImmersion.coborderRange i).ι).inv.app
      (relativeDifferentials f) ≫
    (Modules.pullback (IsImmersion.liftCoborder i)).map
      (Hom.Differentials.comparison
        (IsImmersion.coborderRange i).ι (𝟙 B) f
        ((IsImmersion.coborderRange i).ι ≫ f)
        (Eq.symm (Category.comp_id ((IsImmersion.coborderRange i).ι ≫ f))))

/-- The inverse `Ω_{U/B} ⟶ ι^* Ω_{X/B}` of the coborder open comparison, obtained
by descending `d_{X/B}` through étale restriction and identifying restriction
with pullback. -/
def coborderOpenComparisonInv :
    relativeDifferentials ((IsImmersion.coborderRange i).ι ≫ f) ⟶
      (Modules.pullback (IsImmersion.coborderRange i).ι).obj
        (relativeDifferentials f) :=
  let sectionMap :
      ∀ {U : (smallEtaleSite (IsImmersion.coborderRange i).X)ᵒᵖ},
        (commStructureSheaf (IsImmersion.coborderRange i).X).obj.obj U →
          (Modules.restrict (relativeDifferentials f)
            (IsImmersion.coborderRange i).ι).val.obj U :=
    fun {U} t ↦
      (Modules.restrictAppIso (relativeDifferentials f)
          (IsImmersion.coborderRange i).ι U.unop).inv
        ((universalDerivation f).d (cast rfl t))
  let derivation :
      (toCommPresheaf
          (Modules.restrict (relativeDifferentials f)
            (IsImmersion.coborderRange i).ι)).Derivation'
        (commInverseImageStructureSheafMap
          ((IsImmersion.coborderRange i).ι ≫ f)).hom :=
    { d := fun {_} ↦ AddMonoidHom.mk' sectionMap sorry
      d_mul := sorry
      d_map := sorry
      d_app := sorry }
  let descent :
      relativeDifferentials ((IsImmersion.coborderRange i).ι ≫ f) ⟶
        Modules.restrict (relativeDifferentials f)
          (IsImmersion.coborderRange i).ι :=
    (PresheafOfModules.sheafificationHomEquiv.{u}
        (𝟙 (structureSheaf (IsImmersion.coborderRange i).X).obj)).symm
      ((isUniversal'
          (commInverseImageStructureSheafMap
            ((IsImmersion.coborderRange i).ι ≫ f)).hom).desc
        (cast rfl derivation))
  descent ≫
    (Modules.restrictIsoPullback (relativeDifferentials f)
        (IsImmersion.coborderRange i).ι).hom

/-- The inverse transport `j^* Ω_{U/B} ⟶ i^* Ω_{X/B}` of the coborder open
comparison, as an explicit composite. -/
def coborderDifferentialsComparisonInv :
    (Modules.pullback (IsImmersion.liftCoborder i)).obj
        (relativeDifferentials ((IsImmersion.coborderRange i).ι ≫ f)) ⟶
      (Modules.pullback i).obj (relativeDifferentials f) :=
  (Modules.pullback (IsImmersion.liftCoborder i)).map
      (coborderOpenComparisonInv i f) ≫
    (Modules.pullbackCompIso (IsImmersion.liftCoborder i)
        (IsImmersion.coborderRange i).ι).hom.app
      (relativeDifferentials f) ≫
    (eqToIso (congrArg Modules.pullback (IsImmersion.liftCoborder_comp i))).hom.app
      (relativeDifferentials f)

/-- `coborderDifferentialsComparisonInv` is `j^*` of `coborderOpenComparisonInv`,
then `pullbackCompIso` and `eqToIso` of `liftCoborder_comp`. -/
theorem coborderDifferentialsComparisonInv_eq :
    coborderDifferentialsComparisonInv i f =
      (Modules.pullback (IsImmersion.liftCoborder i)).map
          (coborderOpenComparisonInv i f) ≫
        (Modules.pullbackCompIso (IsImmersion.liftCoborder i)
            (IsImmersion.coborderRange i).ι).hom.app
          (relativeDifferentials f) ≫
        (eqToIso (congrArg Modules.pullback (IsImmersion.liftCoborder_comp i))).hom.app
          (relativeDifferentials f) :=
  rfl

/-- The coborder open comparison on relative differentials as explicit isomorphism
data. -/
def coborderDifferentialsComparisonIso :
    (Modules.pullback i).obj (relativeDifferentials f) ≅
      (Modules.pullback (IsImmersion.liftCoborder i)).obj
        (relativeDifferentials ((IsImmersion.coborderRange i).ι ≫ f)) where
  hom := coborderDifferentialsComparison i f
  inv := coborderDifferentialsComparisonInv i f
  hom_inv_id := sorry
  inv_hom_id := sorry

/-- The coborder open comparison on relative differentials is an isomorphism. -/
instance instIsIso_coborderDifferentialsComparison :
    IsIso (coborderDifferentialsComparison i f) :=
  (coborderDifferentialsComparisonIso i f).isIso_hom

/-- The canonical conormal morphism `C_{Z/X} ⟶ i^* Ω_{X/B}` induced by
`d_{X/B}`. -/
def map :
    Hom.conormalSheaf i ⟶
      (Modules.pullback i).obj (relativeDifferentials f) :=
  coborderMap i f ≫ coborderDifferentialsComparisonInv i f

/-- The canonical comparison `i^* Ω_{X/B} ⟶ Ω_{Z/B}` attached to the identity
square on `B`. -/
def comparison :
    (Modules.pullback i).obj (relativeDifferentials f) ⟶
      relativeDifferentials (i ≫ f) :=
  Hom.Differentials.comparison i (𝟙 B) f (i ≫ f)
    (Eq.symm (Category.comp_id (i ≫ f)))

/-- The two canonical arrows in the conormal sequence have zero composite. -/
theorem map_comp_comparison : map i f ≫ comparison i f = 0 :=
  sorry

/-- The canonical conormal short complex associated to an immersion over `B`. -/
def complex : ShortComplex Z.Modules :=
  ShortComplex.mk (map i f) (comparison i f) (map_comp_comparison i f)

/-- `complex` is the short complex on `map` and `comparison`. -/
theorem complex_eq :
    complex i f =
      ShortComplex.mk (map i f) (comparison i f) (map_comp_comparison i f) :=
  rfl

/-- The canonical conormal short complex of an immersion of algebraic spaces is
exact. -/
theorem exact : (complex i f).Exact :=
  sorry

/-- The comparison at the right of the conormal sequence of an immersion is an
epimorphism. -/
instance comparison_epi : Epi (comparison i f) :=
  sorry

/-- For an immersion of algebraic spaces over `B`, the canonical conormal complex
is exact and its right arrow is an epimorphism. -/
theorem exact_and_epi : (complex i f).Exact ∧ Epi (comparison i f) :=
  ⟨exact i f, comparison_epi i f⟩

/-- The second arrow of the conormal sequence is characterized by carrying
universal differentials to differentials of pulled-back sections. -/
theorem comparison_isComparison :
    Hom.Differentials.IsComparison i f (i ≫ f) (comparison i f) :=
  Hom.Differentials.comparison_isComparison i (𝟙 B) f (i ≫ f)
    (Eq.symm (Category.comp_id (i ≫ f)))

/-- `map` is the coborder `d`-induced adjoint of `I / I² ⟶ j_* j^* Ω_{U/B}`,
transported to `i^* Ω_{X/B}` along the explicit coborder open comparison inverse. -/
theorem map_spec :
    map i f = coborderMap i f ≫ coborderDifferentialsComparisonInv i f :=
  rfl

end AlgebraicGeometry.AlgebraicSpace.Hom.Conormal.Differentials
