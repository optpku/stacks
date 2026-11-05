/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Invertible.Basic
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.Invertible
public import ReasLib.AlgebraicGeometry.Scheme.Divisor.EffectiveCartier
public import ReasLib.AlgebraicGeometry.Scheme.Module.Picard

/-!
# Sheaves associated to effective Cartier divisors

This module constructs the invertible sheaf and canonical section associated to an invertible
ideal sheaf, as well as the sheaves corresponding to negative divisors and differences.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.MonoidalCategory
open CategoryTheory.MonoidalClosed
open AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme

variable {X : Scheme.{u}}
variable [MonoidalClosed (SheafOfModules X.ringCatSheaf)]

/-- The sheaf associated to an invertible ideal sheaf is its internal-Hom dual. -/
abbrev effectiveCartierDivisorAssociatedSheaf
    (I : Subobject (SheafOfModules.unit X.ringCatSheaf :
      SheafOfModules X.ringCatSheaf))
    [Fact (Functor.IsEquivalence (tensorRight (Subobject.underlying.obj I)))] :
    SheafOfModules X.ringCatSheaf :=
  (ihom (Subobject.underlying.obj I)).obj
    (SheafOfModules.unit X.ringCatSheaf : SheafOfModules X.ringCatSheaf)

/-- The evaluation morphism from an invertible ideal sheaf tensored with its associated sheaf
to the structure sheaf. -/
noncomputable abbrev effectiveCartierDivisorEvaluationHom
    (I : Subobject (SheafOfModules.unit X.ringCatSheaf :
      SheafOfModules X.ringCatSheaf))
    [Fact (Functor.IsEquivalence (tensorRight (Subobject.underlying.obj I)))] :
    tensorObj (Subobject.underlying.obj I) (effectiveCartierDivisorAssociatedSheaf I) ⟶
      (SheafOfModules.unit X.ringCatSheaf : SheafOfModules X.ringCatSheaf) :=
  (ihom.ev (Subobject.underlying.obj I)).app
    (SheafOfModules.unit X.ringCatSheaf : SheafOfModules X.ringCatSheaf)

/-- Evaluation of an invertible ideal sheaf against its associated sheaf is an isomorphism. -/
instance effectiveCartierDivisorAssociatedSheaf_evaluationIso
    (I : Subobject (SheafOfModules.unit X.ringCatSheaf :
      SheafOfModules X.ringCatSheaf))
    [Fact (Functor.IsEquivalence (tensorRight (Subobject.underlying.obj I)))] :
    IsIso (effectiveCartierDivisorEvaluationHom (X := X) I) := by
  let L := Subobject.underlying.obj I
  letI : MonoidalCategory.isInvertibleObject L :=
    MonoidalCategory.isInvertibleObject.ofTensorRight L Fact.out
  let η : (SheafOfModules.unit X.ringCatSheaf : SheafOfModules X.ringCatSheaf) ≅
      𝟙_ (SheafOfModules X.ringCatSheaf) :=
    SheafOfModules.RingedSite.unitIsoTensorUnit
      (J := Opens.grothendieckTopology X.toTopCat) (𝒪 := X.𝒪)
  haveI : IsIso η.hom := η.isIso_hom
  have hwhisk : IsIso (L ◁ (ihom L).map η.hom) := by infer_instance
  have heval : IsIso ((ihom.ev L).app (𝟙_ (SheafOfModules X.ringCatSheaf))) :=
    MonoidalCategory.isInvertibleObject.evaluationIsIso L
  haveI : IsIso ((ihom.ev L).app (SheafOfModules.unit X.ringCatSheaf) ≫ η.hom) := by
    rw [← ihom.ev_naturality (A := L) η.hom]
    exact IsIso.comp_isIso' hwhisk heval
  exact IsIso.of_isIso_comp_right
    ((ihom.ev L).app (SheafOfModules.unit X.ringCatSheaf)) η.hom

/-- The sheaf associated to an invertible ideal sheaf is invertible. -/
instance effectiveCartierDivisorAssociatedSheaf_isInvertible
    (I : Subobject (SheafOfModules.unit X.ringCatSheaf :
      SheafOfModules X.ringCatSheaf))
    [Fact (Functor.IsEquivalence (tensorRight (Subobject.underlying.obj I)))] :
    Modules.Invertible (effectiveCartierDivisorAssociatedSheaf I) := by
  let L := Subobject.underlying.obj I
  letI : MonoidalCategory.isInvertibleObject L :=
    MonoidalCategory.isInvertibleObject.ofTensorRight L Fact.out
  let η : (SheafOfModules.unit X.ringCatSheaf : SheafOfModules X.ringCatSheaf) ≅
      𝟙_ (SheafOfModules X.ringCatSheaf) :=
    SheafOfModules.RingedSite.unitIsoTensorUnit
      (J := Opens.grothendieckTopology X.toTopCat) (𝒪 := X.𝒪)
  exact MonoidalCategory.isInvertibleObject.of_iso ((ihom L).mapIso η.symm)
    (MonoidalCategory.isInvertibleObject.ihomUnit L)

/-- The canonical morphism from the structure sheaf to the sheaf associated to an invertible
ideal sheaf. -/
noncomputable abbrev effectiveCartierDivisorCanonicalSectionHom
    (I : Subobject (SheafOfModules.unit X.ringCatSheaf :
      SheafOfModules X.ringCatSheaf))
    [Fact (Functor.IsEquivalence (tensorRight (Subobject.underlying.obj I)))] :
    (SheafOfModules.unit X.ringCatSheaf : SheafOfModules X.ringCatSheaf) ⟶
      effectiveCartierDivisorAssociatedSheaf I :=
  let η : (SheafOfModules.unit X.ringCatSheaf : SheafOfModules X.ringCatSheaf) ≅
      𝟙_ (SheafOfModules X.ringCatSheaf) :=
    SheafOfModules.RingedSite.unitIsoTensorUnit
      (J := Opens.grothendieckTopology X.toTopCat) (𝒪 := X.𝒪)
  η.hom ≫ MonoidalClosed.curry
    ((ρ_ (Subobject.underlying.obj I)).hom ≫ I.arrow)

/-- The canonical global section of the sheaf associated to an invertible ideal sheaf. -/
abbrev effectiveCartierDivisorCanonicalSection
    (I : Subobject (SheafOfModules.unit X.ringCatSheaf :
      SheafOfModules X.ringCatSheaf))
    [Fact (Functor.IsEquivalence (tensorRight (Subobject.underlying.obj I)))] :
    (effectiveCartierDivisorAssociatedSheaf I).sections :=
  (effectiveCartierDivisorAssociatedSheaf I).unitHomEquiv
    (effectiveCartierDivisorCanonicalSectionHom I)

/-- The negative-divisor sheaf attached to an invertible ideal sheaf is its underlying module. -/
abbrev effectiveCartierDivisorNegSheaf
    (I : Subobject (SheafOfModules.unit X.ringCatSheaf :
      SheafOfModules X.ringCatSheaf))
    [Fact (Functor.IsEquivalence (tensorRight (Subobject.underlying.obj I)))] :
    SheafOfModules X.ringCatSheaf :=
  Subobject.underlying.obj I

/-- The sheaf associated to a difference of effective Cartier divisors is the tensor product of
the positive associated sheaf with the negative-divisor sheaf. -/
abbrev effectiveCartierDivisorDifferenceSheaf
    (I I' : Subobject (SheafOfModules.unit X.ringCatSheaf :
      SheafOfModules X.ringCatSheaf))
    [Fact (Functor.IsEquivalence (tensorRight (Subobject.underlying.obj I)))]
    [Fact (Functor.IsEquivalence (tensorRight (Subobject.underlying.obj I')))] :
    SheafOfModules X.ringCatSheaf :=
  tensorObj (effectiveCartierDivisorAssociatedSheaf I)
    (effectiveCartierDivisorNegSheaf I')

/-- The difference sheaf is definitionally the tensor product of the positive associated sheaf
and the negative-divisor sheaf. -/
theorem effectiveCartierDivisorDifferenceSheaf_def
    (I I' : Subobject (SheafOfModules.unit X.ringCatSheaf :
      SheafOfModules X.ringCatSheaf))
    [Fact (Functor.IsEquivalence (tensorRight (Subobject.underlying.obj I)))]
    [Fact (Functor.IsEquivalence (tensorRight (Subobject.underlying.obj I')))] :
    effectiveCartierDivisorDifferenceSheaf I I' =
      tensorObj (effectiveCartierDivisorAssociatedSheaf I)
        (effectiveCartierDivisorNegSheaf I') := rfl

end AlgebraicGeometry.Scheme

/- Legacy namespace retained for source compatibility; the sheaf module owns O(D). -/
namespace WeilCohomology

/-- The Picard class of the invertible scheme module associated to an effective Cartier divisor. -/
noncomputable def effectiveCartierDivisorPicardClass
    {Y X : Scheme.{u}} (i : Y ⟶ X) (hi : IsEffectiveCartierDivisor i) :
    X.PicardGroup :=
  @AlgebraicGeometry.Scheme.Modules.picardClass X
    (@Scheme.effectiveCartierDivisorAssociatedSheaf X inferInstance
      (RingedSpace.Hom.idealSheafSubobject i.toShHom)
      ⟨Scheme.Modules.Invertible.tensorRight_isEquivalence hi.invertibleIdealSheaf⟩)
    (@Scheme.effectiveCartierDivisorAssociatedSheaf_isInvertible X inferInstance
      (RingedSpace.Hom.idealSheafSubobject i.toShHom)
      ⟨Scheme.Modules.Invertible.tensorRight_isEquivalence hi.invertibleIdealSheaf⟩)


end WeilCohomology
