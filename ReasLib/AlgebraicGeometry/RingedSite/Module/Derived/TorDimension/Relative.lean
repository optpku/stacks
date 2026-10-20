/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Mathlib.CategoryTheory.ObjectProperty.Basic
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings.Exact
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite
public import ReasLib.AlgebraicGeometry.RingedSite.CommRing.Pullback
public import ReasLib.AlgebraicGeometry.RingedSite.Module.Derived.Tensor
public import ReasLib.AlgebraicGeometry.RingedSite.Module.Derived.TorDimension.Local
public import ReasLib.AlgebraicGeometry.RingedSite.Module.Localization

/-!
# Relative Tor-amplitude on commutative ringed sites

Restriction of scalars along `f⁻¹𝒪 ⟶ 𝒪` views a derived `𝒪_X`-module as an
object of `D(f⁻¹𝒪_Y)`. Relative Tor-amplitude and locally finite Tor dimension
are the ordinary predicates after this restriction.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open CategoryTheory.MonoidalCategory
open ComplexShape
open RingedSite.Hom
open SheafOfModules.RingedSite
open scoped RingedSite.Hom

noncomputable section

universe uC vC uD vD w

namespace RingedSite.Hom.ModuleDerived

variable {C : Type uC} [Category.{vC} C] {D : Type uD} [Category.{vD} D]
variable {JC : GrothendieckTopology C} {JD : GrothendieckTopology D}
variable [JC.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
variable [JD.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
variable {𝒪 : Sheaf JC CommRingCat.{w}} {𝒪' : Sheaf JD CommRingCat.{w}}

/-- The source site equipped with the inverse-image structure sheaf `f⁻¹𝒪`. -/
noncomputable abbrev inverseImageSite
    (f : RingedSite.Hom
      (RingedSite.ofCommRingSheaf JC 𝒪) (RingedSite.ofCommRingSheaf JD 𝒪'))
    [(f.base.sheafPushforwardContinuous CommRingCat.{w} JD JC).IsRightAdjoint] :
    RingedSite.{uC, vC, w} :=
  RingedSite.ofCommRingSheaf JC (inverseImageStructureSheaf f)

/-- `inverseImageSite f` is the commutative presentation of the source site with
structure sheaf `f⁻¹𝒪`. -/
theorem inverseImageSite_eq
    (f : RingedSite.Hom
      (RingedSite.ofCommRingSheaf JC 𝒪) (RingedSite.ofCommRingSheaf JD 𝒪'))
    [(f.base.sheafPushforwardContinuous CommRingCat.{w} JD JC).IsRightAdjoint] :
    inverseImageSite f =
      RingedSite.ofCommRingSheaf JC (inverseImageStructureSheaf f) := rfl

variable [UnivLE.{max uC vC, w}]

/-- Derived restriction of `𝒪_X`-modules to modules over `f⁻¹𝒪`. -/
noncomputable def relativeRestriction
    (f : RingedSite.Hom
      (RingedSite.ofCommRingSheaf JC 𝒪) (RingedSite.ofCommRingSheaf JD 𝒪'))
    [(f.base.sheafPushforwardContinuous CommRingCat.{w} JD JC).IsRightAdjoint] :
    ModuleDerived.{w} (RingedSite.ofCommRingSheaf JC 𝒪) ⥤
      ModuleDerived.{w} (inverseImageSite f) :=
  @Functor.mapDerivedCategory
    (ModuleCat.{w} (RingedSite.ofCommRingSheaf JC 𝒪)) _ _
    (moduleCat_hasDerivedCategory (RingedSite.ofCommRingSheaf JC 𝒪))
    (ModuleCat.{w} (inverseImageSite f)) _ _
    (moduleCat_hasDerivedCategory (inverseImageSite f))
    (restrictionAlong.{uC, vC, w, w} (inverseImageStructureSheafMap f)) _ _ _

/-- Derived relative restriction is the derived functor of restriction of scalars
along `inverseImageStructureSheafMap f`. -/
theorem relativeRestriction_eq
    (f : RingedSite.Hom
      (RingedSite.ofCommRingSheaf JC 𝒪) (RingedSite.ofCommRingSheaf JD 𝒪'))
    [(f.base.sheafPushforwardContinuous CommRingCat.{w} JD JC).IsRightAdjoint] :
    relativeRestriction f =
      (@Functor.mapDerivedCategory
        (ModuleCat.{w} (RingedSite.ofCommRingSheaf JC 𝒪)) _ _
        (moduleCat_hasDerivedCategory (RingedSite.ofCommRingSheaf JC 𝒪))
        (ModuleCat.{w} (inverseImageSite f)) _ _
        (moduleCat_hasDerivedCategory (inverseImageSite f))
        (restrictionAlong.{uC, vC, w, w} (inverseImageStructureSheafMap f)) _ _ _) := rfl

section

variable [HasWeakSheafify JC AddCommGrpCat.{w}]
variable [JC.WEqualsLocallyBijective AddCommGrpCat.{w}]

/-- A derived `𝒪_X`-module has Tor-amplitude in `[a, b]` over `f` when its
restriction to `f⁻¹𝒪` has that Tor-amplitude. -/
abbrev HasTorAmplitudeInOver
    (f : RingedSite.Hom
      (RingedSite.ofCommRingSheaf JC 𝒪) (RingedSite.ofCommRingSheaf JD 𝒪'))
    [(f.base.sheafPushforwardContinuous CommRingCat.{w} JD JC).IsRightAdjoint]
    (E : ModuleDerived.{w} (RingedSite.ofCommRingSheaf JC 𝒪)) (a b : ℤ) : Prop :=
  HasTorAmplitudeIn (O := inverseImageStructureSheaf f) ((relativeRestriction f).obj E) a b

/-- Relative Tor-amplitude is the ordinary Tor-amplitude of the derived restriction
to `f⁻¹𝒪`. -/
theorem hasTorAmplitudeInOver_iff
    (f : RingedSite.Hom
      (RingedSite.ofCommRingSheaf JC 𝒪) (RingedSite.ofCommRingSheaf JD 𝒪'))
    [(f.base.sheafPushforwardContinuous CommRingCat.{w} JD JC).IsRightAdjoint]
    (E : ModuleDerived.{w} (RingedSite.ofCommRingSheaf JC 𝒪)) (a b : ℤ) :
    HasTorAmplitudeInOver f E a b ↔
      HasTorAmplitudeIn (O := inverseImageStructureSheaf f) ((relativeRestriction f).obj E) a b := Iff.rfl

/-- The object property of having Tor-amplitude in `[a, b]` after restriction from
`𝒪_X` to `f⁻¹𝒪`. -/
noncomputable def torAmplitudeInOver
    (f : RingedSite.Hom
      (RingedSite.ofCommRingSheaf JC 𝒪) (RingedSite.ofCommRingSheaf JD 𝒪'))
    [(f.base.sheafPushforwardContinuous CommRingCat.{w} JD JC).IsRightAdjoint]
    (a b : ℤ) :
    ObjectProperty (ModuleDerived.{w} (RingedSite.ofCommRingSheaf JC 𝒪)) :=
  fun E ↦ HasTorAmplitudeInOver f E a b

/-- The object property `torAmplitudeInOver f a b` is the predicate
`HasTorAmplitudeInOver f · a b`. -/
theorem torAmplitudeInOver_eq
    (f : RingedSite.Hom
      (RingedSite.ofCommRingSheaf JC 𝒪) (RingedSite.ofCommRingSheaf JD 𝒪'))
    [(f.base.sheafPushforwardContinuous CommRingCat.{w} JD JC).IsRightAdjoint]
    (E : ModuleDerived.{w} (RingedSite.ofCommRingSheaf JC 𝒪)) (a b : ℤ) :
    torAmplitudeInOver f a b E = HasTorAmplitudeInOver f E a b := rfl

end

variable [∀ U : C, HasWeakSheafify (JC.over U) AddCommGrpCat.{w}]
variable [∀ U : C, (JC.over U).WEqualsLocallyBijective AddCommGrpCat.{w}]

/-- A derived `𝒪_X`-module locally has finite Tor dimension over `f` when its
restriction to `f⁻¹𝒪` locally has finite Tor dimension. -/
abbrev LocallyHasFiniteTorDimensionOver
    (f : RingedSite.Hom
      (RingedSite.ofCommRingSheaf JC 𝒪) (RingedSite.ofCommRingSheaf JD 𝒪'))
    [(f.base.sheafPushforwardContinuous CommRingCat.{w} JD JC).IsRightAdjoint]
    (E : ModuleDerived.{w} (RingedSite.ofCommRingSheaf JC 𝒪)) : Prop :=
  LocallyHasFiniteTorDimension (O := inverseImageStructureSheaf f) ((relativeRestriction f).obj E)

/-- The object property of locally finite Tor dimension after restriction from
`𝒪_X` to `f⁻¹𝒪`. -/
noncomputable def locallyFiniteTorDimensionOver
    (f : RingedSite.Hom
      (RingedSite.ofCommRingSheaf JC 𝒪) (RingedSite.ofCommRingSheaf JD 𝒪'))
    [(f.base.sheafPushforwardContinuous CommRingCat.{w} JD JC).IsRightAdjoint] :
    ObjectProperty (ModuleDerived.{w} (RingedSite.ofCommRingSheaf JC 𝒪)) :=
  fun E ↦ LocallyHasFiniteTorDimensionOver f E

/-- The object property `locallyFiniteTorDimensionOver f` is the predicate
`LocallyHasFiniteTorDimensionOver f`. -/
theorem locallyFiniteTorDimensionOver_eq
    (f : RingedSite.Hom
      (RingedSite.ofCommRingSheaf JC 𝒪) (RingedSite.ofCommRingSheaf JD 𝒪'))
    [(f.base.sheafPushforwardContinuous CommRingCat.{w} JD JC).IsRightAdjoint]
    (E : ModuleDerived.{w} (RingedSite.ofCommRingSheaf JC 𝒪)) :
    locallyFiniteTorDimensionOver f E = LocallyHasFiniteTorDimensionOver f E := rfl

/-- Relative locally finite Tor dimension is the ordinary covering-local predicate
after derived restriction to `f⁻¹𝒪`. -/
theorem locallyHasFiniteTorDimensionOver_iff
    (f : RingedSite.Hom
      (RingedSite.ofCommRingSheaf JC 𝒪) (RingedSite.ofCommRingSheaf JD 𝒪'))
    [(f.base.sheafPushforwardContinuous CommRingCat.{w} JD JC).IsRightAdjoint]
    (E : ModuleDerived.{w} (RingedSite.ofCommRingSheaf JC 𝒪)) :
    LocallyHasFiniteTorDimensionOver f E ↔
      LocallyHasFiniteTorDimension (O := inverseImageStructureSheaf f) ((relativeRestriction f).obj E) := Iff.rfl

end RingedSite.Hom.ModuleDerived
