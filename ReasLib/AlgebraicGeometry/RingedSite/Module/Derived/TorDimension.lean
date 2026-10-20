module

public import ReasLib.AlgebraicGeometry.RingedSite.Module.Derived.Tensor
public import ReasLib.AlgebraicGeometry.RingedSite.Module.Derived.Localization
public import ReasLib.CategoryTheory.DerivedCategory.Monoidal.TorAmplitude

@[expose] public section

/-!
# Tor-amplitude on derived module sheaves

This file specializes the generic `DerivedTensor` Tor-amplitude object properties to module
sheaves on a bundled ringed site.  The commutative structure sheaf fixes the ordinary tensor product over that
sheaf. Totalization and derived-tensor inputs refer to this specified tensor.
-/

open CategoryTheory
-- Local instance justification (defeq pin): the generic ringed-site ModuleCat derived owner is
-- required by the derived-category APIs in this presentation.
attribute [local instance] RingedSite.Hom.moduleCat_hasDerivedCategory
  RingedSite.Hom.RingPresentation.moduleHasDerivedCategory
  SheafOfModules.RingedSite.moduleCategoryHasMapBifunctor
open CategoryTheory.Limits
open CategoryTheory.MonoidalCategory
open ComplexShape
open RingedSite.Hom
open scoped CategoryTheory.DerivedCategory.DerivedTensor

noncomputable section

universe u v w

namespace RingedSite.Hom.ModuleDerived

section

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
variable {O : Sheaf J CommRingCat.{w}} [UnivLE.{max u v, w}]
variable [HasWeakSheafify J AddCommGrpCat.{w}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{w}]

variable [DerivedCategory.DerivedTensor.Right.Has (C := ModuleCat.{w} (RingedSite.ofCommRingSheaf J O))]

/-- The object property of having lower Tor-amplitude at least `a` on a ringed site. -/
@[stacks 08FZ "(1), ringed-site lower-bound object property"]
abbrev torAmplitudeGE (a : ℤ) : ObjectProperty (ModuleDerived.{w} (RingedSite.ofCommRingSheaf J O)) :=
  DerivedCategory.DerivedTensor.torAmplitudeGE (C := ModuleCat.{w} (RingedSite.ofCommRingSheaf J O)) a

/-- A derived module sheaf has lower Tor-amplitude at least `a`. -/
abbrev HasTorAmplitudeGE (E : ModuleDerived.{w} (RingedSite.ofCommRingSheaf J O)) (a : ℤ) : Prop :=
  torAmplitudeGE (O := O) a E

/-- The object property of having upper Tor-amplitude at most `b` on a ringed site. -/
@[stacks 08FZ "(1), ringed-site upper-bound object property"]
abbrev torAmplitudeLE (b : ℤ) : ObjectProperty (ModuleDerived.{w} (RingedSite.ofCommRingSheaf J O)) :=
  DerivedCategory.DerivedTensor.torAmplitudeLE (C := ModuleCat.{w} (RingedSite.ofCommRingSheaf J O)) b

/-- A derived module sheaf has upper Tor-amplitude at most `b`. -/
abbrev HasTorAmplitudeLE (E : ModuleDerived.{w} (RingedSite.ofCommRingSheaf J O)) (b : ℤ) : Prop :=
  torAmplitudeLE (O := O) b E

/-- The object property of having Tor-amplitude in `[a, b]` on a ringed site. -/
@[stacks 08FZ "(1), ringed-site object property"]
abbrev torAmplitudeIn (a b : ℤ) : ObjectProperty (ModuleDerived.{w} (RingedSite.ofCommRingSheaf J O)) :=
  DerivedCategory.DerivedTensor.torAmplitudeIn (C := ModuleCat.{w} (RingedSite.ofCommRingSheaf J O)) a b

/-- Definition 21.46.1 (1): `E` has Tor-amplitude in `[a, b]` when its canonical derived tensor
product with every degree-zero module sheaf has cohomology only in that interval. -/
@[stacks 08FZ "(1)"]
abbrev HasTorAmplitudeIn (E : ModuleDerived.{w} (RingedSite.ofCommRingSheaf J O)) (a b : ℤ) : Prop :=
  torAmplitudeIn (O := O) a b E

/-- The object property of having finite Tor dimension on a ringed site. -/
@[stacks 08FZ "(2), ringed-site object property"]
abbrev finiteTorDimension : ObjectProperty (ModuleDerived.{w} (RingedSite.ofCommRingSheaf J O)) :=
  DerivedCategory.DerivedTensor.finiteTorDimension (C := ModuleCat.{w} (RingedSite.ofCommRingSheaf J O))

/-- Definition 21.46.1 (2): a derived module sheaf has finite Tor dimension when it has
Tor-amplitude in some finite interval. -/
@[stacks 08FZ "(2)"]
abbrev HasFiniteTorDimension (E : ModuleDerived.{w} (RingedSite.ofCommRingSheaf J O)) : Prop :=
  finiteTorDimension (O := O) E

/-- Tor-amplitude on a ringed site unfolds to the canonical lower and upper bounds. -/
theorem hasTorAmplitudeIn_iff (E : ModuleDerived.{w} (RingedSite.ofCommRingSheaf J O)) (a b : ℤ) :
    HasTorAmplitudeIn E a b ↔ HasTorAmplitudeGE E a ∧ HasTorAmplitudeLE E b := sorry

/-- Tor-amplitude on a ringed site unfolds to homology vanishing outside the interval after
canonical derived tensoring with every degree-zero module sheaf. -/
theorem hasTorAmplitudeIn_iff_homology (E : ModuleDerived.{w} (RingedSite.ofCommRingSheaf J O)) (a b : ℤ) :
    HasTorAmplitudeIn E a b ↔
      ∀ (F : ModuleCat.{w} (RingedSite.ofCommRingSheaf J O)) (i : ℤ), i ∉ Set.Icc a b →
        IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{w} (RingedSite.ofCommRingSheaf J O)) i).obj
          (E ⊗ᴸ (DerivedCategory.singleFunctor (ModuleCat.{w} (RingedSite.ofCommRingSheaf J O)) 0).obj F)) := sorry

/-- Finite Tor dimension unfolds to the existence of a finite Tor-amplitude interval. -/
theorem hasFiniteTorDimension_iff (E : ModuleDerived.{w} (RingedSite.ofCommRingSheaf J O)) :
    HasFiniteTorDimension E ↔ ∃ a b : ℤ, HasTorAmplitudeIn E a b := sorry

/-- Tor-amplitude in a fixed interval implies finite Tor dimension. -/
theorem HasTorAmplitudeIn.hasFiniteTorDimension
    {E : ModuleDerived.{w} (RingedSite.ofCommRingSheaf J O)} {a b : ℤ} (hE : HasTorAmplitudeIn E a b) :
    HasFiniteTorDimension E := sorry

/-- Tor-amplitude in a finite interval implies the corresponding lower bound. -/
theorem HasTorAmplitudeIn.hasTorAmplitudeGE
    {E : ModuleDerived.{w} (RingedSite.ofCommRingSheaf J O)} {a b : ℤ} (hE : HasTorAmplitudeIn E a b) :
    HasTorAmplitudeGE E a := sorry

/-- Tor-amplitude in a finite interval implies the corresponding upper bound. -/
theorem HasTorAmplitudeIn.hasTorAmplitudeLE
    {E : ModuleDerived.{w} (RingedSite.ofCommRingSheaf J O)} {a b : ℤ} (hE : HasTorAmplitudeIn E a b) :
    HasTorAmplitudeLE E b := sorry

end

end RingedSite.Hom.ModuleDerived

namespace RingedSite.ModuleCat

section

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
variable {O : Sheaf J CommRingCat.{w}} [UnivLE.{max u v, w}]
variable [HasWeakSheafify J AddCommGrpCat.{w}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{w}]

variable [DerivedCategory.DerivedTensor.Right.Has (C := ModuleCat.{w} (RingedSite.ofCommRingSheaf J O))]

/-- The object property of module sheaves with Tor dimension at most `d`. -/
@[stacks 08FZ "(4), ringed-site object property"]
abbrev torDimensionLE (d : ℕ) : ObjectProperty (ModuleCat.{w} (RingedSite.ofCommRingSheaf J O)) :=
  DerivedCategory.DerivedTensor.torDimensionLE (C := ModuleCat.{w} (RingedSite.ofCommRingSheaf J O)) d

/-- Definition 21.46.1 (4): a module sheaf has Tor dimension at most `d` when its degree-zero
derived object has Tor-amplitude in `[-d, 0]`. -/
@[stacks 08FZ "(4)"]
abbrev HasTorDimensionLE (F : ModuleCat.{w} (RingedSite.ofCommRingSheaf J O)) (d : ℕ) : Prop :=
  torDimensionLE (O := O) d F

end

end RingedSite.ModuleCat
