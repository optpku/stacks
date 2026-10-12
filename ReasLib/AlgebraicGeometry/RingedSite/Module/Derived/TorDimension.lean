/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.RingedSite.Module.Derived.Tensor
public import ReasLib.AlgebraicGeometry.RingedSite.Module.Derived.Localization
public import ReasLib.CategoryTheory.DerivedCategory.Monoidal.TorAmplitude

@[expose] public section

/-!
# Tor-amplitude on derived module sheaves

This file specializes the generic `DerivedTensor` Tor-amplitude object properties to module
sheaves on a bundled ringed site.  The ambient ringed site need not itself choose a tensor:
commutative site presentations obtain the canonical instances from `Derived.Tensor`, while other
presentations may supply an appropriate source tensor explicitly.
-/

open CategoryTheory
-- Local instance justification (defeq pin): the generic ringed-site ModuleCat derived owner is
-- required by the derived-category APIs in this presentation.
attribute [local instance] RingedSite.Hom.moduleCat_hasDerivedCategory
open CategoryTheory.Limits
open CategoryTheory.MonoidalCategory
open ComplexShape
open RingedSite.Hom
open scoped CategoryTheory.DerivedCategory.DerivedTensor

noncomputable section

universe u v w

namespace RingedSite.Hom.ModuleDerived

section

variable {X : RingedSite.{u, v, w}} [UnivLE.{max u v, w}]
variable [MonoidalCategory (ModuleCat.{w} X)] [MonoidalPreadditive (ModuleCat.{w} X)]
variable [∀ (K L : CochainComplex (ModuleCat.{w} X) ℤ),
  HomologicalComplex.HasMapBifunctor K L (curriedTensor (ModuleCat.{w} X)) (up ℤ)]
variable [DerivedCategory.DerivedTensor.Right.Has (C := ModuleCat.{w} X)]

/-- The object property of having lower Tor-amplitude at least `a` on a ringed site. -/
@[stacks 08FZ "(1), ringed-site lower-bound object property"]
abbrev torAmplitudeGE (a : ℤ) : ObjectProperty (ModuleDerived.{w} X) :=
  DerivedCategory.DerivedTensor.torAmplitudeGE (C := ModuleCat.{w} X) a

/-- A derived module sheaf has lower Tor-amplitude at least `a`. -/
abbrev HasTorAmplitudeGE (E : ModuleDerived.{w} X) (a : ℤ) : Prop :=
  torAmplitudeGE (X := X) a E

/-- The object property of having upper Tor-amplitude at most `b` on a ringed site. -/
@[stacks 08FZ "(1), ringed-site upper-bound object property"]
abbrev torAmplitudeLE (b : ℤ) : ObjectProperty (ModuleDerived.{w} X) :=
  DerivedCategory.DerivedTensor.torAmplitudeLE (C := ModuleCat.{w} X) b

/-- A derived module sheaf has upper Tor-amplitude at most `b`. -/
abbrev HasTorAmplitudeLE (E : ModuleDerived.{w} X) (b : ℤ) : Prop :=
  torAmplitudeLE (X := X) b E

/-- The object property of having Tor-amplitude in `[a, b]` on a ringed site. -/
@[stacks 08FZ "(1), ringed-site object property"]
abbrev torAmplitudeIn (a b : ℤ) : ObjectProperty (ModuleDerived.{w} X) :=
  DerivedCategory.DerivedTensor.torAmplitudeIn (C := ModuleCat.{w} X) a b

/-- Definition 21.46.1 (1): `E` has Tor-amplitude in `[a, b]` when its canonical derived tensor
product with every degree-zero module sheaf has cohomology only in that interval. -/
@[stacks 08FZ "(1)"]
abbrev HasTorAmplitudeIn (E : ModuleDerived.{w} X) (a b : ℤ) : Prop :=
  torAmplitudeIn (X := X) a b E

/-- The object property of having finite Tor dimension on a ringed site. -/
@[stacks 08FZ "(2), ringed-site object property"]
abbrev finiteTorDimension : ObjectProperty (ModuleDerived.{w} X) :=
  DerivedCategory.DerivedTensor.finiteTorDimension (C := ModuleCat.{w} X)

/-- Definition 21.46.1 (2): a derived module sheaf has finite Tor dimension when it has
Tor-amplitude in some finite interval. -/
@[stacks 08FZ "(2)"]
abbrev HasFiniteTorDimension (E : ModuleDerived.{w} X) : Prop :=
  finiteTorDimension (X := X) E

/-- Tor-amplitude on a ringed site unfolds to the canonical lower and upper bounds. -/
theorem hasTorAmplitudeIn_iff (E : ModuleDerived.{w} X) (a b : ℤ) :
    HasTorAmplitudeIn E a b ↔ HasTorAmplitudeGE E a ∧ HasTorAmplitudeLE E b := sorry

/-- Tor-amplitude on a ringed site unfolds to homology vanishing outside the interval after
canonical derived tensoring with every degree-zero module sheaf. -/
theorem hasTorAmplitudeIn_iff_homology (E : ModuleDerived.{w} X) (a b : ℤ) :
    HasTorAmplitudeIn E a b ↔
      ∀ (F : ModuleCat.{w} X) (i : ℤ), i ∉ Set.Icc a b →
        IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{w} X) i).obj
          (E ⊗ᴸ (DerivedCategory.singleFunctor (ModuleCat.{w} X) 0).obj F)) := sorry

/-- Finite Tor dimension unfolds to the existence of a finite Tor-amplitude interval. -/
theorem hasFiniteTorDimension_iff (E : ModuleDerived.{w} X) :
    HasFiniteTorDimension E ↔ ∃ a b : ℤ, HasTorAmplitudeIn E a b := sorry

/-- Tor-amplitude in a fixed interval implies finite Tor dimension. -/
theorem HasTorAmplitudeIn.hasFiniteTorDimension
    {E : ModuleDerived.{w} X} {a b : ℤ} (hE : HasTorAmplitudeIn E a b) :
    HasFiniteTorDimension E := sorry

/-- Tor-amplitude in a finite interval implies the corresponding lower bound. -/
theorem HasTorAmplitudeIn.hasTorAmplitudeGE
    {E : ModuleDerived.{w} X} {a b : ℤ} (hE : HasTorAmplitudeIn E a b) :
    HasTorAmplitudeGE E a := sorry

/-- Tor-amplitude in a finite interval implies the corresponding upper bound. -/
theorem HasTorAmplitudeIn.hasTorAmplitudeLE
    {E : ModuleDerived.{w} X} {a b : ℤ} (hE : HasTorAmplitudeIn E a b) :
    HasTorAmplitudeLE E b := sorry

end

end RingedSite.Hom.ModuleDerived

namespace RingedSite.ModuleCat

section

variable {X : RingedSite.{u, v, w}} [UnivLE.{max u v, w}]
variable [MonoidalCategory (ModuleCat.{w} X)] [MonoidalPreadditive (ModuleCat.{w} X)]
variable [∀ (K L : CochainComplex (ModuleCat.{w} X) ℤ),
  HomologicalComplex.HasMapBifunctor K L (curriedTensor (ModuleCat.{w} X)) (up ℤ)]
variable [DerivedCategory.DerivedTensor.Right.Has (C := ModuleCat.{w} X)]

/-- The object property of module sheaves with Tor dimension at most `d`. -/
@[stacks 08FZ "(4), ringed-site object property"]
abbrev torDimensionLE (d : ℕ) : ObjectProperty (ModuleCat.{w} X) :=
  DerivedCategory.DerivedTensor.torDimensionLE (C := ModuleCat.{w} X) d

/-- Definition 21.46.1 (4): a module sheaf has Tor dimension at most `d` when its degree-zero
derived object has Tor-amplitude in `[-d, 0]`. -/
@[stacks 08FZ "(4)"]
abbrev HasTorDimensionLE (F : ModuleCat.{w} X) (d : ℕ) : Prop :=
  torDimensionLE (X := X) d F

end

end RingedSite.ModuleCat
