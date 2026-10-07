module

public import ReasLib.AlgebraicGeometry.RingedSite.Module.Derived.Basic
public import ReasLib.AlgebraicGeometry.RingedSite.Module.Derived.Localization
public import ReasLib.AlgebraicGeometry.RingedSite.Module.HigherDirectImage
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous.FiniteLimits
public import ReasLib.CategoryTheory.DerivedCategory.Functor.Bounded.RightDerived.Properties
import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Bounded-below derived pushforward on ringed-site modules

The bounded-below direct image is the canonical right-derived functor of the
additive module pushforward.  Its acyclicity witness remains an explicit
typeclass input, shared by all downstream restrictions.
-/

open CategoryTheory
-- Local instance justification (defeq pin): the generic ringed-site ModuleCat derived owner is
-- required by the derived-category APIs in this presentation.
attribute [local instance] RingedSite.Hom.moduleCat_hasDerivedCategory

noncomputable section

universe z uX vX uY vY w

namespace RingedSite.Hom

variable {X : RingedSite.{uX, vX, w}} {Y : RingedSite.{uY, vY, w}}

/-- The bounded-below right-derived direct image on module sheaves. -/
@[stacks 015A "bounded-below derived pushforward on modules"]
noncomputable abbrev modulePushforwardDerivedPlus
    (f : RingedSite.Hom X Y)
    [UnivLE.{max uX vX, z}] [UnivLE.{max uY vY, z}]
    [Functor.HasRightDerivedFunctor
      (f.modulePushforward.{z}).toBoundedBelowDerived
      (HomotopyCategory.Plus.quasiIso (ModuleCat.{z} X))] :
    DerivedCategory.Plus (ModuleCat.{z} X) ⥤
      DerivedCategory.Plus (ModuleCat.{z} Y) :=
  Functor.RightDerived.Bounded.functor f.modulePushforward

namespace modulePushforwardDerivedPlus

/-- The localization unit for bounded-below derived module pushforward. -/
@[stacks 015A "bounded-below derived pushforward unit"]
noncomputable abbrev unit
    (f : RingedSite.Hom X Y)
    [UnivLE.{max uX vX, z}] [UnivLE.{max uY vY, z}]
    [Functor.HasRightDerivedFunctor
      (f.modulePushforward.{z}).toBoundedBelowDerived
      (HomotopyCategory.Plus.quasiIso (ModuleCat.{z} X))] :
    (f.modulePushforward.{z}).toBoundedBelowDerived ⟶
      DerivedCategory.Plus.Qh ⋙ modulePushforwardDerivedPlus f :=
  Functor.RightDerived.Bounded.unit f.modulePushforward

/-- The degree-`n` cohomology functor of bounded-below derived module pushforward. -/
@[stacks 015A "bounded-below derived pushforward cohomology functor"]
abbrev cohomologyFunctor
    (f : RingedSite.Hom X Y) (n : ℤ)
    [UnivLE.{max uX vX, z}] [UnivLE.{max uY vY, z}]
    [Functor.HasRightDerivedFunctor
      (f.modulePushforward.{z}).toBoundedBelowDerived
      (HomotopyCategory.Plus.quasiIso (ModuleCat.{z} X))] :
    DerivedCategory.Plus (ModuleCat.{z} X) ⥤ ModuleCat.{z} Y :=
  modulePushforwardDerivedPlus f ⋙ DerivedCategory.Plus.homologyFunctor (ModuleCat.{z} Y) n

/-- The degree-`n` cohomology object of bounded-below derived module pushforward. -/
@[stacks 015A "bounded-below derived pushforward cohomology"]
abbrev cohomology
    (f : RingedSite.Hom X Y)
    [UnivLE.{max uX vX, z}] [UnivLE.{max uY vY, z}]
    [Functor.HasRightDerivedFunctor
      (f.modulePushforward.{z}).toBoundedBelowDerived
      (HomotopyCategory.Plus.quasiIso (ModuleCat.{z} X))]
    (K : DerivedCategory.Plus (ModuleCat.{z} X)) (n : ℤ) :
    ModuleCat.{z} Y :=
  (cohomologyFunctor f n).obj K

/-- On a module placed in degree zero, nonnegative cohomology of bounded-below derived
pushforward agrees with the ordinary higher direct image. -/
@[stacks 0715 "bounded-derived higher direct-image comparison"]
theorem cohomology_single_isIsomorphic_higherDirectImage
    (f : RingedSite.Hom X Y)
    [UnivLE.{max uX vX, z}] [UnivLE.{max uY vY, z}]
    [Functor.HasRightDerivedFunctor
      (f.modulePushforward.{z}).toBoundedBelowDerived
      (HomotopyCategory.Plus.quasiIso (ModuleCat.{z} X))]
    [HasInjectiveResolutions (ModuleCat.{z} X)]
    (ℱ : ModuleCat.{z} X) (n : ℕ) :
    IsIsomorphic
      (cohomology f ((DerivedCategory.Plus.singleFunctor (ModuleCat.{z} X) 0).obj ℱ)
        (Int.ofNat n))
      (higherDirectImageModule f ℱ n) := sorry

end modulePushforwardDerivedPlus

end RingedSite.Hom

end
