/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.RingedSite.Module.Derived.Basic
public import ReasLib.CategoryTheory.DerivedCategory.Functor.Bounded.Acyclic.Characterization
public import Mathlib.CategoryTheory.Abelian.RightDerived
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Higher Direct Images of Module Sheaves

This leaf owns the classical higher direct images of module sheaves along a
morphism of ringed sites.  It is the module-valued specialization of a right
derived direct-image functor.
-/

@[expose] public section

open CategoryTheory Limits

noncomputable section

universe uX vX uY vY w z

namespace RingedSite.Hom

/-- The degree-`i` higher direct image functor on module sheaves along a morphism of ringed
sites. -/
@[stacks 0715 "ringed-site higher direct image functor"]
abbrev higherDirectImageModuleFunctor
    {X : RingedSite.{uX, vX, w}} {Y : RingedSite.{uY, vY, w}}
    (f : Hom X Y) [UnivLE.{max uX vX, z}] [UnivLE.{max uY vY, z}]
    [HasInjectiveResolutions (ModuleCat.{z} X)] (i : ℕ) :
    ModuleCat.{z} X ⥤ ModuleCat.{z} Y :=
  f.modulePushforward.rightDerived i

/-- The degree-`i` higher direct image of a sheaf of modules along a morphism of ringed sites. -/
@[stacks 0715 "ringed-site higher direct image"]
abbrev higherDirectImageModule
    {X : RingedSite.{uX, vX, w}} {Y : RingedSite.{uY, vY, w}}
    (f : Hom X Y) [UnivLE.{max uX vX, z}] [UnivLE.{max uY vY, z}]
    [HasInjectiveResolutions (ModuleCat.{z} X)]
    (ℱ : ModuleCat.{z} X) (i : ℕ) : ModuleCat.{z} Y :=
  (higherDirectImageModuleFunctor f i).obj ℱ

/-- The map on higher direct images induced by a morphism of module sheaves. -/
abbrev higherDirectImageModuleMap
    {X : RingedSite.{uX, vX, w}} {Y : RingedSite.{uY, vY, w}}
    (f : Hom X Y) [UnivLE.{max uX vX, z}] [UnivLE.{max uY vY, z}]
    [HasInjectiveResolutions (ModuleCat.{z} X)]
    {ℱ 𝒢 : ModuleCat.{z} X} (φ : ℱ ⟶ 𝒢) (i : ℕ) :
    higherDirectImageModule f ℱ i ⟶ higherDirectImageModule f 𝒢 i :=
  (higherDirectImageModuleFunctor f i).map φ

namespace HigherDirectImage

/-- A chosen injective resolution computes the higher direct image of a module
sheaf by applying module pushforward degreewise and taking homology. -/
@[stacks 071I "module higher direct image from an injective resolution"]
noncomputable abbrev isoHomologyPushforward
    {X : RingedSite.{uX, vX, w}} {Y : RingedSite.{uY, vY, w}}
    (f : Hom X Y) [UnivLE.{max uX vX, z}] [UnivLE.{max uY vY, z}]
    [HasInjectiveResolutions (ModuleCat.{z} X)]
    (F : ModuleCat.{z} X) (I : InjectiveResolution F) (i : ℕ) :
    higherDirectImageModule f F i ≅
      (HomologicalComplex.homologyFunctor (ModuleCat.{z} Y)
        (ComplexShape.up ℕ) i).obj
          (((f.modulePushforward.mapHomologicalComplex
            (ComplexShape.up ℕ)).obj I.cocomplex)) :=
  I.isoRightDerivedObj f.modulePushforward i

/-- Vanishing of all positive higher direct images is the ordinary right-derived vanishing
condition for module pushforward. -/
@[stacks 0715 "positive higher direct-image vanishing"]
theorem vanishesAboveZero_iff
    {X : RingedSite.{uX, vX, w}} {Y : RingedSite.{uY, vY, w}}
    (f : Hom X Y) [UnivLE.{max uX vX, z}] [UnivLE.{max uY vY, z}]
    [HasInjectiveResolutions (ModuleCat.{z} X)] (ℱ : ModuleCat.{z} X) :
    Functor.RightDerived.Vanishes.aboveZero f.modulePushforward ℱ ↔
      ∀ q : ℕ, 0 < q → IsZero (higherDirectImageModule f ℱ q) := sorry

end HigherDirectImage

section TypedCheck

variable {X : RingedSite.{uX, vX, w}} {Y : RingedSite.{uY, vY, w}}
variable (f : Hom X Y) [UnivLE.{max uX vX, z}] [UnivLE.{max uY vY, z}]
variable [HasInjectiveResolutions (ModuleCat.{z} X)]
variable (ℱ : ModuleCat.{z} X) (i : ℕ)

end TypedCheck

end RingedSite.Hom
