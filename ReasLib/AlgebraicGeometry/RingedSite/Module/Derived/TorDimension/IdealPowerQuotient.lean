module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Ideal.Quotient
public import ReasLib.AlgebraicGeometry.RingedSite.Module.Derived.ChangeOfRings
public import ReasLib.AlgebraicGeometry.RingedSite.Module.Derived.TorDimension
public import ReasLib.AlgebraicGeometry.RingedSite.Module.Derived.Tensor
import Mathlib.Tactic.CrossRefAttribute

/-!
# Tor-amplitude over ideal-power quotients

The quotient ringed sites, their projections, and the associated derived extensions of scalars
are reusable data indexed by every natural exponent.  The propagation results only require a
positive exponent, reflecting the mathematical statement rather than restricting the data owner.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open RingedSite.Hom

noncomputable section

universe u v w

namespace SheafOfModules.RingedSite.IdealSheaf.PowerQuotient

-- Use the existing standard derived model and the native tensor totalizations.
attribute [local instance] RingedSite.Hom.moduleCat_hasDerivedCategory
  RingedSite.Hom.RingPresentation.moduleHasDerivedCategory
  SheafOfModules.RingedSite.moduleCategoryHasMapBifunctor

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
variable [UnivLE.{max u v, w}]
variable [HasWeakSheafify J CommRingCat.{w}]
variable [HasWeakSheafify J AddCommGrpCat.{w}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
variable {O : Sheaf J CommRingCat.{w}}

/-- The commutative ringed site `(C, J, O / I ^ n)`. -/
@[stacks 0942 "ideal-power quotient site"]
noncomputable abbrev ringedSite
    (I : Subobject (unitModule J O)) (n : ℕ) : RingedSite.{u, v, w} :=
  RingedSite.ofCommRingSheaf J (sheaf I n)

/-- The canonical morphism `(C, J, O / I ^ n) ⟶ (C, J, O)`. -/
@[stacks 0942 "ideal-power quotient projection"]
noncomputable abbrev projectionHom
    (I : Subobject (unitModule J O)) (n : ℕ) :
    ringedSite I n ⟶ RingedSite.ofCommRingSheaf J O :=
  sameSiteHom (projection I n)

/-- Derived extension of scalars from `O` to `O / I ^ n`. -/
@[stacks 0942 "ideal-power quotient derived pullback"]
noncomputable abbrev pullbackDerived
    (I : Subobject (unitModule J O)) (n : ℕ) :
    ModuleDerived.{w} (RingedSite.ofCommRingSheaf J O) ⥤
      ModuleDerived.{w} (ringedSite I n) :=
  SameSite.pullbackDerived (projection I n)

/-- An upper bound after reduction modulo `I` is
preserved after reduction modulo every positive power of `I`. -/
@[stacks 0942 "(1), sharp bound"]
theorem pullbackDerived_isLE
    (I : Subobject (unitModule J O))
    (K : ModuleDerived.{w} (RingedSite.ofCommRingSheaf J O)) {b : ℤ}
    (hModI : @DerivedCategory.IsLE (ringedSite I 1).ModuleCat _ _
      (moduleCategoryHasDerivedCategory (𝒪 := sheaf I 1))
      ((pullbackDerived I 1).obj K) b) (n : ℕ+) :
    @DerivedCategory.IsLE (ringedSite I n).ModuleCat _ _
      (moduleCategoryHasDerivedCategory (𝒪 := sheaf I n))
      ((pullbackDerived I n).obj K) b := sorry

/-- Boundedness above after reduction modulo `I` gives one uniform
upper bound after reduction modulo every positive power of `I`. -/
@[stacks 0942 "(1)"]
theorem pullbackDerived_uniformlyBoundedAbove
    (I : Subobject (unitModule J O))
    (K : ModuleDerived.{w} (RingedSite.ofCommRingSheaf J O))
    (hModI : ∃ b : ℤ, @DerivedCategory.IsLE (ringedSite I 1).ModuleCat _ _
      (moduleCategoryHasDerivedCategory (𝒪 := sheaf I 1))
      ((pullbackDerived I 1).obj K) b) :
    ∃ b : ℤ, ∀ n : ℕ+, @DerivedCategory.IsLE (ringedSite I n).ModuleCat _ _
      (moduleCategoryHasDerivedCategory (𝒪 := sheaf I n))
      ((pullbackDerived I n).obj K) b := sorry

/-- A Tor-amplitude interval after reduction modulo `I` is
preserved after reduction modulo every positive power of `I`. -/
@[stacks 0942 "(2)"]
theorem pullbackDerived_hasTorAmplitudeIn
    (I : Subobject (unitModule J O))
    [∀ n : ℕ, DerivedCategory.DerivedTensor.Right.Has
      (C := ringedSiteModuleCategory.{u, v, w, w} J (sheaf I n))]
    (K : ModuleDerived.{w} (RingedSite.ofCommRingSheaf J O)) (a b : ℤ)
    (hModI : RingedSite.Hom.ModuleDerived.HasTorAmplitudeIn
      (O := sheaf I 1) ((pullbackDerived I 1).obj K) a b)
    (n : ℕ+) :
    RingedSite.Hom.ModuleDerived.HasTorAmplitudeIn
      (O := sheaf I n) ((pullbackDerived I n).obj K) a b := sorry

end SheafOfModules.RingedSite.IdealSheaf.PowerQuotient
