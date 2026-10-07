module

public import ReasLib.Algebra.Homology.DerivedCategory.ModuleCat.IdealPower.Torsion
public import ReasLib.Algebra.Category.ModuleCat.FinitePresentation
public import ReasLib.CategoryTheory.DerivedCategory.CohomologyIn.Bounded
public import Mathlib.Data.Int.ConditionallyCompleteOrder
public import Mathlib.Order.ConditionallyCompleteLattice.Basic
public import Mathlib.RingTheory.Noetherian.Defs

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open scoped DerivedCategory.CohomologyIn

noncomputable section

universe u

namespace Ideal

/-- The depth of a bounded-below complex with coherent cohomology relative to `I` is the
largest extended integer below which its local cohomology supported at `I` vanishes. -/
noncomputable def derivedDepth
    {A : Type u} [CommRing A] [IsNoetherianRing A] (I : Ideal A)
    (RΓ : DerivedCategory (ModuleCat.{u} A) ⥤
      DerivedCategory.IdealPowerTorsion I)
    (hRΓ : DerivedCategory.IdealPowerTorsion.inclusion I ⊣ RΓ)
    (K : DerivedCategory.Plus.CohomologyIn
      (ModuleCat.isFinitePresentation A)) : WithTop ℤ :=
  sSup {m : WithTop ℤ | ∀ i : ℤ, (i : WithTop ℤ) < m →
    IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).obj
      (RΓ.obj ((DerivedCategory.Plus.CohomologyIn.ambient
        (ModuleCat.isFinitePresentation A)).obj K)).obj)}

/-- `Ideal.derivedDepth` is the supremum of the extended integers below which all supported
local cohomology objects vanish. -/
theorem derivedDepth_eq_sSup
    {A : Type u} [CommRing A] [IsNoetherianRing A] (I : Ideal A)
    (RΓ : DerivedCategory (ModuleCat.{u} A) ⥤
      DerivedCategory.IdealPowerTorsion I)
    (hRΓ : DerivedCategory.IdealPowerTorsion.inclusion I ⊣ RΓ)
    (K : DerivedCategory.Plus.CohomologyIn
      (ModuleCat.isFinitePresentation A)) :
    I.derivedDepth RΓ hRΓ K =
      sSup {m : WithTop ℤ | ∀ i : ℤ, (i : WithTop ℤ) < m →
        IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).obj
          (RΓ.obj ((DerivedCategory.Plus.CohomologyIn.ambient
            (ModuleCat.isFinitePresentation A)).obj K)).obj)} := sorry

/-- The derived depth is the greatest extended integer whose lower integer degrees have
vanishing supported local cohomology. -/
theorem isGreatest_derivedDepth
    {A : Type u} [CommRing A] [IsNoetherianRing A] (I : Ideal A)
    (RΓ : DerivedCategory (ModuleCat.{u} A) ⥤
      DerivedCategory.IdealPowerTorsion I)
    (hRΓ : DerivedCategory.IdealPowerTorsion.inclusion I ⊣ RΓ)
    (K : DerivedCategory.Plus.CohomologyIn
      (ModuleCat.isFinitePresentation A)) :
    IsGreatest {m : WithTop ℤ | ∀ i : ℤ, (i : WithTop ℤ) < m →
      IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).obj
        (RΓ.obj ((DerivedCategory.Plus.CohomologyIn.ambient
          (ModuleCat.isFinitePresentation A)).obj K)).obj)}
      (I.derivedDepth RΓ hRΓ K) := sorry

/-- The derived depth is independent of the chosen right adjoint to the inclusion of
`I`-power-torsion derived objects. -/
theorem derivedDepth_eq_of_rightAdjoint
    {A : Type u} [CommRing A] [IsNoetherianRing A] (I : Ideal A)
    (RΓ₁ RΓ₂ : DerivedCategory (ModuleCat.{u} A) ⥤
      DerivedCategory.IdealPowerTorsion I)
    (hRΓ₁ : DerivedCategory.IdealPowerTorsion.inclusion I ⊣ RΓ₁)
    (hRΓ₂ : DerivedCategory.IdealPowerTorsion.inclusion I ⊣ RΓ₂)
    (K : DerivedCategory.Plus.CohomologyIn
      (ModuleCat.isFinitePresentation A)) :
    I.derivedDepth RΓ₁ hRΓ₁ K = I.derivedDepth RΓ₂ hRΓ₂ K := sorry

end Ideal

namespace CategoryTheory.DerivedCategory

/-- Over a local Noetherian ring, the depth of a bounded-below coherent complex is its depth
relative to the maximal ideal. -/
noncomputable abbrev depth
    {A : Type u} [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    (RΓ : DerivedCategory (ModuleCat.{u} A) ⥤
      IdealPowerTorsion (IsLocalRing.maximalIdeal A))
    (hRΓ : IdealPowerTorsion.inclusion (IsLocalRing.maximalIdeal A) ⊣ RΓ)
    (K : Plus.CohomologyIn (ModuleCat.isFinitePresentation A)) : WithTop ℤ :=
  (IsLocalRing.maximalIdeal A).derivedDepth RΓ hRΓ K

/-- Local derived depth is depth relative to the maximal ideal. -/
theorem depth_eq_maximalIdeal_derivedDepth
    {A : Type u} [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    (RΓ : DerivedCategory (ModuleCat.{u} A) ⥤
      IdealPowerTorsion (IsLocalRing.maximalIdeal A))
    (hRΓ : IdealPowerTorsion.inclusion (IsLocalRing.maximalIdeal A) ⊣ RΓ)
    (K : Plus.CohomologyIn (ModuleCat.isFinitePresentation A)) :
    depth RΓ hRΓ K =
      (IsLocalRing.maximalIdeal A).derivedDepth RΓ hRΓ K := sorry

end CategoryTheory.DerivedCategory
