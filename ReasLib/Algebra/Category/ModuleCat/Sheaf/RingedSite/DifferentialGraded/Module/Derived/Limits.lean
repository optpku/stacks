/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.DifferentialGraded.Module.Derived.KInjective
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.DifferentialGraded.Module.KInjective.Limits
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.DifferentialGraded.Module.KInjective.Resolution
import Mathlib.Tactic.CrossRefAttribute

/-!
# Products and coproducts in the DG derived category

The DG derived category has coproducts and products indexed in a universe that fits the
coefficient universe.  Coproducts are computed directly on DG modules.  Products are computed on
families of K-injective representatives; no claim is made that localization preserves arbitrary
products before replacement.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open DifferentialGradedCategory
open scoped DifferentialGradedCategory
open scoped SheafOfModules.RingedSite.DifferentialGradedAlgebra
open scoped SheafOfModules.RingedSite.DifferentialGradedModule

noncomputable section

-- Mathlib keeps this canonical finite-biproduct construction non-global.  Products and
-- coproducts in the Verdier quotient must use the pinned triangulated structure of this stack.
attribute [local instance] Abelian.hasFiniteBiproducts

universe u v w

namespace SheafOfModules.RingedSite.DifferentialGradedModule.DerivedCategory

section


variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable [HasWeakSheafify J AddCommGrpCat.{max u v}]
variable [HasSheafify J AddCommGrpCat.{max u v}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
variable {𝒪 : Sheaf J CommRingCat.{max u v}}

namespace Coproduct

/-- The intrinsic DG derived category has coproducts whose index universe fits the coefficient
universe. -/
@[stacks 0FT9]
instance hasCoproducts [UnivLE.{w, max u v}] (𝒜 : DGA(𝒪)) :
    HasCoproducts.{w} (DerivedCategory 𝒜) := sorry

/-- Localization from the DG homotopy category preserves arbitrary coproducts. -/
instance qhPreserves (𝒜 : DGA(𝒪)) (ι : Type w) :
    PreservesColimitsOfShape (Discrete ι) (Qh 𝒜) := sorry

/-- The canonical functor from DG modules to the derived category preserves arbitrary
coproducts. -/
@[stacks 0FT9]
instance qPreserves (𝒜 : DGA(𝒪)) (ι : Type w) :
    PreservesColimitsOfShape (Discrete ι) (Q 𝒜) := sorry

end Coproduct

namespace Product

/-- The intrinsic DG derived category has products whose index universe fits the coefficient
universe. -/
@[stacks 0FT9]
instance hasProducts [UnivLE.{w, max u v}] (𝒜 : DGA(𝒪)) :
    HasProducts.{w} (DerivedCategory 𝒜) := sorry

/-- A product of K-injective DG homotopy objects computes their product after localization. -/
theorem qhPreservesOfKInjective (𝒜 : DGA(𝒪)) {ι : Type w}
    (I : ι → K ℤ Mod(𝒜, d)) [HasProduct I]
    (hI : ∀ i, Homotopy.kInjective 𝒜 (I i)) :
    PreservesLimit (Discrete.functor I) (Qh 𝒜) := sorry

/-- Localization preserves a product diagram whose factors carry K-injectivity instances. -/
instance qhPreserves (𝒜 : DGA(𝒪)) {ι : Type w}
    (I : ι → K ℤ Mod(𝒜, d)) [HasProduct I]
    [∀ i, (Homotopy.kInjective 𝒜).Is (I i)] :
    PreservesLimit (Discrete.functor I) (Qh 𝒜) := sorry

/-- A product of K-injective DG module representatives computes their product in the derived
category. -/
@[stacks 0FT9]
instance qPreserves (𝒜 : DGA(𝒪)) {ι : Type w}
    (I : ι → Mod(𝒜, d)) [HasProduct I]
    [∀ i, Module.IsKInjective (I i)] :
    PreservesLimit (Discrete.functor I) (Q 𝒜) := sorry

end Product

end


end SheafOfModules.RingedSite.DifferentialGradedModule.DerivedCategory
