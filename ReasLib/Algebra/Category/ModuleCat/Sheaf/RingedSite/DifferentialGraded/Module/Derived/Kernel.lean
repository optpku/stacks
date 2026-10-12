/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.DifferentialGraded.Module.Derived.Basic
public import ReasLib.CategoryTheory.ObjectProperty.Localization.Triangulated.VerdierQuotient.Kernel
import Mathlib.Tactic.CrossRefAttribute

/-!
# Kernel of the DG derived localization

This leaf records the objectwise computation of the kernel of the DG Verdier quotient.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open DifferentialGradedCategory
open scoped DifferentialGradedCategory
open scoped SheafOfModules.RingedSite.DifferentialGradedAlgebra
open scoped SheafOfModules.RingedSite.DifferentialGradedModule

noncomputable section

-- Mathlib keeps this canonical finite-biproduct construction non-global; kernel computation is
-- tied to the pinned Verdier-quotient structure from the imported owner.
attribute [local instance] Abelian.hasFiniteBiproducts

universe u v

namespace SheafOfModules.RingedSite.DifferentialGradedModule.DerivedCategory

section

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable [HasWeakSheafify J AddCommGrpCat.{max u v}]
variable [HasSheafify J AddCommGrpCat.{max u v}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
variable {𝒪 : Sheaf J CommRingCat.{max u v}}

/-- The kernel of the homotopy-to-derived localization is exactly the acyclic subcategory. -/
@[stacks 0FT6]
theorem Qh_kernel_eq (𝒜 : DGA(𝒪)) :
    Functor.kernel (Qh 𝒜) = Homotopy.acyclic 𝒜 := sorry

/-- A DG homotopy object becomes zero in the derived category exactly when it is acyclic. -/
theorem Qh_obj_isZero_iff (𝒜 : DGA(𝒪)) (X : K ℤ Mod(𝒜, d)) :
    IsZero ((Qh 𝒜).obj X) ↔ Homotopy.acyclic 𝒜 X := sorry

/-- A DG module becomes zero in the derived category exactly when its underlying cochain complex
is acyclic. -/
theorem Q_obj_isZero_iff (𝒜 : DGA(𝒪)) (X : Mod(𝒜, d)) :
    IsZero ((Q 𝒜).obj X) ↔ X.toComplex.Acyclic := sorry

end


end SheafOfModules.RingedSite.DifferentialGradedModule.DerivedCategory
