/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.DifferentialGraded.Limits
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.DifferentialGraded.Module.Homotopy.KInjective
public import ReasLib.CategoryTheory.ObjectProperty.Orthogonal.Limits

/-!
# Products and coproducts in the DG homotopy category

Products and coproducts in the intrinsic DG homotopy category are computed by the corresponding
constructions on DG modules.  The closure APIs for acyclic, quasi-isomorphic, and K-injective
objects record the parts used by derived-category applications.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open DifferentialGradedCategory
open scoped DifferentialGradedCategory
open scoped SheafOfModules.RingedSite.DifferentialGradedAlgebra
open scoped SheafOfModules.RingedSite.DifferentialGradedModule

noncomputable section

-- Local instance justification (search instability): Mathlib deliberately keeps this theorem
-- non-global because registering it breaks instance search in module-sheaf constructions; the
-- homotopy-category limit construction needs the finite-biproduct witness in this owner only.
attribute [local instance] Abelian.hasFiniteBiproducts

universe u v w

namespace SheafOfModules.RingedSite.DifferentialGradedModule.Homotopy

section


variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable [HasWeakSheafify J AddCommGrpCat.{max u v}]
variable [HasSheafify J AddCommGrpCat.{max u v}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
variable {𝒪 : Sheaf J CommRingCat.{max u v}}

/-- The intrinsic DG homotopy category has arbitrary coproducts. -/
instance hasCoproducts (𝒜 : DGA(𝒪)) :
    HasCoproducts (K ℤ Mod(𝒜, d)) := sorry

/-- The intrinsic DG homotopy category has arbitrary products. -/
instance hasProducts (𝒜 : DGA(𝒪)) :
    HasProducts (K ℤ Mod(𝒜, d)) := sorry

/-- Passage from DG modules to the homotopy category preserves coproducts. -/
instance toKPreservesCoproducts (𝒜 : DGA(𝒪)) (ι : Type w) :
    PreservesColimitsOfShape (Discrete ι) (toK 𝒜) := sorry

/-- Passage from DG modules to the homotopy category preserves products. -/
instance toKPreservesProducts (𝒜 : DGA(𝒪)) (ι : Type w) :
    PreservesLimitsOfShape (Discrete ι) (toK 𝒜) := sorry

namespace Acyclic

/-- A coproduct of acyclic DG homotopy objects is acyclic. -/
theorem coproduct (𝒜 : DGA(𝒪)) {ι : Type w}
    (X : ι → K ℤ Mod(𝒜, d)) [HasCoproduct X]
    (hX : ∀ i, acyclic 𝒜 (X i)) :
    acyclic 𝒜 (∐ X) := sorry

end Acyclic

namespace QuasiIso

/-- A coproduct of DG homotopy quasi-isomorphisms is a quasi-isomorphism. -/
theorem coproduct (𝒜 : DGA(𝒪)) {ι : Type w}
    {X Y : ι → K ℤ Mod(𝒜, d)}
    [HasCoproduct X] [HasCoproduct Y]
    (f : ∀ i, X i ⟶ Y i) (hf : ∀ i, quasiIso 𝒜 (f i)) :
    quasiIso 𝒜 (CategoryTheory.Limits.Sigma.map f) := sorry

end QuasiIso

end


end SheafOfModules.RingedSite.DifferentialGradedModule.Homotopy
