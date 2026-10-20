/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.DifferentialGraded.Module.QuasiIso
public import ReasLib.CategoryTheory.ObjectProperty.Localization.Triangulated.Saturation
import Mathlib.Tactic.CrossRefAttribute

/-!
# Localization structure on DG homotopy quasi-isomorphisms

Quasi-isomorphisms in the intrinsic DG homotopy category form the saturated localization system
associated to the triangulated subcategory of acyclic objects.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open DifferentialGradedCategory
open scoped DifferentialGradedCategory
open scoped SheafOfModules.RingedSite.DifferentialGradedAlgebra
open scoped SheafOfModules.RingedSite.DifferentialGradedModule

noncomputable section

-- Mathlib keeps this canonical finite-biproduct construction non-global; the triangulated
-- localization API below requires the same choice throughout this owner leaf.
attribute [local instance] Abelian.hasFiniteBiproducts

universe u v

namespace SheafOfModules.RingedSite.DifferentialGradedModule.Homotopy.QuasiIso

section

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable [HasWeakSheafify J AddCommGrpCat.{max u v}]
variable [HasSheafify J AddCommGrpCat.{max u v}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
variable {𝒪 : Sheaf J CommRingCat.{max u v}}

/-- DG homotopy quasi-isomorphisms satisfy the intrinsic saturation axiom. -/
instance hasSaturationAxiom (𝒜 : DGA(𝒪)) :
    (Homotopy.quasiIso 𝒜).HasSaturationAxiom := sorry

/-- DG homotopy quasi-isomorphisms form a saturated multiplicative system. -/
@[stacks 0FT4]
instance isSaturatedMultiplicativeSystem (𝒜 : DGA(𝒪)) :
    (Homotopy.quasiIso 𝒜).IsSaturatedMultiplicativeSystem := sorry

/-- DG homotopy quasi-isomorphisms are compatible with the triangulated structure. -/
@[stacks 0FT4]
instance isCompatibleWithTriangulation (𝒜 : DGA(𝒪)) :
    (Homotopy.quasiIso 𝒜).IsCompatibleWithTriangulation := sorry

end


end SheafOfModules.RingedSite.DifferentialGradedModule.Homotopy.QuasiIso
