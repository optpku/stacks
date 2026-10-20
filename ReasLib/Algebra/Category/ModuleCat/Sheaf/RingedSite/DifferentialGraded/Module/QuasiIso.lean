/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.DifferentialGraded.Module.Acyclic

/-!
# Quasi-isomorphisms of differential graded modules

This leaf distinguishes quasi-isomorphisms of actual DG modules from quasi-isomorphisms in their
DG homotopy category, and provides the bridge induced by the quotient functor.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open ComplexShape
open DifferentialGradedCategory
open scoped DifferentialGradedCategory
open scoped SheafOfModules.RingedSite.DifferentialGradedAlgebra
open scoped SheafOfModules.RingedSite.DifferentialGradedModule

noncomputable section

-- Local instance justification (defeq pin): the homology-to-homotopy comparison must use the
-- finite biproducts canonically induced by the ambient Abelian category.
attribute [local instance] Abelian.hasFiniteBiproducts

universe u v w

namespace SheafOfModules.RingedSite.DifferentialGradedModule.Module

section Underlying

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
variable [HasSheafify J AddCommGrpCat.{w}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
variable [UnivLE.{max u v, w}]
variable {𝒪 : Sheaf J CommRingCat.{w}}

/-- A morphism of DG modules is a quasi-isomorphism when its underlying cochain map is a
quasi-isomorphism. -/
def quasiIso (𝒜 : DGA(𝒪)) : MorphismProperty Mod(𝒜, d) :=
  fun _ _ f ↦ _root_.QuasiIso f.toCochainMap

namespace QuasiIso

/-- A DG-module morphism is a quasi-isomorphism exactly when its underlying cochain map is a
quasi-isomorphism. -/
theorem iff_underlying (𝒜 : DGA(𝒪)) {X Y : Mod(𝒜, d)} (f : X ⟶ Y) :
    quasiIso 𝒜 f ↔ _root_.QuasiIso f.toCochainMap := sorry

/-- DG-module quasi-isomorphisms contain all identities. -/
instance containsIdentities (𝒜 : DGA(𝒪)) :
    (quasiIso 𝒜).ContainsIdentities := sorry

/-- DG-module quasi-isomorphisms are closed under composition. -/
instance isMultiplicative (𝒜 : DGA(𝒪)) :
    (quasiIso 𝒜).IsMultiplicative := sorry

/-- DG-module quasi-isomorphisms satisfy two-out-of-three. -/
instance hasTwoOutOfThree (𝒜 : DGA(𝒪)) :
    (quasiIso 𝒜).HasTwoOutOfThreeProperty := sorry

/-- DG-module quasi-isomorphisms are stable under retracts. -/
instance isStableUnderRetracts (𝒜 : DGA(𝒪)) :
    (quasiIso 𝒜).IsStableUnderRetracts := sorry

end QuasiIso

end Underlying

section Homotopy

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable [HasSheafify J AddCommGrpCat.{max u v}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
variable {𝒪 : Sheaf J CommRingCat.{max u v}}

namespace QuasiIso

/-- Passing a DG-module morphism to its homotopy class preserves and reflects the
quasi-isomorphism predicate. -/
theorem toK_map_iff (𝒜 : DGA(𝒪)) {X Y : Mod(𝒜, d)} (f : X ⟶ Y) :
    quasiIso 𝒜 f ↔ Homotopy.quasiIso 𝒜 ((toK 𝒜).map f) := sorry

end QuasiIso

end Homotopy

section Acyclic

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable [HasSheafify J AddCommGrpCat.{max u v}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
variable {𝒪 : Sheaf J CommRingCat.{max u v}}

namespace Acyclic

/-- Every morphism between acyclic DG modules is a quasi-isomorphism. -/
theorem quasiIso_of_source_target (𝒜 : DGA(𝒪))
    {X Y : Mod(𝒜, d)} (f : X ⟶ Y)
    (hX : acyclic 𝒜 X) (hY : acyclic 𝒜 Y) :
    quasiIso 𝒜 f := sorry

end Acyclic

end Acyclic

end SheafOfModules.RingedSite.DifferentialGradedModule.Module
