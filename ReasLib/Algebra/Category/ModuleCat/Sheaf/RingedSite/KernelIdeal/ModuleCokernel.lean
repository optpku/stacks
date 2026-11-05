/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.KernelIdeal
public import ReasLib.CategoryTheory.Abelian.KernelSubobject.Quotient

/-! # The module cokernel of a kernel ideal

The epimorphism hypothesis is imposed on the specified module map, not on the map of rings.
This comparison is distinct from the existing quotient comparison of ring sheaves.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe u v w

namespace SheafOfModules.RingedSite.KernelIdeal

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
variable [HasSheafify J AddCommGrpCat.{w}] [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
variable {A Q : Sheaf J CommRingCat.{w}} (π : A ⟶ Q)

/-- The actual module cokernel comparison for the specified module epimorphism. -/
def moduleCokernelIso [Epi (map π)] :
    cokernel (ι π) ≅ (SheafOfModules.pushforward (ringedSiteStructureMap π)).obj
      (SheafOfModules.unit (ringSheaf J Q)) :=
  Abelian.kernelSubobjectCokernelIso (map π)

/-- The comparison carries the native cokernel projection to `map π`. -/
@[reassoc (attr := simp)]
theorem π_comp_moduleCokernelIso_hom [Epi (map π)] :
    cokernel.π (ι π) ≫ (moduleCokernelIso π).hom = map π :=
  Abelian.π_comp_kernelSubobjectCokernelIso_hom (map π)

end SheafOfModules.RingedSite.KernelIdeal
