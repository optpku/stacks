/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite

/-!
# Mixed-scalar extensions on a first-order thickening

This module defines mixed-scalar short exact sequences of sheaves of modules on a same-site
morphism of commutative ring sheaves.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u v

namespace SheafOfModules.RingedSite
namespace FirstOrderThickening

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat.{max u v} RingCat.{max u v})]
variable {𝒪' 𝒪 : Sheaf J CommRingCat.{max u v}} (π : 𝒪' ⟶ 𝒪)

/-- A mixed-scalar extension with kernel and quotient over 𝒪 and middle term over 𝒪'. -/
structure Extension where
  /-- The kernel module over 𝒪. -/
  kernel : ringedSiteModuleCategory.{u, v, max u v, max u v} J 𝒪
  /-- The middle module over 𝒪'. -/
  middle : ringedSiteModuleCategory.{u, v, max u v, max u v} J 𝒪'
  /-- The quotient module over 𝒪. -/
  quot : ringedSiteModuleCategory.{u, v, max u v, max u v} J 𝒪
  /-- The inclusion after restriction of scalars along π. -/
  ι : (restrictionAlong π).obj kernel ⟶ middle
  /-- The projection after restriction of scalars along π. -/
  p : middle ⟶ (restrictionAlong π).obj quot
  /-- The two maps compose to zero. -/
  zero : ι ≫ p = 0
  /-- The associated sequence is short exact. -/
  shortExact : (ShortComplex.mk ι p zero).ShortExact

/-- Assemble a mixed-scalar extension from its modules, maps, and exactness witness. -/
def ofMaps (kernel : ringedSiteModuleCategory.{u, v, max u v, max u v} J 𝒪)
    (middle : ringedSiteModuleCategory.{u, v, max u v, max u v} J 𝒪')
    (quot : ringedSiteModuleCategory.{u, v, max u v, max u v} J 𝒪)
    (ι : (restrictionAlong π).obj kernel ⟶ middle)
    (p : middle ⟶ (restrictionAlong π).obj quot)
    (zero : ι ≫ p = 0)
    (shortExact : (ShortComplex.mk ι p zero).ShortExact) :
    Extension π where
  kernel := kernel
  middle := middle
  quot := quot
  ι := ι
  p := p
  zero := zero
  shortExact := shortExact

variable {π}

/-- The short complex underlying a mixed-scalar extension. -/
abbrev shortComplex (E : Extension π) :
    ShortComplex (ringedSiteModuleCategory.{u, v, max u v, max u v} J 𝒪') :=
  ShortComplex.mk E.ι E.p E.zero

/-- The short complex underlying a mixed-scalar extension is short exact. -/
theorem shortComplex_shortExact (E : Extension π) :
    (shortComplex E).ShortExact := E.shortExact

end FirstOrderThickening
end SheafOfModules.RingedSite
