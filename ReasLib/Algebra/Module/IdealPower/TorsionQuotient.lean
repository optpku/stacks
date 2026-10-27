/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Module.Torsion.PrimaryComponent
public import Mathlib.RingTheory.Noetherian.Defs
public import ReasLib.Algebra.Module.IdealPower.ModuleCat

@[expose] public section

noncomputable section

universe u v

open CategoryTheory Limits

namespace Ideal

variable {A : Type u} [CommRing A] [IsNoetherianRing A]
variable {M : Type v} [AddCommGroup M] [Module A M]
variable (I : Ideal A)

/-- Over a Noetherian ring, the quotient of a module by its `I`-power torsion has
zero `I`-power torsion. -/
theorem primaryComponent_quotient_eq_bot :
    I.primaryComponent (M ⧸ I.primaryComponent M) = ⊥ := sorry

/-- Over a Noetherian ring, the quotient map by `I`-power torsion induces an
isomorphism on the sequential colimits of the modules `Hom_A(I^n, M)`. -/
@[instance]
instance instIsIso_colimMap_powerHomModuleDiagramMap_mkQ [IsNoetherianRing A] :
    IsIso (colim.map (I.powerHomModuleDiagramMap (Submodule.mkQ (I.primaryComponent M)))) := sorry

end Ideal
