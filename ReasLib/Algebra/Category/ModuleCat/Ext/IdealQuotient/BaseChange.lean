/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import ReasLib.Algebra.Category.ModuleCat.Ext.FlatBaseChange
public import ReasLib.RingTheory.RingHom.Quotient.Flat
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Ext base change for ideal quotients

This leaf isolates the finite quotient step in ideal-power torsion base change.  The source
module is the canonical quotient `R ⧸ I`; the main ideal-power theorem is a separate reduction
layer and does not duplicate this statement.
@stack 05EG
-/

@[expose] public section

noncomputable section

open CategoryTheory Limits Abelian

universe u

namespace CategoryTheory.ModuleCat.Ext.IdealQuotient.BaseChange

variable {R S : Type u} [CommRing R] [CommRing S]

/-- Tag 05EG: flat base change on `Ext¹(R ⧸ I, N)` is bijective when `I` is finitely generated
and the ring map is an isomorphism modulo `I`. -/
@[stacks 05EG "Ext base change for a finite ideal quotient"]
theorem map_bijective (f : R →+* S) (I : Ideal R) (hI : I.FG)
    (N : ModuleCat.{u} R) (hf : f.Flat)
    (hquot : Function.Bijective (f.quotientByIdeal I)) :
    Function.Bijective
      (FlatBaseChange.map f (ModuleCat.of R (R ⧸ I)) N hf 1) := sorry

/-- Tag 05EG: the finite quotient step applies uniformly to every positive ideal power. -/
@[stacks 05EG "Ext base change for a positive ideal-power quotient"]
theorem map_bijective_pow (f : R →+* S) (I : Ideal R) (hI : I.FG) (n : ℕ+)
    (N : ModuleCat.{u} R) (hf : f.Flat)
    (hquot : Function.Bijective (f.quotientByIdeal I)) :
    Function.Bijective
      (FlatBaseChange.map f (ModuleCat.of R (R ⧸ I ^ (n : ℕ))) N hf 1) := sorry

end CategoryTheory.ModuleCat.Ext.IdealQuotient.BaseChange
