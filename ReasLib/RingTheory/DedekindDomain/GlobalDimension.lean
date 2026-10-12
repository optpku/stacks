/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Module.Projective
public import Mathlib.RingTheory.DedekindDomain.Basic
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.RingTheory.GlobalDimension.IdealQuotient
public import ReasLib.RingTheory.GlobalDimension.Injective

@[expose] public section

/-!
# Homological Dimension of Dedekind Domains

@stack 0EX0

Ideals in a Dedekind domain are projective, so ideal quotients have projective dimension at most
one. The ideal-quotient criterion upgrades this to a global-dimension bound, from which the
injective-dimension and higher-Ext views follow uniformly.
-/

open CategoryTheory

universe u

namespace IsDedekindDomain

variable {R : Type u} [CommRing R] [IsDedekindDomain R]

/-- Ideals in a Dedekind domain are projective modules. -/
@[stacks 0EX0 "projective ideals"]
instance idealProjective (I : Ideal R) : Module.Projective R I := sorry

/-- Stacks 0EX0: a Dedekind domain has global dimension at most one. -/
@[stacks 0EX0 "global dimension at most one"]
instance globalDimensionLEOne (R : Type u) [CommRing R] [IsDedekindDomain R] :
    HasGlobalDimensionLE R 1 := sorry

/-- Stacks 0EX0: every module over a Dedekind domain has injective dimension at most one. -/
@[stacks 0EX0 "injective dimension at most one"]
theorem injectiveDimension_le_one (M : ModuleCat.{u} R) :
    injectiveDimension M ≤ 1 := sorry

/-- Stacks 0EX0: all extension groups in degrees at least two over a Dedekind domain are
subsingletons. -/
@[stacks 0EX0 "higher Ext vanishing"]
theorem ext_subsingleton (X Y : ModuleCat.{u} R) (i : ℕ) (hi : 2 ≤ i) :
    Subsingleton (Abelian.Ext X Y i) := sorry

section

variable (M : ModuleCat.{u} R)

#synth HasProjectiveDimensionLE M 1
#synth HasInjectiveDimensionLE M 1

end

end IsDedekindDomain
