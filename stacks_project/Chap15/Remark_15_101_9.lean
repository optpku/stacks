/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.Algebra.Homology.DerivedCategory.ModuleCat.IdealPower.Ext

/-!
# Remark 15.101.9

@stack 0EGZ
-/

@[expose] public section

open CategoryTheory
open IadicFiniteModuleSystem
open IadicFiniteModuleSystem.Ext

universe u v

/- Remark 15.101.9 (0EGZ): the reduced Ext groups form a weak ideal-power system.  There is a
uniform exponent `c` and, for `m ≫ n ≫ 0`, canonical cross-index maps from the `I ^ c`-part of
the reduced Ext group at stage `m`, modulo its `I ^ n`-part, to the reduced Ext group at stage
`n` modulo its `I ^ c`-torsion.  Their kernels and cokernels are annihilated by `I ^ c`.

The reusable owner regards these source and target quotients as `A`-modules.  This expresses the
source formula without assigning the stage-`m` reduced modules an invalid `A / I ^ n` action. -/
section

variable {A : Type u} [CommRing A] [IsNoetherianRing A] [Small.{v} A]
variable (I : Ideal A) (M N : ModuleCat.{v} A)
variable [Module.Finite A M] [Module.Finite A N]
variable (i : ℕ)

@[stacks 0EGZ "reduced Ext system used by the weak comparison"]
#check (extReductionSystem I M N i : IadicFiniteModuleSystem A I)

@[stacks 0EGZ "bounded representative of the Ext comparison"]
#check (existsComparisonRepresentative I M N i :
  ∃ f : HomRepresentative (extQuotientSystem I M N i) (extReductionSystem I M N i),
    HomRepresentative.HasUniformTorsionBound f)

end

/- The exact cross-index source and target modules. -/
#check @CrossIndex.source
#check @CrossIndex.target
@[stacks 0EGZ "cross-index denominator equals the ambient ideal-power part"]
#check @CrossIndex.denominator_map_subtype

/- Auxiliary source-facing package for an explicit family of maps and bounds on `m ≫ n ≫ 0`; the
quotient-category representative above is the canonical reusable owner. -/
#check @existsCrossIndexComparison
#check @CrossIndexComparison
#check @CrossIndexComparison.map
#check @CrossIndexComparison.ofMaps

/- The reusable predicate records the common annihilator of every admissible kernel and cokernel. -/
#check @CrossIndexComparison.HasUniformTorsionBound

/- The object-level comparison from Lemma 15.101.8 remains available independently. -/
#check @extQuotientSystem_isomorphic_extReductionSystem
