/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.FormalDeformation.FormalObject.MinimalVersal
import StacksCheckRecall

/-!
# Minimal versal formal objects and orbit-bijective differentials

A predeformation category satisfying Schlessinger's condition (S2) and possessing
a versal formal object has a minimal versal formal object whose differential is
bijective on `Derivation Λ k k`-orbits.
-/

@[expose] public section

open CategoryTheory

universe u

variable {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]
variable {F : Type (u + 1)} [Category.{u + 1} F]
variable {p : F ⥤ ArtinianLocalAlgCat Λ k}

/- Lemma 90.15.4: if `p` is a predeformation category satisfying `HasSchlessingerS2`
and `ξ` is a minimal versal formal object of `p`, then
`FormalObject.BijectiveDifferentialOnOrbits ξ` holds. -/
@[stacks 06T8]
#check (FormalObject.bijectiveDifferentialOnOrbits_of_isMinimalVersal :
  ∀ [Functor.IsPredeformationCategory p] [Functor.HasSchlessingerS2 p]
    (ξ : FormalObject p) [FormalObject.IsMinimalVersal ξ],
    FormalObject.BijectiveDifferentialOnOrbits ξ)
