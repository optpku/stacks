/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.FormalDeformation.FormalObject.MinimalVersal
import StacksCheckRecall

/-!
# Versal formal objects satisfying 90.15.0.2

A versal formal object of a predeformation category whose differential is
bijective on `Derivation Λ k k`-orbits is minimal versal, hence unique up to
isomorphism.
-/

@[expose] public section

open CategoryTheory

universe u

variable {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]
variable {F : Type (u + 1)} [Category.{u + 1} F]
variable {p : F ⥤ ArtinianLocalAlgCat Λ k}

/- Lemma 90.15.1 (1): if `p` is a predeformation category and `ξ` is a versal
formal object of `p` such that `BijectiveDifferentialOnOrbits ξ` holds, then `ξ`
is a minimal versal formal object. -/
@[stacks 06IR]
#check (FormalObject.isMinimalVersal_of_bijectiveDifferentialOnOrbits :
  ∀ [Functor.IsPredeformationCategory p] (ξ : FormalObject p) [FormalObject.IsVersal ξ],
    FormalObject.BijectiveDifferentialOnOrbits ξ → FormalObject.IsMinimalVersal ξ)

/- Lemma 90.15.1 (2): if `p` is a predeformation category, then any two versal
formal objects of `p` satisfying `BijectiveDifferentialOnOrbits` are isomorphic. -/
@[stacks 06IR]
#check (FormalObject.nonempty_iso_of_bijectiveDifferentialOnOrbits :
  ∀ [Functor.IsPredeformationCategory p] (ξ η : FormalObject p)
    [FormalObject.IsVersal ξ] [FormalObject.IsVersal η],
    FormalObject.BijectiveDifferentialOnOrbits ξ →
      FormalObject.BijectiveDifferentialOnOrbits η → Nonempty (ξ ≅ η))
