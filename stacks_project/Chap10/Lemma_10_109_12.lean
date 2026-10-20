/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.GlobalDimension.FiniteModule
import StacksCheckRecall

/-!
# Testing Global Dimension on Finite and Cyclic Modules

@stack 065T
-/

@[expose] public section

open CategoryTheory

universe u

variable {R : Type u} [CommRing R]

/- Lemma 10.109.12 (Stacks `065T`): a global-dimension bound is equivalent to the same bound on
all finite modules and to the same bound on all cyclic modules `R ⧸ I`. -/
@[stacks 065T]
#check (HasGlobalDimensionLE.tfae_finite_idealQuotients (R := R) :
  ∀ n : ℕ,
    List.TFAE
      [ HasGlobalDimensionLE R n,
        ∀ (M : ModuleCat.{u} R) [Module.Finite R M], HasProjectiveDimensionLE M n,
        ∀ I : Ideal R, HasProjectiveDimensionLE (ModuleCat.of R (R ⧸ I)) n ])

/- The two atomic characterizations and the constructor from cyclic modules are the reusable
owner API behind the source-facing TFAE. -/
@[stacks 065T "finite-module characterization"]
#check @HasGlobalDimensionLE.iff_finiteModules
@[stacks 065T "ideal-quotient characterization"]
#check @HasGlobalDimensionLE.iff_idealQuotients
@[stacks 065T "cyclic-module constructor"]
#check @HasGlobalDimensionLE.of_idealQuotients
