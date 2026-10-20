/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.Flatness.LocallyFree
import StacksCheckRecall

@[expose] public section

/-!
# Definition 111.22.1

@stack 027R

This exercise entry is a source-facing recall of `Module.FiniteLocallyFree` and of invertible
modules as finite locally free of rank 1.
-/

universe u v

section

variable (R : Type u) (M : Type v) [CommRing R] [AddCommGroup M] [Module R M]

/- Definition 111.22.1 (1): a finite locally free `R`-module is one for which every prime
admits some `f` outside it such that `M_f` is a finite free `R_f`-module. Equivalently,
a standard-open cover trivializes the localizations as finite free modules. -/
@[stacks 027R] #check (Module.FiniteLocallyFree R M : Prop)

/- Definition 111.22.1 (2): an invertible module is a finite locally free module of rank 1,
i.e. for every prime there is some `f` outside it such that `M_f` is linearly equivalent
to `R_f`. Functions indexed by `Fin 1` identify canonically with the localized ring. -/
@[stacks 027R] #check (Module.FiniteLocallyFreeOfRank R M 1 : Prop)

end
