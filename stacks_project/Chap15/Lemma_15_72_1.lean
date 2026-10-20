/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Homology.CochainComplex.Monoidal.Closed.ModuleCat.Source
import StacksCheckRecall

/-!
# Currying for module-valued Hom complexes

The reusable owner is `CategoryTheory.CochainComplex.InternalHom.Module.tensorIso`.

@stack 0A5Y
-/

@[expose] public section

/- Lemma 15.72.1: currying identifies the iterated Hom complex
`Hom^•(K, Hom^•(L, M))` with `Hom^•(K ⊗ L, M)`. -/
@[stacks 0A5Y "currying isomorphism of module-valued Hom complexes"]
#check @CategoryTheory.CochainComplex.InternalHom.Module.tensorIso

#check @CochainComplex.HomComplex.moduleComplex
#check @CochainComplex.HomComplex.degreeIso
#check @CochainComplex.HomComplex.proj
#check @CategoryTheory.CochainComplex.InternalHom.Module.tensorIso_natural_left
#check @CategoryTheory.CochainComplex.InternalHom.Module.tensorIso_natural_middle
#check @CategoryTheory.CochainComplex.InternalHom.Module.tensorIso_natural_right

#print axioms CategoryTheory.CochainComplex.InternalHom.Module.tensorIso
