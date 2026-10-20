/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 10.14.3

@stack 05DQ
-/

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] (f : R →+* S)

/- Lemma 10.14.3: for a ring map `f : R →+* S`, extension of scalars
`ModuleCat.extendScalars f : ModuleCat R ⥤ ModuleCat S` is left adjoint to restriction of scalars
`ModuleCat.restrictScalars f : ModuleCat S ⥤ ModuleCat R`. This is the canonical tensor-Hom
adjunction for modules. -/
@[stacks 05DQ "extension-restriction adjunction"]
#check @ModuleCat.extendRestrictScalarsAdj

/- Companion recall: the owner-object form of the tensor-Hom adjunction is the canonical
equivalence
`Hom_S(S ⊗[R] M, N) ≃ Hom_R(M, N|_R)`,
implemented by `(ModuleCat.extendRestrictScalarsAdj f).homEquiv`. The textbook orientation
`Hom_S(M ⊗[R] S, N) ≃ Hom_R(M, N|_R)` is obtained by tensor symmetry. -/
@[stacks 05DQ "tensor-Hom equivalence"]
#check (ModuleCat.extendRestrictScalarsAdj f).homEquiv
