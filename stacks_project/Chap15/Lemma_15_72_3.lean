/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Homology.CochainComplex.Monoidal.Closed.ModuleCat.Composition
import StacksCheckRecall

/-!
# Composition of Hom complexes

The source-order composition map is owned generically by
`CategoryTheory.MonoidalClosed.Source.comp`. Its module-valued Hom-complex specialization is
transported once in `CategoryTheory.CochainComplex.InternalHom.Module.comp`.

@stack 0A8I
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory
open CategoryTheory.CochainComplex.InternalHom

variable {R : Type u} [CommRing R]
variable (K L M : CochainComplex (ModuleCat R) ℤ)

/- Lemma 15.72.3: the canonical source-order composition morphism is
`Hom^•(L, M) ⊗ Hom^•(K, L) ⟶ Hom^•(K, M)`. -/
@[stacks 0A8I "composition of module-valued Hom complexes"]
#check Module.comp (R := R) K L M

#check @CategoryTheory.MonoidalClosed.Source.comp
#check @CategoryTheory.CochainComplex.InternalHom.Module.Composition.component
#check @CategoryTheory.CochainComplex.InternalHom.Module.Composition.component_tmul_apply
