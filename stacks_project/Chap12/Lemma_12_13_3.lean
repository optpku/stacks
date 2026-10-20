/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Homology.HomologicalComplexAbelian
public import ReasLib.Algebra.Homology.HomologicalComplex.MonoEpi
import StacksCheckRecall

@[expose] public section

open CategoryTheory CategoryTheory.Limits HomologicalComplex ComplexShape

universe v u

variable {A : Type u} [Category.{v} A] [Abelian A]
variable {K L : ChainComplex A ℤ} (f : K ⟶ L)
variable (S : ShortComplex (ChainComplex A ℤ))

/- Lemma 12.13.3 (1) [010Y]: chain complexes in an abelian category form an abelian
category. -/
@[stacks 010Y]
#check (inferInstance : Abelian (ChainComplex A ℤ))

/- Lemma 12.13.3 (2) [010Y]: monomorphisms of chain complexes are detected degreewise. -/
@[stacks 010Y]
#check (HomologicalComplex.mono_iff_mono_f f : Mono f ↔ ∀ i : ℤ, Mono (f.f i))

/- Lemma 12.13.3 (3) [010Y]: epimorphisms of chain complexes are detected degreewise. -/
@[stacks 010Y]
#check (HomologicalComplex.epi_iff_epi_f f : Epi f ↔ ∀ i : ℤ, Epi (f.f i))

/- Lemma 12.13.3 (4) [010Y]: exactness of chain-complex rows is detected degreewise. -/
@[stacks 010Y]
#check (HomologicalComplex.exact_iff_degreewise_exact S :
  S.Exact ↔ ∀ i : ℤ, (S.map (HomologicalComplex.eval A (down ℤ) i)).Exact)
