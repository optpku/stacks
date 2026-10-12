/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Homology.HomologicalComplexAbelian
public import ReasLib.Algebra.Homology.HomologicalComplex.MonoEpi
import StacksCheckRecall

@[expose] public section

open CategoryTheory CategoryTheory.Limits HomologicalComplex ComplexShape

universe v u

variable {A : Type u} [Category.{v} A] [Abelian A]
variable {K L : CochainComplex A ℤ} (f : K ⟶ L)
variable (S : ShortComplex (CochainComplex A ℤ))

/- Lemma 12.13.9 (1) [0114]: cochain complexes in an abelian category form an abelian
category. -/
@[stacks 0114]
#check (inferInstance : Abelian (CochainComplex A ℤ))

/- Lemma 12.13.9 (2) [0114]: monomorphisms of cochain complexes are detected degreewise. -/
@[stacks 0114]
#check (HomologicalComplex.mono_iff_mono_f f : Mono f ↔ ∀ i : ℤ, Mono (f.f i))

/- Lemma 12.13.9 (3) [0114]: epimorphisms of cochain complexes are detected degreewise. -/
@[stacks 0114]
#check (HomologicalComplex.epi_iff_epi_f f : Epi f ↔ ∀ i : ℤ, Epi (f.f i))

/- Lemma 12.13.9 (4) [0114]: exactness of cochain-complex rows is detected degreewise. -/
@[stacks 0114]
#check (HomologicalComplex.exact_iff_degreewise_exact S :
  S.Exact ↔ ∀ i : ℤ, (S.map (HomologicalComplex.eval A (up ℤ) i)).Exact)
