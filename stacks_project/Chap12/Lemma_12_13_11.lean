/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Homology.QuasiIso
import StacksCheckRecall

@[expose] public section

open CategoryTheory HomologicalComplex ComplexShape

universe v u

variable {A : Type u} [Category.{v} A] [Abelian A]
variable {K L : CochainComplex A ℤ} {f g : K ⟶ L}
variable (h : Homotopy f g) (i : ℤ)

/- Lemma 12.13.11 (1) [0116]: homotopic cochain maps induce the same map on cohomology. -/
@[stacks 0116]
#check (Homotopy.homologyMap_eq h i :
  HomologicalComplex.homologyMap f i = HomologicalComplex.homologyMap g i)

variable (k : K ⟶ L) (hk : HomologicalComplex.homotopyEquivalences A (up ℤ) k)

/- Lemma 12.13.11 (2) [0116]: a homotopy equivalence is a quasi-isomorphism. -/
@[stacks 0116]
#check ((HomologicalComplex.mem_quasiIso_iff k).1
  ((homotopyEquivalences_le_quasiIso A (up ℤ)) k hk) : QuasiIso k)
