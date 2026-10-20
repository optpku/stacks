/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Homology.DerivedCategory.Morita.Center
import StacksCheckRecall

@[expose] public section

noncomputable section

open CategoryTheory
open scoped ModuleCat.Algebra

universe u

variable {R : Type u} [CommRing R]
variable {A B : Type u} [Ring A] [Ring B] [Algebra R A] [Algebra R B]
variable (e : RLinear.TriangulatedEquivalence R
  (DerivedCategory (ModuleCat Aᵐᵒᵖ)) (DerivedCategory (ModuleCat Bᵐᵒᵖ)))

/- Remark 22.37.9 (09SD) (1): an `R`-linear triangulated equivalence `D(A) ≌ D(B)` preserves
the centers of the two `R`-algebras. -/
@[stacks 09SD] #check
  (DerivedCategory.Morita.nonempty_centerAlgEquiv e :
    Nonempty (Subalgebra.center R A ≃ₐ[R] Subalgebra.center R B))

/- Remark 22.37.9 (09SD) (2): in particular, derived-equivalent commutative `R`-algebras are
equivalent as `R`-algebras. -/
section Commutative

variable {A B : Type u} [CommRing A] [CommRing B] [Algebra R A] [Algebra R B]
variable (e : RLinear.TriangulatedEquivalence R
  (DerivedCategory (ModuleCat Aᵐᵒᵖ)) (DerivedCategory (ModuleCat Bᵐᵒᵖ)))

@[stacks 09SD]
#check (DerivedCategory.Morita.nonempty_algEquiv (R := R) (A := A) (B := B) e :
  Nonempty (A ≃ₐ[R] B))

end Commutative
