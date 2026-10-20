/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Homology.CochainDGAlgebra.Hom
import StacksCheckRecall

universe u v

variable {R : Type u} [CommRing R]

section Chain

variable (A B : ChainDGAlgebra.{u, v} R)

/- Definition 22.3.2 (1) (061X): morphisms of chain differential graded algebras are
canonically represented by `ChainDGAlgebra.Hom`. -/
@[stacks 061X] #check (ChainDGAlgebra.Hom A B : Type _)

end Chain

section Cochain

variable (A B : CochainDGAlgebra.{u, v} R)

/- Definition 22.3.2 (2) (061X): morphisms of cochain differential graded algebras are
canonically represented by `CochainDGAlgebra.Hom`. -/
@[stacks 061X] #check (CochainDGAlgebra.Hom A B : Type _)

end Cochain
