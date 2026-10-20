/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Homology.CochainComplex.FunctorialApproximation.AcyclicKilling
import StacksCheckRecall

@[expose] public section

/-!
# Acyclic-killing functorial approximations

The reusable owner for Lemma 19.12.4 is
`CochainComplex.FunctorialAcyclicKilling`. It packages the functor, comparison map,
monomorphism and quasi-isomorphism conditions, and the null-homotopy specification.
-/

open CategoryTheory

universe w v u

namespace CochainComplex

variable {C : Type u} [Category.{v} C] [Abelian C] [IsGrothendieckAbelian.{w} C]
variable {I : Type w}

/- Lemma 19.12.4: a family of acyclic complexes in a Grothendieck abelian category has a
functorial monomorphic quasi-isomorphic enlargement that kills maps from the family up to
homotopy. -/
@[stacks 079M] #check
  fun (K : I → CochainComplex C ℤ) (hK : ∀ i, (K i).Acyclic) ↦
    (FunctorialAcyclicKilling.nonempty K hK : Nonempty (FunctorialAcyclicKilling K))

/- The source-facing existential view is also reusable without importing this chapter. -/
#check @FunctorialAcyclicKilling.exists_approximation

end CochainComplex
