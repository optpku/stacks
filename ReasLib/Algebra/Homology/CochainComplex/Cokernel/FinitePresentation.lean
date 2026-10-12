/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Category.ModuleCat.FinitePresentation.Cokernel
public import ReasLib.Algebra.Homology.CochainComplex.Cokernel
public import ReasLib.Algebra.Homology.CochainComplex.Cokernel.Opcycles
public import ReasLib.Algebra.Homology.HomologicalComplex.Termwise.FinitePresentation
import Mathlib.Tactic.CrossRefAttribute

/-!
# Finite presentation of differential cokernels

Termwise finite presentation is the weakest degreewise complex hypothesis needed here.  More
structured models, such as finite-projective or finite-free complexes, should enter through their
shape-generic bridges to this predicate.
@stack 0E1U
@stack 0G8Y
-/

@[expose] public section

open CategoryTheory

universe u

namespace CochainComplex.IsTermwiseFinitePresentation

variable {R : Type u} [Ring R]
variable {K : CochainComplex (ModuleCat R) ℤ}

/-- Stacks `0E1U`: the cokernel of every incoming differential of a termwise finitely presented complex is
finitely presented. -/
@[stacks 0G8Y "finite-presentation differential cokernels"]
theorem differentialCokernel
    (hK : K.IsTermwiseFinitePresentation) (n : ℤ) :
    Module.FinitePresentation R (K.differentialCokernel n) := sorry
/- Proof strategy: apply `ModuleCat.isFinitePresentation.cokernel_of_isFG` to the incoming
differential.  The two adjacent terms are finitely presented by `hK`, hence the source is finitely
generated and the target is finitely presented. -/

/-- Stacks `0E1U`: the canonical opcycles object of a termwise finitely presented complex is finitely presented. -/
@[stacks 0E1U "finite-presentation opcycles bridge"]
theorem opcycles
    (hK : K.IsTermwiseFinitePresentation) (n : ℤ) :
    Module.FinitePresentation R (K.opcycles n) := sorry
/- Proof strategy: transport `differentialCokernel` across `K.opcyclesIsoCokernel n`. -/

end CochainComplex.IsTermwiseFinitePresentation
