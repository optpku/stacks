/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Homology.DerivedCategory.Completeness.Cech
import StacksCheckRecall

/-!
# Derived completion from an extended alternating Cech complex

@stack 091V

The reusable owner exposes the source's concrete Cech internal-Hom functor and its functorial
unit.  The general reflector API remains the canonical owner for the existence of derived
completion independently of a chosen finite generating family.
-/

@[expose] public section

/- Lemma 15.92.10 (091V) (1): for a finitely generated ideal, the inclusion of derived-complete
objects into `D(A)` has a left adjoint with a universal map. -/
@[stacks 091V "derived-completion reflector existence"]
#check @DerivedCategory.DerivedCompletion.existsReflector

@[stacks 091V "derived-completion reflector specification"]
#check @DerivedCategory.DerivedCompletion.chosenReflector_spec

@[stacks 091V "derived-completion universal map"]
#check @DerivedCategory.toDerivedCompletion

@[stacks 091V "derived-completion universal factorization"]
#check @DerivedCategory.DerivedCompletion.toDerivedCompletion_comp_lift

/- Lemma 15.92.10 (091V) (2): for generators `f`, the completion functor is explicitly
`K ↦ RHom_A(Cech(f), K)`, with its unit induced by `Cech(f) ⟶ A[0]`. -/
@[stacks 091V "Cech derived-completion functor"]
#check @DerivedCategory.CechCompletion.functor

@[stacks 091V "Cech derived-completion unit"]
#check @DerivedCategory.CechCompletion.unit

/- Lemma 15.92.10 (091V) (3): the explicit Cech completion is derived complete and its unit
induces the required Hom bijection for every derived-complete target. -/
@[stacks 091V "Cech completion is derived complete"]
#check @DerivedCategory.CechCompletion.obj_isDerivedComplete

@[stacks 091V "Cech completion universal Hom bijection"]
#check @DerivedCategory.CechCompletion.unit_bijective
