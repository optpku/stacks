/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Category.CommRingCat.Under.ModuleValuedFunctor.Restriction
import StacksCheckRecall

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u v

/- Remark 46.3.4 (1): `FinitelyPresentedAlgebra A` is the category
`Alg_{fp,A}` of finitely presented commutative `A`-algebras. -/
@[stacks 06UV] #check
  (FinitelyPresentedAlgebra : CommRingCat.{u} → Type (u + 1))

/- Remark 46.3.4 (2): every commutative `R`-algebra `A` is a filtered colimit of
finitely presented commutative `R`-algebras. -/
@[stacks 06UV] #check
  (CommAlgCat.Over.FinitePresentation.isFilteredColimit :
    ∀ (R : Type u) [CommRing R] (A : Type v) [CommRing A] [Algebra R A],
      IsFiltered (CommAlgCat.Over.FinitePresentation.category R A) ∧
        Nonempty (IsColimit (CommAlgCat.Over.FinitePresentation.cocone R A)))

/- Remark 46.3.4 (3): a tensor-adequate module-valued functor is determined, on
objects and morphisms, by its restriction to `FinitelyPresentedAlgebra A`. -/
@[stacks 06UV] #check
  (ModuleValuedFunctor.restrictionFullyFaithful :
    ∀ A : CommRingCat.{u}, Nonempty (ModuleValuedFunctor.restriction A).FullyFaithful)

/- Remark 46.3.4 (4): `ModuleValuedFunctor.TensorAdeq` is the canonical
algebra-based, site-independent presentation of the category of adequate functors. -/
@[stacks 06UV] #check
  (ModuleValuedFunctor.TensorAdeq : CommRingCat.{u} → Type (u + 1))
