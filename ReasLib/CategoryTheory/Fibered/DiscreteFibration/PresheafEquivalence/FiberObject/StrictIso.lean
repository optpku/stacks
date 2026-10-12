/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Fibered.BasedCategory.Basic
public import ReasLib.CategoryTheory.Fibered.DiscreteFibration.PresheafEquivalence.FiberObject.Evaluation

/-!
# Strict reconstruction from fiber objects

This leaf packages evaluation and the tautological functor as strict categorical and based
isomorphisms. Their computational data live in `FiberObject.Evaluation`.
-/

@[expose] public section

universe u v uS vS

namespace CategoryTheory

variable {C : Type u} [Category.{v} C]

namespace Functor

variable {S : Type uS} [Category.{vS} S]

/-- A discrete fibration is strictly isomorphic to the opposite category of elements of its
fiber-object presheaf. The forward and inverse functors are the explicit evaluation and
tautological constructions. -/
@[stacks 02Y2 "fiber-object strict category isomorphism",
  stacks 04SI "fiber-object strict category isomorphism"]
noncomputable def fiberObjectPresheaf.isoCat
    (p : S ⥤ C) [Functor.IsDiscreteFibration p] :
    IsoCat p.fiberObjectPresheaf.Elementsᵒᵖ S where
  functor := fiberObjectPresheaf.evaluation p
  inverse := fiberObjectPresheaf.unit p
  unit_eq := (fiberObjectPresheaf.evaluation.comp_unit p).symm
  counit_eq := fiberObjectPresheaf.unit.comp_evaluation p

/- Axiom audit: both functors have explicit object and morphism data. `sorryAx` is confined to
their category-of-elements membership proofs, functor laws, and the two strict inverse equations. -/

/-- The forward functor of `fiberObjectPresheaf.isoCat` is evaluation. -/
@[simp]
theorem fiberObjectPresheaf.isoCat.functor
    (p : S ⥤ C) [Functor.IsDiscreteFibration p] :
    (fiberObjectPresheaf.isoCat p).functor =
      fiberObjectPresheaf.evaluation p := sorry

/-- The inverse functor of `fiberObjectPresheaf.isoCat` is the tautological construction. -/
@[simp]
theorem fiberObjectPresheaf.isoCat.inverse
    (p : S ⥤ C) [Functor.IsDiscreteFibration p] :
    (fiberObjectPresheaf.isoCat p).inverse =
      fiberObjectPresheaf.unit p := sorry

/-- The strict isomorphism over `C` between a discrete fibration and the category-of-elements
projection of its fiber-object presheaf. This packages `fiberObjectPresheaf.isoCat` together with
the projection computation needed by based-category consumers. -/
@[stacks 02Y2 "fiber-object strict based isomorphism",
  stacks 04SI "fiber-object strict based isomorphism"]
noncomputable def fiberObjectPresheaf.basedStrictIso
    (p : S ⥤ C) [Functor.IsDiscreteFibration p] :
    BasedCategory.StrictIso
      (BasedCategory.ofFunctor
        (CategoryOfElements.π p.fiberObjectPresheaf).leftOp)
      (BasedCategory.ofFunctor p) where
  toIsoCat := fiberObjectPresheaf.isoCat p
  functor_w := fiberObjectPresheaf.evaluation.comp_projection p

/- Axiom audit: its forward and inverse functors are the explicit evaluation and tautological
functors; deferred dependencies occur only in proof-valued laws and projection compatibility. -/

/-- The total functor underlying the forward based morphism of
`fiberObjectPresheaf.basedStrictIso` is evaluation. -/
@[simp]
theorem fiberObjectPresheaf.basedStrictIso.hom.toFunctor
    (p : S ⥤ C) [Functor.IsDiscreteFibration p] :
    (fiberObjectPresheaf.basedStrictIso p).hom.toFunctor =
      fiberObjectPresheaf.evaluation p := sorry

/-- The total functor underlying the inverse based morphism of
`fiberObjectPresheaf.basedStrictIso` is the tautological construction. -/
@[simp]
theorem fiberObjectPresheaf.basedStrictIso.inv.toFunctor
    (p : S ⥤ C) [Functor.IsDiscreteFibration p] :
    (fiberObjectPresheaf.basedStrictIso p).inv.toFunctor =
      fiberObjectPresheaf.unit p := sorry

end Functor

end CategoryTheory
