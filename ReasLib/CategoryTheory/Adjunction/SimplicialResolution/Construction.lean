module

public import ReasLib.AlgebraicTopology.SimplicialObject.Augmented.Composition.Pointwise
public import ReasLib.AlgebraicTopology.SimplicialObject.Augmented.Composition.Whiskering
public import ReasLib.CategoryTheory.Endofunctor.ComonadResolution.Evaluation
public import Mathlib.CategoryTheory.Monad.Adjunction

/-!
@stack 08ND

# Constructing simplicial resolutions from adjunctions

An adjunction determines a comonad and hence a canonical augmented simplicial resolution.
This leaf owns the resolution, its face and degeneracy formulas, the two functor-level
compositions, and their uncontracted pointwise evaluations.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Functor
open CategoryTheory.SimplicialObject
open Opposite
open scoped CategoryTheory.IteratedEndofunctor Simplicial

universe uA uS vA vS

namespace CategoryTheory.Adjunction.SimplicialResolution

variable {A : Type uA} {S : Type uS} [Category.{vA} A] [Category.{vS} S]
variable {U : S ⥤ A} {V : A ⥤ S}

/-- In degree `n`, the adjunction resolution is the positive `(n + 1)`-fold iterate of the
comonad endofunctor `V ⋙ U`. -/
@[simp, stacks 08NC "degree of the simplicial resolution of an adjunction"]
theorem obj (adj : U ⊣ V) (n : ℕ) :
    adj.toComonad.simplicialResolution.obj (op ⦋n⦌) = (V ⋙ U) ⁺⦋n⦌ := sorry

/-- The faces of the adjunction resolution insert the adjunction counit. -/
@[simp, stacks 08NC "faces of the simplicial resolution of an adjunction"]
theorem face (adj : U ⊣ V) {n : ℕ} (i : Fin (n + 2)) :
    adj.toComonad.simplicialResolution.δ i =
      IteratedEndofunctor.face adj.counit n i := sorry

/-- The degeneracies of the adjunction resolution insert the comultiplication induced by the
adjunction unit. -/
@[simp, stacks 08NC "degeneracies of the simplicial resolution of an adjunction"]
theorem degeneracy (adj : U ⊣ V) {n : ℕ} (i : Fin (n + 1)) :
    adj.toComonad.simplicialResolution.σ i =
      IteratedEndofunctor.degeneracy
        (Functor.whiskerRight (Functor.whiskerLeft V adj.unit) U) n i := sorry

/-- The degree-zero component of the adjunction-resolution augmentation is the adjunction
counit. -/
@[simp, stacks 08NC "augmentation of the simplicial resolution of an adjunction"]
theorem augmentation.app_zero (adj : U ⊣ V) :
    (Comonad.simplicialResolution.augmentation adj.toComonad).app (op ⦋0⦌) =
      adj.counit := sorry

/-- The canonical adjunction resolution after postcomposing every degree with the right
adjoint.  Its augmentation target is `V`. -/
@[stacks 08ND "postcomposed adjunction resolution"]
noncomputable def postcompose (adj : U ⊣ V) :
    SimplicialObject.Augmented (A ⥤ S) :=
  SimplicialObject.Augmented.postcompose V
    (Comonad.simplicialResolution.augmentation adj.toComonad)

/-- The canonical adjunction resolution after precomposing every degree with the left adjoint.
Its augmentation target is `U`. -/
@[stacks 08ND "precomposed adjunction resolution"]
noncomputable def precompose (adj : U ⊣ V) :
    SimplicialObject.Augmented (S ⥤ A) :=
  SimplicialObject.Augmented.precompose U
    (Comonad.simplicialResolution.augmentation adj.toComonad)

/-- The canonical adjunction resolution, evaluated functorially in the resolved object. -/
@[stacks 08NC "evaluated simplicial resolution of an adjunction"]
noncomputable def eval (adj : U ⊣ V) :
    A ⥤ SimplicialObject.Augmented A :=
  Comonad.simplicialResolution.eval adj.toComonad

/-- The postcomposed adjunction resolution, evaluated functorially in the resolved object. -/
@[stacks 08ND "pointwise postcomposed adjunction resolution"]
noncomputable def postcompose.eval (adj : U ⊣ V) :
    A ⥤ SimplicialObject.Augmented S :=
  SimplicialObject.Augmented.pointwise (postcompose adj)

/-- Pointwise postcomposition is the evaluated adjunction resolution followed by the right
adjoint degreewise. -/
@[stacks 08ND "postcomposed evaluation as degreewise right-adjoint image"]
theorem postcompose.eval_eq (adj : U ⊣ V) :
    postcompose.eval adj =
      CategoryTheory.Adjunction.SimplicialResolution.eval adj ⋙
        SimplicialObject.Augmented.whiskeringObj A S V := sorry

/-- The precomposed adjunction resolution, evaluated functorially in the input of the left
adjoint. -/
@[stacks 08ND "pointwise precomposed adjunction resolution"]
noncomputable def precompose.eval (adj : U ⊣ V) :
    S ⥤ SimplicialObject.Augmented A :=
  SimplicialObject.Augmented.pointwise (precompose adj)

/-- Pointwise precomposition evaluates the adjunction resolution at the image under the left
adjoint. -/
@[stacks 08ND "precomposed evaluation as evaluation after the left adjoint"]
theorem precompose.eval_eq (adj : U ⊣ V) :
    precompose.eval adj =
      U ⋙ CategoryTheory.Adjunction.SimplicialResolution.eval adj := sorry

end CategoryTheory.Adjunction.SimplicialResolution
