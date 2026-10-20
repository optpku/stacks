/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicTopology.CosimplicialObject.Augmented.Composition.Whiskering
public import ReasLib.CategoryTheory.Endofunctor.MonadResolution.Evaluation
public import Mathlib.CategoryTheory.Monad.Adjunction

/-!
# Constructing cosimplicial resolutions from adjunctions

An adjunction determines a monad and hence a canonical augmented cosimplicial resolution. This
leaf owns its degree, coface, codegeneracy, and coaugmentation formulas, together with the two
functor-level compositions and their uncontracted pointwise evaluations.
-/

@[expose] public section

open CategoryTheory.Functor
open scoped CategoryTheory.IteratedEndofunctor Simplicial

universe uC uD vC vD

namespace CategoryTheory

namespace Adjunction.CosimplicialResolution

variable {C : Type uC} {D : Type uD} [Category.{vC} C] [Category.{vD} D]
variable {L : C ⥤ D} {R : D ⥤ C}

/-- In degree `n`, the adjunction resolution is the positive `(n + 1)`-fold iterate of the
monad endofunctor `L ⋙ R`. -/
@[simp, stacks 0FKS "degree of the cosimplicial resolution of an adjunction"]
theorem obj (adj : L ⊣ R) (n : ℕ) :
    adj.toMonad.cosimplicialResolution.obj ⦋n⦌ = (L ⋙ R) ⁺⦋n⦌ := sorry

/-- The cofaces of the adjunction resolution insert the adjunction unit. -/
@[simp, stacks 0FKS "cofaces of the cosimplicial resolution of an adjunction"]
theorem δ (adj : L ⊣ R) {n : ℕ} (i : Fin (n + 2)) :
    adj.toMonad.cosimplicialResolution.δ i =
      IteratedEndofunctor.coface adj.unit n i := sorry

/-- The codegeneracies of the adjunction resolution insert the multiplication induced by the
adjunction counit. -/
@[simp, stacks 0FKS "codegeneracies of the cosimplicial resolution of an adjunction"]
theorem σ (adj : L ⊣ R) {n : ℕ} (i : Fin (n + 1)) :
    adj.toMonad.cosimplicialResolution.σ i =
      IteratedEndofunctor.codegeneracy
        (Functor.whiskerRight (Functor.whiskerLeft L adj.counit) R) n i := sorry

/-- The degree-zero component of the adjunction-resolution coaugmentation is the adjunction
unit. -/
@[simp, stacks 0FKS "coaugmentation of the cosimplicial resolution of an adjunction"]
theorem coaugmentation.app_zero (adj : L ⊣ R) :
    (Monad.cosimplicialResolution.coaugmentation adj.toMonad).app ⦋0⦌ =
      adj.unit := sorry

/-- The canonical adjunction resolution, evaluated functorially in the resolved object. -/
@[stacks 0FKS "evaluated cosimplicial resolution of an adjunction"]
noncomputable def eval (adj : L ⊣ R) :
    C ⥤ CosimplicialObject.Augmented C :=
  Monad.cosimplicialResolution.eval adj.toMonad

/-- The canonical monad resolution after postcomposing every degree with the left adjoint. Its
coaugmentation point is `L`. -/
@[stacks 0FKS "left-adjoint image of the monad resolution"]
noncomputable def postcompose (adj : L ⊣ R) :
    CosimplicialObject.Augmented (C ⥤ D) :=
  CosimplicialObject.Augmented.postcompose L
    (Monad.cosimplicialResolution.coaugmentation adj.toMonad)

/-- The canonical monad resolution after precomposing every degree with the right adjoint. Its
coaugmentation point is `R`. -/
@[stacks 0FKS "right-adjoint precomposition of the monad resolution"]
noncomputable def precompose (adj : L ⊣ R) :
    CosimplicialObject.Augmented (D ⥤ C) :=
  CosimplicialObject.Augmented.precompose R
    (Monad.cosimplicialResolution.coaugmentation adj.toMonad)

/-- The postcomposed adjunction resolution, evaluated functorially in the resolved object. -/
@[stacks 0FKS "pointwise postcomposed adjunction resolution"]
noncomputable def postcompose.eval (adj : L ⊣ R) :
    C ⥤ CosimplicialObject.Augmented D :=
  CosimplicialObject.Augmented.pointwise (postcompose adj)

/-- Pointwise postcomposition is the evaluated adjunction resolution followed degreewise by the
left adjoint. -/
@[stacks 0FKS "postcomposed evaluation as degreewise left-adjoint image"]
theorem postcompose.eval_eq (adj : L ⊣ R) :
    postcompose.eval adj =
      CategoryTheory.Adjunction.CosimplicialResolution.eval adj ⋙
        CosimplicialObject.Augmented.whiskeringObj C D L := sorry

/-- The precomposed adjunction resolution, evaluated functorially in the input of the right
adjoint. -/
@[stacks 0FKS "pointwise precomposed adjunction resolution"]
noncomputable def precompose.eval (adj : L ⊣ R) :
    D ⥤ CosimplicialObject.Augmented C :=
  CosimplicialObject.Augmented.pointwise (precompose adj)

/-- Pointwise precomposition evaluates the adjunction resolution at the image under the right
adjoint. -/
@[stacks 0FKS "precomposed evaluation as evaluation after the right adjoint"]
theorem precompose.eval_eq (adj : L ⊣ R) :
    precompose.eval adj =
      R ⋙ CategoryTheory.Adjunction.CosimplicialResolution.eval adj := sorry

end Adjunction.CosimplicialResolution

end CategoryTheory
