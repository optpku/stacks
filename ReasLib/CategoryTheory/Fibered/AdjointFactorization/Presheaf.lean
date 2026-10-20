module

public import ReasLib.CategoryTheory.Fibered.AdjointFactorization.Fiber
public import ReasLib.CategoryTheory.Fibered.Presheaf
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import Mathlib.Tactic.CrossRefAttribute

/-!
# Presheaves on an adjoint factorization

The source endpoint of the adjoint factorization acts on coefficient presheaves by
precomposition.  This construction is independent of the coefficient category and of any
subsequent fiberwise homology theory.
-/

@[expose] public section

open CategoryTheory

universe u v w a b

namespace CategoryTheory.FiberedCategoryOver.AdjointFactorization

variable {B : Type u} [Category.{v} B]
variable {X Y : FiberedCategoryOver.{u, v, w, w} B}
variable {A : Type a} [Category.{b} A]

/-- Pullback along the source endpoint of an adjoint factorization, functorially in the
coefficient presheaf. -/
@[stacks 08PK "comparison-index coefficient pullback functor"]
def sourcePullbackFunctor (g : X ⟶ Y) :
    (X.totalᵒᵖ ⥤ A) ⥤ ((overTarget g).totalᵒᵖ ⥤ A) :=
  (Functor.whiskeringLeft _ _ A).obj (source g).op

/-- Evaluation of source-endpoint pullback on a coefficient presheaf. -/
@[simp, stacks 08PK "comparison-index coefficient pullback object formula"]
theorem sourcePullbackFunctor_obj (g : X ⟶ Y) (F : X.totalᵒᵖ ⥤ A) :
    (sourcePullbackFunctor g).obj F = sourcePullback g F := sorry

/-- Source-endpoint pullback acts on coefficient morphisms by whiskering. -/
@[simp, stacks 08PK "comparison-index coefficient pullback map formula"]
theorem sourcePullbackFunctor_map (g : X ⟶ Y)
    {F G : X.totalᵒᵖ ⥤ A} (t : F ⟶ G) :
    (sourcePullbackFunctor g).map t = Functor.whiskerLeft (source g).op t := sorry

/-- Precomposition along the source endpoint is additive for preadditive coefficients. -/
@[stacks 08PK "additivity of comparison-index coefficient pullback"]
instance sourcePullbackFunctor.additive [Preadditive A] (g : X ⟶ Y) :
    (sourcePullbackFunctor g : (X.totalᵒᵖ ⥤ A) ⥤ _).Additive := sorry

/-- Restricting source-pulled coefficients to a target fiber is the canonical fiber-source
pullback. -/
@[simp, stacks 08PK "comparison-index coefficient restriction formula"]
theorem restrict_sourcePullback (g : X ⟶ Y)
    (F : X.totalᵒᵖ ⥤ A) (y : Y.total) :
    Presheaf.restrict (overTarget g) A (sourcePullback g F) y =
      fiberSourcePullback g F y := sorry

end CategoryTheory.FiberedCategoryOver.AdjointFactorization
