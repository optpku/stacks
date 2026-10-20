/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Fibered.PseudoPullback.Cartesian
public import ReasLib.CategoryTheory.Fibered.CategoryOver.Fiber
import Mathlib.Tactic.CrossRefAttribute

/-!
# Explicit pseudo-pullbacks as fibred categories

This application leaf bundles the generic cartesian pseudo-pullback construction in
`FiberedCategoryOver`. Keeping it separate prevents the generic cartesian API from depending on
the application-facing bicategory of fibred categories.
-/

@[expose] public section

universe u v uX vX uY vY uS vS w vT

namespace CategoryTheory

open scoped Bicategory BasedFunctor

variable {C : Type u} [Category.{v} C]

namespace BasedCategory.PseudoPullback

variable {X : BasedCategory.{vX, uX} C} {Y : BasedCategory.{vY, uY} C}
variable {S : BasedCategory.{vS, uS} C}

/-- Bundle the pseudo-pullback of cartesian based functors with fibred domains as a fibred
category over the common base. The common target need not itself be fibred. -/
@[stacks 0040 "explicit pseudo-pullback as a fibred category"]
def fibered
    [X.p.IsFibered] [Y.p.IsFibered]
    (F : CartesianBasedFunctor X.p S.p) (G : CartesianBasedFunctor Y.p S.p) :
    FiberedCategoryOver C :=
  ⟨PseudoPullback F.toBasedFunctor G.toBasedFunctor, projectionIsFibered F G⟩

/-- The based category underlying the bundled fibred pseudo-pullback is the explicit
pseudo-pullback owner. -/
@[simp]
theorem fibered.toBasedCategory
    [X.p.IsFibered] [Y.p.IsFibered]
    (F : CartesianBasedFunctor X.p S.p) (G : CartesianBasedFunctor Y.p S.p) :
    (fibered F G).toBasedCategory =
      PseudoPullback F.toBasedFunctor G.toBasedFunctor := sorry

/-- The projection of the bundled fibred pseudo-pullback is the explicit pseudo-pullback
projection. -/
@[simp]
theorem fibered.p
    [X.p.IsFibered] [Y.p.IsFibered]
    (F : CartesianBasedFunctor X.p S.p) (G : CartesianBasedFunctor Y.p S.p) :
    (fibered F G).p =
      (PseudoPullback F.toBasedFunctor G.toBasedFunctor).p := sorry

/-- Explicit cleavages on the two source projections exhibit the pseudo-pullback projection as
fibred, without requiring ambient fibredness instances. -/
theorem fibered.ofCleavage.isFibered
    (F : CartesianBasedFunctor X.p S.p) (G : CartesianBasedFunctor Y.p S.p)
    (χX : X.p.Cleavage) (χY : Y.p.Cleavage) :
    (PseudoPullback F.toBasedFunctor G.toBasedFunctor).p.IsFibered := sorry

/-- Bundle the pseudo-pullback as a fibred category from explicit cleavages on its two source
projections. -/
@[stacks 0040 "explicit pseudo-pullback fibred category from source cleavages"]
def fibered.ofCleavage
    (F : CartesianBasedFunctor X.p S.p) (G : CartesianBasedFunctor Y.p S.p)
    (χX : X.p.Cleavage) (χY : Y.p.Cleavage) : FiberedCategoryOver C :=
  ⟨PseudoPullback F.toBasedFunctor G.toBasedFunctor,
    fibered.ofCleavage.isFibered F G χX χY⟩

/-- The based category underlying the explicit-cleavage fibred pseudo-pullback is the concrete
pseudo-pullback owner. -/
@[simp]
theorem fibered.ofCleavage.toBasedCategory
    (F : CartesianBasedFunctor X.p S.p) (G : CartesianBasedFunctor Y.p S.p)
    (χX : X.p.Cleavage) (χY : Y.p.Cleavage) :
    (fibered.ofCleavage F G χX χY).toBasedCategory =
      PseudoPullback F.toBasedFunctor G.toBasedFunctor := sorry

/-- The projection of the explicit-cleavage fibred pseudo-pullback is the concrete
pseudo-pullback projection. -/
@[simp]
theorem fibered.ofCleavage.p
    (F : CartesianBasedFunctor X.p S.p) (G : CartesianBasedFunctor Y.p S.p)
    (χX : X.p.Cleavage) (χY : Y.p.Cleavage) :
    (fibered.ofCleavage F G χX χY).p =
      (PseudoPullback F.toBasedFunctor G.toBasedFunctor).p := sorry

/-- Any explicit-cleavage fibred pseudo-pullback agrees with the instance-driven owner; the
cleavages affect only the proof that its projection is fibred. -/
@[simp]
theorem fibered.ofCleavage.eq
    [X.p.IsFibered] [Y.p.IsFibered]
    (F : CartesianBasedFunctor X.p S.p) (G : CartesianBasedFunctor Y.p S.p)
    (χX : X.p.Cleavage) (χY : Y.p.Cleavage) :
    fibered.ofCleavage F G χX χY =
      fibered F G := sorry

end BasedCategory.PseudoPullback

namespace FiberedCategoryOver

variable {X Y S : FiberedCategoryOver.{u, v, w, vT} C}

/-- The explicit pseudo-pullback of two morphisms of fibred categories has a fibred projection.

This bridge retains the bundled morphisms in its instance head, so chosen-cleavage constructions
can synthesize fibredness without unfolding their cartesian based-functor presentations. -/
instance pseudoPullbackIsFibered
    (F : X ⟶ S) (G : Y ⟶ S) :
    (BasedCategory.PseudoPullback
      (toBasedFunctor F) (toBasedFunctor G)).p.IsFibered := sorry

end FiberedCategoryOver

end CategoryTheory
