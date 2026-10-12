/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.CategoryTheory.Yoneda
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Extension.Conditions
public import stacks_project.Chap98.Lemma_98_25_2_Noetherian
import Mathlib.Tactic.CrossRefAttribute

/-!
# Limit preserving functors of points on the Noetherian site

If the functor of points of a locally Noetherian scheme over a locally
Noetherian base preserves directed affine limits on `(Noetherian/S)`, then
the structure morphism is locally of finite presentation.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Over

/-- Lemma 98.25.3: if `X` is an object of `(Noetherian/S)_τ` and the functor of
points `h_X`, packaged as `(locallyNoetherian S).ι.op ⋙ yoneda.obj (Over.mk f)`,
is limit preserving, then `f : X ⟶ S` is locally of finite presentation. The
topology `τ` does not enter: the underlying category of `(Noetherian/S)_τ` is
independent of `τ`. The assumption that `S` is locally Noetherian is from the
section. -/
@[stacks 0GE4]
theorem locallyFinitePresentation_of_noetherianDirectedAffineLimits
    {X S : Scheme.{u}} [IsLocallyNoetherian S] [IsLocallyNoetherian X]
    (f : X ⟶ S)
    (hF : Extension.PreservesDirectedAffineLimits (locallyNoetherian S)
      ((locallyNoetherian S).ι.op ⋙ yoneda.obj (Over.mk f))) :
    LocallyOfFinitePresentation f := sorry

end AlgebraicGeometry.Scheme.Over
