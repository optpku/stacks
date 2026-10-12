/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
import ReasLib.AlgebraicGeometry.Scheme.Morphism.Unramified.FittingIdeal

open AlgebraicGeometry
open scoped AlgebraicGeometry

universe u

/- Lemma 31.10.2: For a locally finite type morphism of schemes, the closed subscheme cut out by
the zeroth Fitting ideal of its relative differentials has underlying set equal to the locus where
the morphism is not unramified. -/
@[stacks 0C3J] #check
  (AlgebraicGeometry.Scheme.Hom.fittingIdealSheaf_differentials_support_eq_nonUnramifiedAtLocus :
    ∀ {X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFiniteType f],
    ((Scheme.fittingIdealSheaf (Ω[f.toShHom]) 0).support : Set X) =
      {x : X | ¬ f.UnramifiedAt x})
