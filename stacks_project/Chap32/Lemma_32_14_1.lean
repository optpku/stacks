/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import ReasLib.AlgebraicGeometry.Scheme.Limit.ClosedSubscheme
import StacksCheckRecall

open AlgebraicGeometry
open CategoryTheory CategoryTheory.Limits

universe u

/- Lemma 32.14.1: a closed subscheme over a quasi-compact base change that avoids the fiber
over a point descends, after restricting to an affine neighborhood, to a closed subscheme over
an affine scheme locally of finite presentation over the original base, while continuing to
avoid the corresponding fiber. -/
@[stacks 05BD] #check
  (AlgebraicGeometry.Scheme.Limit.ClosedSubscheme.existsAffineApproximationAvoidingFiber :
    ∀ {X S T : Scheme.{u}} (f : X ⟶ S) [QuasiCompact f] (g : T ⟶ S)
      (t : T) (Z : (pullback f g).IdealSheafData),
      Scheme.IdealSheafData.avoidsFiber (pullback.snd f g) Z t →
      ∃ (V : T.Opens) (hVt : t ∈ (V : Set T)) (_ : IsAffine V.toScheme)
        (T' : Scheme.{u}) (b : T' ⟶ S) (_ : LocallyOfFinitePresentation b)
        (_ : IsAffine T') (a : V.toScheme ⟶ T') (_ : CommSq a V.ι b g)
        (Z' : (pullback f b).IdealSheafData)
        (_ : Scheme.IdealSheafData.avoidsFiber (pullback.snd f b) Z' (a ⟨t, hVt⟩))
        (toXT : pullback f (V.ι ≫ g) ⟶ pullback f g)
        (toXT' : pullback f (V.ι ≫ g) ⟶ pullback f b)
        (_ : toXT ≫ pullback.fst f g = pullback.fst f (V.ι ≫ g))
        (_ : toXT ≫ pullback.snd f g = pullback.snd f (V.ι ≫ g) ≫ V.ι)
        (_ : toXT' ≫ pullback.fst f b = pullback.fst f (V.ι ≫ g))
        (_ : toXT' ≫ pullback.snd f b = pullback.snd f (V.ι ≫ g) ≫ a),
        Z'.comap toXT' ≤ Z.comap toXT)
