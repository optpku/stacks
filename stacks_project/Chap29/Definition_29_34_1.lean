/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Smooth.Basic
import StacksCheckRecall

@[expose] public section

open CategoryTheory
open scoped AlgebraicGeometry

universe u

/- Definition 29.34.1: a scheme morphism is smooth at a point exactly when there are compatible
affine neighborhoods on which the induced coordinate-ring homomorphism is smooth. -/
@[stacks 01V5] #check
  (AlgebraicGeometry.Scheme.Hom.smoothAt_iff :
    ∀ {X S : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ S) (x : X),
      f.SmoothAt x ↔
        ∃ V : S.affineOpens, ∃ U : X.affineOpens,
          x ∈ (U : X.Opens) ∧ ∃ e : (U : X.Opens) ≤ f ⁻¹ᵁ (V : S.Opens),
            (f.appLE (V : S.Opens) (U : X.Opens) e).hom.Smooth)

/- The global smoothness condition is equivalent to smoothness at every source point. -/
#check
  (AlgebraicGeometry.Scheme.Hom.smooth_iff_forall_smoothAt :
    ∀ {X S : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ S),
      AlgebraicGeometry.Smooth f ↔ ∀ x : X, f.SmoothAt x)

/- For affine source and target, standard smoothness is the standard-smooth condition on the
canonical global-sections ring homomorphism. -/
#check
  (AlgebraicGeometry.standardSmooth_iff :
    ∀ {X S : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ S)
      [AlgebraicGeometry.IsAffine X] [AlgebraicGeometry.IsAffine S],
      AlgebraicGeometry.StandardSmooth f ↔
        RingHom.IsStandardSmooth
          (CommRingCat.Hom.hom (AlgebraicGeometry.Scheme.Hom.appTop f)))
