/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.Germ.MorphismProperties

@[expose] public section

universe u

/- Definition 35.20.2: a morphism of scheme germs is étale (respectively smooth) if it
has an étale (respectively smooth) representative on an open neighborhood of the
distinguished source point. -/
@[stacks 04QS] #check
  (AlgebraicGeometry.Scheme.Germ.Hom.etale_iff_exists_representation :
    ∀ {X Y : AlgebraicGeometry.Scheme.Germ.{u}}
      (f : AlgebraicGeometry.Scheme.Germ.Hom X Y),
      AlgebraicGeometry.Scheme.Germ.Hom.Etale f ↔
        ∃ r : AlgebraicGeometry.Scheme.Germ.Hom.Representative X Y,
          AlgebraicGeometry.Scheme.Germ.Hom.mk r = f ∧ AlgebraicGeometry.Etale r.hom)

#check
  (AlgebraicGeometry.Scheme.Germ.Hom.smooth_iff_exists_representation :
    ∀ {X Y : AlgebraicGeometry.Scheme.Germ.{u}}
      (f : AlgebraicGeometry.Scheme.Germ.Hom X Y),
      AlgebraicGeometry.Scheme.Germ.Hom.Smooth f ↔
        ∃ r : AlgebraicGeometry.Scheme.Germ.Hom.Representative X Y,
          AlgebraicGeometry.Scheme.Germ.Hom.mk r = f ∧ AlgebraicGeometry.Smooth r.hom)
