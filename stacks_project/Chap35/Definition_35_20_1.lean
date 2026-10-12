/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Germ
import StacksCheckRecall

@[expose] public section

/- Definition 35.20.1 (1): a germ of a scheme is a scheme together with a distinguished
point. -/
@[stacks 04QR] #check (AlgebraicGeometry.Scheme.Germ.of :
  (X : AlgebraicGeometry.Scheme) → X → AlgebraicGeometry.Scheme.Germ)

/- Definition 35.20.1 (2): morphisms of germs are neighborhood-defined pointed scheme
morphisms modulo agreement on a smaller open neighborhood. -/
@[stacks 04QR] #check (AlgebraicGeometry.Scheme.Germ.Hom.mk_eq_mk_iff :
  ∀ {X Y : AlgebraicGeometry.Scheme.Germ}
    (f g : AlgebraicGeometry.Scheme.Germ.Hom.Representative X Y),
    AlgebraicGeometry.Scheme.Germ.Hom.mk f = AlgebraicGeometry.Scheme.Germ.Hom.mk g ↔
      AlgebraicGeometry.Scheme.Germ.Hom.Representative.Equivalent f g)

/- Definition 35.20.1 (3): morphisms of germs compose by composing representatives on the
canonical smaller neighborhood. -/
@[stacks 04QR] #check (AlgebraicGeometry.Scheme.Germ.Hom.comp :
  ∀ {X Y Z : AlgebraicGeometry.Scheme.Germ},
    AlgebraicGeometry.Scheme.Germ.Hom X Y →
      AlgebraicGeometry.Scheme.Germ.Hom Y Z → AlgebraicGeometry.Scheme.Germ.Hom X Z)
