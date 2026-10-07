module

import ReasLib.AlgebraicGeometry.Scheme.PreRelation.Invariant
import StacksCheckRecall

universe u

open CategoryTheory

variable {S : AlgebraicGeometry.Scheme.{u}} {U : Over S}

/- Definition 39.19.1 (1): a subset `W` is set-theoretically invariant under a groupoid
scheme when `t (s ⁻¹' W) ⊆ W`. -/
@[stacks 03BC] #check (AlgebraicGeometry.Scheme.PreRelation.IsSetInvariant :
  AlgebraicGeometry.Scheme.PreRelation U → Set U.left → Prop)

/- Definition 39.19.1 (2): an open subset is invariant when its underlying subset is
set-theoretically invariant. -/
@[stacks 03BC] #check (AlgebraicGeometry.Scheme.PreRelation.IsOpenInvariant :
  AlgebraicGeometry.Scheme.PreRelation U → U.left.Opens → Prop)

/- Definition 39.19.1 (3): a closed subscheme is invariant when its scheme-theoretic inverse
images under the target and source maps agree. -/
@[stacks 03BC] #check (AlgebraicGeometry.Scheme.PreRelation.IsClosedInvariant :
  AlgebraicGeometry.Scheme.PreRelation U → U.left.IdealSheafData → Prop)

/- Definition 39.19.1 (4): a monomorphism is invariant when its pullbacks under the target and
source maps agree as subobjects over the relation scheme. -/
@[stacks 03BC] #check (AlgebraicGeometry.Scheme.PreRelation.IsInvariant :
  AlgebraicGeometry.Scheme.PreRelation U → Subobject U.left → Prop)
