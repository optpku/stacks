module

public import ReasLib.AlgebraicGeometry.Scheme.Seminormal
import StacksCheckRecall

@[expose] public section

open scoped AlgebraicGeometry

universe u

variable (X : AlgebraicGeometry.Scheme.{u})

/- Definition 29.47.3 (1): a scheme is seminormal when every point has an
affine open neighbourhood whose section ring is seminormal. -/
@[stacks 0EUN] #check (AlgebraicGeometry.Scheme.Seminormal X : Prop)

#check
  (AlgebraicGeometry.Scheme.seminormal_iff X :
    AlgebraicGeometry.Scheme.Seminormal X ↔
      ∀ x : X, ∃ U : X.affineOpens, x ∈ (U : X.Opens) ∧
        SeminormalRing (Γ(X, (U : X.Opens))))

/- Definition 29.47.3 (2): a scheme is absolutely weakly normal when every
point has an affine open neighbourhood whose section ring is absolutely weakly
normal. -/
@[stacks 0EUN] #check (AlgebraicGeometry.Scheme.AbsolutelyWeaklyNormal X : Prop)

#check
  (AlgebraicGeometry.Scheme.absolutelyWeaklyNormal_iff X :
    AlgebraicGeometry.Scheme.AbsolutelyWeaklyNormal X ↔
      ∀ x : X, ∃ U : X.affineOpens, x ∈ (U : X.Opens) ∧
        AbsolutelyWeaklyNormalRing (Γ(X, (U : X.Opens))))
