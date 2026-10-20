module

public import ReasLib.AlgebraicGeometry.Scheme.Normal.Affine
import StacksCheckRecall

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

open scoped AlgebraicGeometry

universe u

/- Lemma 28.7.4: an integral scheme is normal if and only if the section ring on every nonempty
affine open is a normal domain. -/
@[stacks 033L] #check
  (AlgebraicGeometry.Scheme.isNormal_iff_forall_affineOpen_isNormalRing :
    ∀ (X : AlgebraicGeometry.Scheme.{u}) [AlgebraicGeometry.IsIntegral X],
      X.isNormal ↔
        ∀ U : X.affineOpens, (U : Set X).Nonempty → _root_.IsNormalRing (Γ(X, U)))
