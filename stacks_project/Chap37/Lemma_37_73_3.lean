module

public import ReasLib.AlgebraicGeometry.Scheme.AffineStratification
import StacksCheckRecall

universe u

/- Lemma 37.73.3: a scheme admits a finite affine stratification if and only if it is
quasi-compact and quasi-separated. -/
@[stacks 0F2U]
#check (AlgebraicGeometry.Scheme.FiniteAffineStratification.nonempty_iff_compactSpace_and_quasiSeparatedSpace :
  ∀ X : AlgebraicGeometry.Scheme.{u},
    Nonempty (AlgebraicGeometry.Scheme.FiniteAffineStratification.{u, 0} X) ↔
      CompactSpace X ∧ QuasiSeparatedSpace X)
