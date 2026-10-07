module

public import ReasLib.AlgebraicGeometry.Curve.Frobenius
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory
open Scheme.Hom
open Scheme.Hom.IsNonconstant

universe u

namespace AlgebraicGeometry.Curve

/- Lemma 53.13.3: let `f : X ⟶ Y` be a nonconstant morphism of proper nonsingular
curves over a field `k` of characteristic `p > 0`. If `X` is smooth and the induced
extension `k(Y) ⊆ k(X)` is inseparable of degree `p`, then there is a unique isomorphism
`Y ≅ X⁽ᵖ⁾` under which `f` is the relative Frobenius `F_{X/k}`. -/
@[stacks 0CCY] #check
  (AlgebraicGeometry.Curve.uniqueIsoRelativeFrobeniusTargetOfInseparableDegree :
    ∀ {k : Type u} [Field k] (p : ℕ) [Fact p.Prime] [CharP k p]
      (X Y : SchemeOverField k) [Curve X] [Curve Y]
      [Scheme.Regular X.left] [Scheme.Regular Y.left]
      [IsProper X.hom] [IsProper Y.hom] [Smooth X.hom]
      (f : X ⟶ Y) (hf : f.left.IsNonconstant)
      (_ : @FiniteFunctionFieldExtension _ _ f.left
        inferInstance inferInstance (isDominant_of_curves hf))
      (_ : @inducedFunctionFieldDegree _ _ f.left
        inferInstance inferInstance (isDominant_of_curves hf) = p)
      (_ :
        ¬@Algebra.IsSeparable Y.left.functionField X.left.functionField
          inferInstance inferInstance
          (@functionFieldAlgebra _ _ f.left inferInstance inferInstance
            (@map_genericPoint_eq_of_isDominant _ _ f.left
              inferInstance inferInstance (isDominant_of_curves hf)))),
      ∃! e : Y ≅ @relativeFrobeniusTargetOver p inferInstance X.left
        (Spec (CommRingCat.of k))
          X.hom inferInstance,
        f ≫ e.hom = @relativeFrobeniusOver p inferInstance X.left
          (Spec (CommRingCat.of k))
          X.hom inferInstance)

end AlgebraicGeometry.Curve
