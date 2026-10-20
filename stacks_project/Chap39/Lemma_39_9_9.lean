module

public import ReasLib.AlgebraicGeometry.GroupScheme.AbelianVariety.Etale
import StacksCheckRecall

@[expose] public section

open CategoryTheory

universe u

/- Lemma 39.9.9: For a nonzero abelian variety `A` over a field `k`, multiplication by
an integer `d` is étale if and only if `d` is a unit in `k`. -/
@[stacks 0BFH] #check
  (AlgebraicGeometry.AbelianVariety.mulByInt_etale_iff :
    ∀ {k : Type u} [Field k] (A : AlgebraicGeometry.SchemeOverField k)
      [CategoryTheory.GrpObj A] [AlgebraicGeometry.AbelianVariety A],
      0 < AlgebraicGeometry.AbelianVariety.dimension A → ∀ d : ℤ,
        AlgebraicGeometry.Etale (AlgebraicGeometry.SchemeOverField.mulByInt A d) ↔
          IsUnit (d : k))
