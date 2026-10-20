module

public import ReasLib.AlgebraicGeometry.Scheme.OverField.Tsen
import StacksCheckRecall

universe u

/- Theorem 59.67.10 (Tsen's theorem): the function field of a variety of dimension `r`
over an algebraically closed field `k` is `C_r`. -/
@[stacks 03RD] #check (AlgebraicGeometry.SchemeOverField.functionField_isCr_of_dimension :
  ∀ {k : Type u} [Field k] [IsAlgClosed k]
    (X : AlgebraicGeometry.SchemeOverField k) [AlgebraicGeometry.Variety X] (r : ℕ),
    X.dimension = r → Field.IsCr X.left.functionField r)
