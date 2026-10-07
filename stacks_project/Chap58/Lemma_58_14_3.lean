module

public import ReasLib.AlgebraicGeometry.Scheme.FiniteEtale.GeometricArithmetic
import StacksCheckRecall

@[expose] public section

universe u

/- Lemma 58.14.3: a geometrically connected quasi-compact quasi-separated scheme over a field
has a short exact geometric-arithmetic étale fundamental-group sequence. -/
@[stacks 0BTX] #check (AlgebraicGeometry.SchemeOverField.geometricArithmetic_shortExact :
  {k : Type u} → [Field k] → (X : AlgebraicGeometry.SchemeOverField k) →
    [CompactSpace X.left] → [QuasiSeparatedSpace X.left] →
    [ConnectedSpace (AlgebraicGeometry.SchemeOverField.geometricBaseChange X)] →
    (xbar : AlgebraicGeometry.Scheme.GeometricPoint
      (AlgebraicGeometry.SchemeOverField.geometricBaseChange X)) →
    Function.Injective
        (AlgebraicGeometry.SchemeOverField.geometricToArithmetic X xbar) ∧
      MonoidHom.range
          (AlgebraicGeometry.SchemeOverField.geometricToArithmetic X xbar).hom.toMonoidHom =
        MonoidHom.ker
          (AlgebraicGeometry.SchemeOverField.arithmeticToGalois X
            (AlgebraicGeometry.SchemeOverField.arithmeticPoint X xbar)).hom.toMonoidHom ∧
      Function.Surjective
        (AlgebraicGeometry.SchemeOverField.arithmeticToGalois X
          (AlgebraicGeometry.SchemeOverField.arithmeticPoint X xbar)))
