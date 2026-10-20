module

public import ReasLib.AlgebraicGeometry.Scheme.FieldExtension.Geometric
public import ReasLib.AlgebraicGeometry.Scheme.FiniteEtale.FundamentalGroup

/-!
# Fundamental-group maps for a scheme over a field

Geometric base change belongs to `FieldExtension.Geometric`. This module
owns the induced point maps and continuous fundamental-group homomorphisms.
-/

@[expose] public section

open AlgebraicGeometry
open AlgebraicGeometry.Scheme

noncomputable section

universe u

namespace AlgebraicGeometry.SchemeOverField

/-- The image in `X` of a geometric point of the algebraic-closure base change. -/
noncomputable def arithmeticPoint {k : Type u} [Field k] (X : SchemeOverField k)
    (xbar : GeometricPoint (geometricBaseChange X)) : GeometricPoint X.left :=
  xbar.map (geometricToArithmeticHom X)

/-- The image in `Spec k` of a geometric point of a scheme over `k`. -/
noncomputable def galoisPoint {k : Type u} [Field k] (X : SchemeOverField k)
    (ybar : GeometricPoint X.left) : GeometricPoint (Spec (CommRingCat.of k)) :=
  ybar.map X.hom

/-- The homomorphism from the geometric to the arithmetic fundamental group. -/
noncomputable def geometricToArithmetic {k : Type u} [Field k] (X : SchemeOverField k)
    [ConnectedSpace (geometricBaseChange X)]
    (xbar : GeometricPoint (geometricBaseChange X)) :
    Scheme.GeometricPoint.etaleFundamentalGroup (geometricBaseChange X) xbar ⟶
      Scheme.GeometricPoint.etaleFundamentalGroup X.left (arithmeticPoint X xbar) :=
  ProfiniteGrp.ofHom (Scheme.GeometricPoint.fundamentalGroupMap
    (geometricToArithmeticHom X) xbar)

/-- The homomorphism from the arithmetic to the field-spectrum fundamental group. -/
noncomputable def arithmeticToGalois {k : Type u} [Field k] (X : SchemeOverField k)
    [ConnectedSpace X.left] (ybar : GeometricPoint X.left) :
    Scheme.GeometricPoint.etaleFundamentalGroup X.left ybar ⟶
      Scheme.GeometricPoint.etaleFundamentalGroup
        (Spec (CommRingCat.of k)) (galoisPoint X ybar) :=
  ProfiniteGrp.ofHom (Scheme.GeometricPoint.fundamentalGroupMap X.hom ybar)

end AlgebraicGeometry.SchemeOverField
