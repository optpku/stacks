module

public import ReasLib.AlgebraicGeometry.Scheme.FieldExtension.Geometric
public import ReasLib.AlgebraicGeometry.Scheme.FiniteEtale.FundamentalGroup

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

/-- The geometric-to-arithmetic fundamental-group homomorphism is injective. -/
theorem geometricToArithmetic_injective {k : Type u} [Field k] (X : SchemeOverField k)
    [CompactSpace X.left] [QuasiSeparatedSpace X.left]
    [ConnectedSpace (geometricBaseChange X)]
    (xbar : GeometricPoint (geometricBaseChange X)) :
    Function.Injective (geometricToArithmetic X xbar) := sorry

/-- The arithmetic-to-Galois fundamental-group homomorphism is surjective. -/
theorem arithmeticToGalois_surjective {k : Type u} [Field k] (X : SchemeOverField k)
    [CompactSpace X.left] [QuasiSeparatedSpace X.left]
    [ConnectedSpace (geometricBaseChange X)] (ybar : GeometricPoint X.left) :
    Function.Surjective (arithmeticToGalois X ybar) := sorry

/-- The image of the geometric fundamental group is the kernel of the arithmetic-to-Galois map. -/
theorem geometricToArithmetic_range_eq_arithmeticToGalois_ker
    {k : Type u} [Field k] (X : SchemeOverField k)
    [CompactSpace X.left] [QuasiSeparatedSpace X.left]
    [ConnectedSpace (geometricBaseChange X)]
    (xbar : GeometricPoint (geometricBaseChange X)) :
    MonoidHom.range (geometricToArithmetic X xbar).hom.toMonoidHom =
      MonoidHom.ker (arithmeticToGalois X (arithmeticPoint X xbar)).hom.toMonoidHom :=
  sorry

/-- The geometric-arithmetic sequence of fundamental groups is short exact. -/
theorem geometricArithmetic_shortExact
    {k : Type u} [Field k] (X : SchemeOverField k)
    [CompactSpace X.left] [QuasiSeparatedSpace X.left]
    [ConnectedSpace (geometricBaseChange X)]
    (xbar : GeometricPoint (geometricBaseChange X)) :
    Function.Injective (geometricToArithmetic X xbar) ∧
      MonoidHom.range (geometricToArithmetic X xbar).hom.toMonoidHom =
        MonoidHom.ker (arithmeticToGalois X (arithmeticPoint X xbar)).hom.toMonoidHom ∧
      Function.Surjective (arithmeticToGalois X (arithmeticPoint X xbar)) := sorry

end AlgebraicGeometry.SchemeOverField
