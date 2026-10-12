/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import ReasLib.AlgebraicGeometry.Scheme.FieldExtension.Basic
public import ReasLib.AlgebraicGeometry.Scheme.FiniteEtale.FundamentalGroup
public import ReasLib.AlgebraicGeometry.Scheme.OverField

@[expose] public section

noncomputable section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme

universe u

namespace AlgebraicGeometry.SchemeOverField

/-- The base change of a scheme over `k` to an algebraic closure of `k`. -/
abbrev geometricBaseChange {k : Type u} [Field k] (X : SchemeOverField k) : Scheme.{u} :=
  FieldExtension.baseChange k (AlgebraicClosure k) X.hom

/-- The image on `X` of a geometric point of its base change to an algebraic closure. -/
abbrev arithmeticPoint {k : Type u} [Field k] (X : SchemeOverField k)
    (xbar : GeometricPoint (geometricBaseChange X)) : GeometricPoint X.left :=
  xbar.map (FieldExtension.toSource k (AlgebraicClosure k) X.hom)

/-- The morphism of étale fundamental groups induced by the geometric base-change projection. -/
def geometricToArithmetic {k : Type u} [Field k] (X : SchemeOverField k)
    [ConnectedSpace (geometricBaseChange X)] [ConnectedSpace X.left]
    (xbar : GeometricPoint (geometricBaseChange X)) :
    etaleFundamentalGroup (geometricBaseChange X) xbar ⟶
      etaleFundamentalGroup X.left (arithmeticPoint X xbar) :=
  ProfiniteGrp.ofHom
    ⟨(GeometricPoint.fundamentalGroupMap
        (FieldExtension.toSource k (AlgebraicClosure k) X.hom) xbar).toMonoidHom,
      sorry⟩

end AlgebraicGeometry.SchemeOverField
