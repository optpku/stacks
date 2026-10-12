/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.FiniteEtale.GeometricArithmetic
public import stacks_project.Chap58.Theorem_58_6_2_Fiber

@[expose] public section

noncomputable section

open AlgebraicGeometry
open AlgebraicGeometry.Scheme

universe u

namespace AlgebraicGeometry.SchemeOverField

/- The promoted geometric-arithmetic fundamental-group result is available to legacy imports. -/
#check (geometricArithmetic_shortExact :
  {k : Type u} → [Field k] → (X : SchemeOverField k) →
    [CompactSpace X.left] → [QuasiSeparatedSpace X.left] →
    [ConnectedSpace (geometricBaseChange X)] →
    (xbar : GeometricPoint (geometricBaseChange X)) →
    Function.Injective (geometricToArithmetic X xbar) ∧
      MonoidHom.range (geometricToArithmetic X xbar).hom.toMonoidHom =
        MonoidHom.ker (arithmeticToGalois X (arithmeticPoint X xbar)).hom.toMonoidHom ∧
      Function.Surjective (arithmeticToGalois X (arithmeticPoint X xbar)))

end AlgebraicGeometry.SchemeOverField
