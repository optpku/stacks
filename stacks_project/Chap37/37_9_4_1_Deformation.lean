/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Deformation

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme.Hom.Deformation

variable {X' Y' : Scheme.{u}} {U' V' : X'.Opens}
variable (h : V' ≤ U') (a' : U'.toScheme ⟶ Y')

#check (restrictHom h a' : V'.toScheme ⟶ Y')

end AlgebraicGeometry.Scheme.Hom.Deformation
