module

public import ReasLib.Algebra.Homology.DifferentialGradedModule.Bimodule
public import ReasLib.Algebra.Homology.DifferentialGradedModule.PropertyP

/-!
# Property P for Differential Graded Bimodules

Property P for an `(A, B)`-bimodule is the intrinsic property P of the corresponding module over
the enveloping DGA `A.opposite ⊗[R] B`.  These transparent specializations keep the bimodule API
short while leaving the filtration and its cells under the general DG-module owner.

The full enveloping specialization uses independent carrier universes for `A` and `B`; its
bimodule carrier is `max v w`, the carrier of the enveloping DGA.  The left-module convenience
predicate `HasLeftPropertyP` instead keeps the bimodule carrier equal to the carrier of `A`,
while allowing `B` to live independently.  In both cases the filtration and its cells remain
owned by the general DG-module Property-P API.
-/

@[expose] public section

universe u v w

open CategoryTheory

namespace DifferentialGradedBimodule

variable {R : Type u} [CommRing R]

section EnvelopingCarrier

variable (A : CochainDGAlgebra.{u, v} R) (B : CochainDGAlgebra.{u, w} R)

namespace PropertyP

/-- A chosen coproduct presentation of a DG `(A, B)`-bimodule by shifts of the regular
`A.opposite ⊗[R] B`-module. -/
@[stacks 0FQK "property-P pieces for differential graded bimodules"]
abbrev Piece (P : DifferentialGradedBimodule.{u, max v w, v, w} A B) :=
  DifferentialGradedModule.PropertyP.Piece
    (CochainDGAlgebra.enveloping A B) P

/-- DG `(A, B)`-bimodules which are coproducts of shifts of the regular enveloping module. -/
@[stacks 0FQK "coproducts of shifted regular differential graded bimodules"]
abbrev IsCoproductOfShifts :
    ObjectProperty (DifferentialGradedBimodule.{u, max v w, v, w} A B) :=
  DifferentialGradedModule.PropertyP.IsCoproductOfShifts
    (CochainDGAlgebra.enveloping A B)

/-- A property P filtration of a DG `(A, B)`-bimodule by shifted regular enveloping modules. -/
@[stacks 0FQK "property-P filtrations for differential graded bimodules"]
abbrev Filtration (P : DifferentialGradedBimodule.{u, max v w, v, w} A B) :=
  DifferentialGradedModule.PropertyP.Filtration
    (CochainDGAlgebra.enveloping A B) P

end PropertyP

/-- A DG `(A, B)`-bimodule has property P when it admits a filtration whose successive pieces
are coproducts of shifts of the regular `A.opposite ⊗[R] B`-module. -/
@[stacks 0FQK "property P for differential graded bimodules"]
abbrev HasPropertyP :
    ObjectProperty (DifferentialGradedBimodule.{u, max v w, v, w} A B) :=
  DifferentialGradedModule.HasPropertyP (CochainDGAlgebra.enveloping A B)

end EnvelopingCarrier

section LeftCarrier

variable (A : CochainDGAlgebra.{u, v} R) (B : CochainDGAlgebra.{u, w} R)

/-- A differential graded `(A, B)`-bimodule has property P on the left when its canonical
right `A.opposite`-module has property P.  Only the bimodule and `A` carriers must agree;
the right-hand algebra `B` may live in an independent universe. -/
@[stacks 0GZ2 "property P for the left module underlying a differential graded bimodule"]
abbrev HasLeftPropertyP : ObjectProperty (DifferentialGradedBimodule.{u, v, v, w} A B) :=
  fun N ↦ DifferentialGradedModule.HasPropertyP A.opposite N.toOppositeLeftModule

end LeftCarrier

end DifferentialGradedBimodule
