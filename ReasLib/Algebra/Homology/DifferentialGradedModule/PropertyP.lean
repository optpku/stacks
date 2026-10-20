/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.Algebra.Homology.DifferentialGradedModule.Admissible
public import ReasLib.Algebra.Homology.DifferentialGradedModule.Limits
public import ReasLib.Algebra.Homology.DifferentialGradedModule.Regular
public import ReasLib.CategoryTheory.Filtration.Sequential.Successive

/-!
# Property P for differential graded modules

Property P is the intrinsic cellular filtration of a right module over a differential graded
algebra.  Its cells are coproducts of shifts of the regular module.
-/

@[expose] public section

noncomputable section

universe u v

open CategoryTheory CategoryTheory.Limits
open scoped DifferentialGradedModule

namespace DifferentialGradedModule

variable {R : Type u} [CommRing R]
variable (A : CochainDGAlgebra.{u, v} R)

namespace PropertyP

/-- A chosen coproduct presentation of a right DG `A`-module by shifts of the regular module.
The indexing type and the shift of every summand remain available to downstream constructions. -/
@[stacks 09KK "chosen coproduct of shifts of the regular differential graded module"]
structure Piece (P : DifferentialGradedModule.{u, v} A) where
  /-- The indexing type of regular-module summands. -/
  index : Type v
  /-- The shift of each regular-module summand. -/
  degree : index → ℤ
  /-- The selected identification with the coproduct of shifted regular modules. -/
  iso : P ≅ ∐ fun i : index ↦
    DifferentialGradedModule.shift A.regularModule (degree i)

/-- A right DG `A`-module is a coproduct of shifts of the regular module when it merely admits
such a concrete presentation. -/
@[stacks 09KK "coproducts of shifts of the regular differential graded module"]
def IsCoproductOfShifts : ObjectProperty (DifferentialGradedModule.{u, v} A) :=
  fun P ↦ Nonempty (Piece A P)

namespace Piece

/-- The shifted regular DG-module represented by one summand of a property-P piece. -/
@[stacks 09KK "summand of a property-P piece"]
abbrev summand {B : CochainDGAlgebra.{u, v} R}
    {P : DifferentialGradedModule.{u, v} B}
    (Q : Piece B P) (i : Q.index) : DifferentialGradedModule.{u, v} B :=
  DifferentialGradedModule.shift B.regularModule (Q.degree i)

/-- The coproduct injection of a chosen summand into a property-P piece. -/
@[stacks 09KK "injection of a property-P summand"]
noncomputable abbrev ι {B : CochainDGAlgebra.{u, v} R}
    {P : DifferentialGradedModule.{u, v} B}
    (Q : Piece B P) (i : Q.index) : Q.summand i ⟶ P :=
  Sigma.ι (fun j : Q.index ↦ Q.summand j) i ≫ Q.iso.inv

/-- The canonical map between property-P summands whose chosen shifts have equal degrees. -/
@[stacks 09KK "comparison of equal-degree property-P summands"]
abbrev summandEqToHom {B : CochainDGAlgebra.{u, v} R}
    {P Q : DifferentialGradedModule.{u, v} B}
    (D : Piece B P) (D' : Piece B Q) (i : D.index) (j : D'.index)
    (h : D.degree i = D'.degree j) : D.summand i ⟶ D'.summand j :=
  eqToHom (congrArg (DifferentialGradedModule.shift B.regularModule) h)

/-- A chosen piece presentation proves the corresponding coproduct-of-shifts property. -/
@[stacks 09KK "a property-P piece gives a coproduct-of-shifts presentation"]
theorem isCoproductOfShifts {P : DifferentialGradedModule.{u, v} A}
    (Q : Piece A P) : IsCoproductOfShifts A P := sorry

end Piece

/-- Section 22.20 (09KK): a property P filtration is a sequential filtration starting at zero,
with admissibly monic steps and explicitly presented successive coproducts of shifts of `A`. -/
@[stacks 09KK "property-P filtration"]
structure Filtration (P : DifferentialGradedModule.{u, v} A) extends
    SequentialFiltration P (admissibleMonomorphisms A) (IsCoproductOfShifts A) where
  /-- The concrete coproduct presentation of every successive piece. -/
  pieceData : ∀ n : ℕ, Piece A (piece n)

end PropertyP

/-- Section 22.20 (09KK): right DG `A`-modules admitting a property P filtration. -/
@[stacks 09KK "objects with property P"]
def HasPropertyP : ObjectProperty (DifferentialGradedModule.{u, v} A) :=
  fun P ↦ Nonempty (PropertyP.Filtration A P)

namespace PropertyP.Filtration

/-- A chosen property P filtration exhibits its ambient module as having property P. -/
@[stacks 09KK "a property-P filtration gives property P"]
theorem hasPropertyP {P : DifferentialGradedModule.{u, v} A}
    (F : Filtration A P) : HasPropertyP A P := sorry

end PropertyP.Filtration

namespace HasPropertyP

/-- Property P is invariant under isomorphism of differential graded modules. -/
@[stacks 09KK "property P is invariant under isomorphism"]
theorem of_iso {P Q : DifferentialGradedModule.{u, v} A}
    (hP : HasPropertyP A P) (e : P ≅ Q) : HasPropertyP A Q := sorry

/-- An isomorphism identifies property P on its source and target. -/
@[stacks 09KK "property P is equivalent across an isomorphism"]
theorem iff_of_iso {P Q : DifferentialGradedModule.{u, v} A} (e : P ≅ Q) :
    HasPropertyP A P ↔ HasPropertyP A Q := sorry

/-- Property P is closed under isomorphisms of differential graded modules. -/
@[stacks 09KK "property P is closed under isomorphisms"]
instance isClosedUnderIsomorphisms :
    (HasPropertyP A).IsClosedUnderIsomorphisms := sorry

end HasPropertyP

#synth (HasPropertyP A).IsClosedUnderIsomorphisms

end DifferentialGradedModule
