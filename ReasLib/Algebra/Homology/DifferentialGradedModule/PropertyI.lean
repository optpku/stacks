module

public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.Algebra.Homology.DifferentialGradedModule.Admissible
public import ReasLib.Algebra.Homology.DifferentialGradedModule.Limits
public import ReasLib.Algebra.Homology.DifferentialGradedModule.PontryaginDual
public import ReasLib.CategoryTheory.Filtration.SequentialInverse.Closure

/-!
# Property I for differential graded modules

Property I is the intrinsic inverse filtration of a right module over a differential graded
algebra.  Its successive kernels are explicitly presented as products of shifts of `Aᵛ`.
-/

@[expose] public section

noncomputable section

universe u v

open CategoryTheory CategoryTheory.Limits
open scoped DifferentialGradedModule

namespace DifferentialGradedModule

variable {R : Type u} [CommRing R]
variable (A : CochainDGAlgebra.{u, v} R)

namespace PropertyI

/-- A chosen product presentation of a right DG `A`-module by shifts of the distinguished
Pontryagin dual `Aᵛ`.  The index type and every shift degree remain available to consumers. -/
@[stacks 09KQ "products of shifts of the dual regular differential graded module"]
structure Piece (Q : DifferentialGradedModule.{u, v} A) where
  /-- The indexing type of product factors. -/
  index : Type v
  /-- The shift attached to each product factor. -/
  degree : index → ℤ
  /-- The specified product presentation. -/
  iso : Q ≅ ∏ᶜ fun i : index ↦
    DifferentialGradedModule.shift A.dualRegularModule (degree i)

/-- The object property of admitting a product presentation by shifts of `Aᵛ`. -/
@[stacks 09KQ "objects which are products of shifts of the dual regular module"]
def IsProductOfShifts : ObjectProperty (DifferentialGradedModule.{u, v} A) :=
  fun Q ↦ Nonempty (Piece A Q)

namespace Piece

/-- The shifted dual regular DG-module represented by one factor of a property-I piece. -/
@[stacks 09KQ "factor of a property-I piece"]
abbrev factor {B : CochainDGAlgebra.{u, v} R}
    {Q : DifferentialGradedModule.{u, v} B}
    (P : Piece B Q) (i : P.index) : DifferentialGradedModule.{u, v} B :=
  DifferentialGradedModule.shift B.dualRegularModule (P.degree i)

/-- The product projection from a property-I piece to a chosen factor. -/
@[stacks 09KQ "projection to a property-I factor"]
noncomputable abbrev π {B : CochainDGAlgebra.{u, v} R}
    {Q : DifferentialGradedModule.{u, v} B}
    (P : Piece B Q) (i : P.index) : Q ⟶ P.factor i :=
  P.iso.hom ≫ Pi.π (fun j : P.index ↦ P.factor j) i

/-- The canonical map between property-I factors whose chosen shifts have equal degrees. -/
@[stacks 09KQ "comparison of equal-degree property-I factors"]
abbrev factorEqToHom {B : CochainDGAlgebra.{u, v} R}
    {P Q : DifferentialGradedModule.{u, v} B}
    (D : Piece B P) (D' : Piece B Q) (i : D.index) (j : D'.index)
    (h : D.degree i = D'.degree j) : D.factor i ⟶ D'.factor j :=
  eqToHom (congrArg (DifferentialGradedModule.shift B.dualRegularModule) h)

/-- A chosen piece presentation proves the corresponding product-of-shifts property. -/
@[stacks 09KQ "a property-I piece is a product of shifts"]
theorem isProductOfShifts {Q : DifferentialGradedModule.{u, v} A}
    (P : Piece A Q) : IsProductOfShifts A Q := sorry

end Piece

/-- Section 22.21 (09KQ): a property I filtration presents a right DG `A`-module as the
inverse limit of admissible quotients and retains concrete product data for every successive
kernel. -/
@[stacks 09KQ "property-I filtration"]
structure Filtration (I : DifferentialGradedModule.{u, v} A) extends
    SequentialInverseFiltration I (admissibleEpimorphisms A) (IsProductOfShifts A) where
  /-- The concrete product-of-dual-shifts presentation of every successive kernel. -/
  pieceData : ∀ n : ℕ, Piece A (piece n)

namespace Filtration

/-- The underlying generic sequential inverse filtration. -/
@[stacks 09KQ "underlying sequential filtration of a property-I filtration"]
abbrev underlying {I : DifferentialGradedModule.{u, v} A} (F : Filtration A I) :
    SequentialInverseFiltration I (admissibleEpimorphisms A) (IsProductOfShifts A) :=
  F.toSequentialInverseFiltration

/-- The concrete product presentation of the `n`th successive kernel. -/
@[stacks 09KQ "presentation of a successive property-I kernel"]
abbrev piecePresentation {I : DifferentialGradedModule.{u, v} A}
    (F : Filtration A I) (n : ℕ) : Piece A (F.piece n) :=
  F.pieceData n

end Filtration

end PropertyI

/-- Section 22.21 (09KQ): right DG `A`-modules admitting a property I filtration. -/
@[stacks 09KQ "objects with property I"]
def HasPropertyI : ObjectProperty (DifferentialGradedModule.{u, v} A) :=
  fun I ↦ Nonempty (PropertyI.Filtration A I)

namespace PropertyI.Filtration

/-- A chosen property I filtration exhibits its ambient module as having property I. -/
@[stacks 09KQ "a property-I filtration gives property I"]
theorem hasPropertyI {I : DifferentialGradedModule.{u, v} A}
    (F : Filtration A I) : HasPropertyI A I := sorry

end PropertyI.Filtration

namespace HasPropertyI

/-- Property I is invariant under isomorphism of differential graded modules. -/
@[stacks 09KQ "property I is invariant under isomorphism"]
theorem of_iso {I J : DifferentialGradedModule.{u, v} A}
    (hI : HasPropertyI A I) (e : I ≅ J) : HasPropertyI A J := sorry

/-- An isomorphism identifies property I on its source and target. -/
@[stacks 09KQ "property I is equivalent across an isomorphism"]
theorem iff_of_iso {I J : DifferentialGradedModule.{u, v} A} (e : I ≅ J) :
    HasPropertyI A I ↔ HasPropertyI A J := sorry

/-- Property I is closed under isomorphisms of differential graded modules. -/
@[stacks 09KQ "property I is closed under isomorphisms"]
instance isClosedUnderIsomorphisms :
    (HasPropertyI A).IsClosedUnderIsomorphisms := sorry

end HasPropertyI

#synth (HasPropertyI A).IsClosedUnderIsomorphisms

end DifferentialGradedModule
