module

public import ReasLib.Algebra.Homology.DifferentialGradedModule.Derived
public import ReasLib.Algebra.Homology.DifferentialGradedModule.Derived.Limits
public import ReasLib.Algebra.Homology.DifferentialGradedModule.Regular
public import ReasLib.CategoryTheory.Preadditive.CompactObject
public import ReasLib.CategoryTheory.Pretriangulated.Generation.Localizing
public import ReasLib.CategoryTheory.Pretriangulated.Generation.Orthogonal
public import Mathlib.Tactic.CrossRefAttribute

/-!
# The Regular Generator of a Differential Graded Derived Category

For a cochain DG algebra `A`, this leaf owns the regular object in the canonical derived
category and its compact-generator properties.  It also proves that the images of the shifted
regular modules generate any chosen localization of the DG homotopy category at
quasi-isomorphisms.  The latter API includes the exact three-clause induction principle used by
the source: arbitrary coproducts, two-out-of-three for distinguished triangles, and the chosen
shifts.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.ObjectProperty
open DifferentialGradedCategory CategoryTheory.Pretriangulated

universe u v w

namespace DifferentialGradedModule.Derived

section Canonical

variable {R : Type u} [CommRing R]

/-- The regular module as an object of the canonical derived category of a cochain differential
graded algebra. -/
@[stacks 09S7 "regular object in the differential graded derived category"]
abbrev regularObject (A : CochainDGAlgebra.{u, v} R) : Category.{u, v} A :=
  (Q A).obj (CochainDGAlgebra.RegularModule.shiftK A 0)

/-- The zero shift of the regular module is canonically its unshifted homotopy object. -/
@[stacks 09S7 "zero-shift comparison for the regular derived generator"]
def regularZeroIso (A : CochainDGAlgebra.{u, v} R) :
    CochainDGAlgebra.RegularModule.shiftK A 0 ≅
      (DifferentialGradedModule.toK A).obj A.regularModule :=
  (DifferentialGradedModule.toK A).mapIso
    (DifferentialGradedModule.Shift.zeroApp A.regularModule)

/-- The regular object of a differential graded derived category is compact. -/
theorem regularObject_isCompact (A : CochainDGAlgebra.{u, v} R) :
    IsCompactObject (regularObject A) := sorry

/-- The regular object weakly generates its differential graded derived category. -/
theorem regularObject_isWeakGenerator (A : CochainDGAlgebra.{u, v} R) :
    IsWeakGenerator (regularObject A) := sorry

/-- The regular object localizing-generates its differential graded derived category. -/
theorem regularObject_isLocalizingGenerator (A : CochainDGAlgebra.{u, v} R) :
    (singleton (regularObject A)).IsLocalizingGenerator := sorry

/-- The integer shifts of the regular object detect isomorphisms in the differential graded
derived category. -/
theorem regularObject_shifts_isDetecting (A : CochainDGAlgebra.{u, v} R) :
    ((singleton (regularObject A)).shiftClosure ℤ).IsDetecting := sorry

end Canonical

section ChosenLocalization

variable {R : Type u} [CommRing R]
variable (A : CochainDGAlgebra R)
variable {D : Type v} [CategoryTheory.Category.{w} D] [HasZeroObject D] [Preadditive D]
variable [HasShift D ℤ] [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]
variable (Q : K R (DifferentialGradedModule A) ⥤ D)
variable [Q.IsLocalization (quasiIso A)]
variable [Q.CommShift ℤ] [Q.IsTriangulated]

/-- Remark 22.22.5 (`0FQE`): a property of objects in the derived category of a cochain DG
algebra holds for every object if it is closed under arbitrary coproducts, satisfies all three
two-out-of-three implications for distinguished triangles, and contains every shifted regular
module `A[k]`. -/
@[stacks 0FQE "generation by shifts of the regular differential graded module"]
theorem holds_of_regularShifts
    (T : ObjectProperty D)
    [∀ I : Type (max v w), T.IsClosedUnderColimitsOfShape (Discrete I)]
    [T.IsTriangulatedClosed₁] [T.IsTriangulatedClosed₂] [T.IsTriangulatedClosed₃]
    (h_shift : ∀ k : ℤ,
      T (Q.obj (CochainDGAlgebra.RegularModule.shiftK A k)))
    (X : D) :
    T X := sorry

/-- The images of all shifts of the regular DG module form a localizing generating family.
This is the canonical reusable form of Remark `22.22.5`. -/
theorem regularShifts_isLocalizingGenerator :
    (ofObj (fun k : ℤ ↦
      Q.obj (CochainDGAlgebra.RegularModule.shiftK A k))).IsLocalizingGenerator := sorry

end ChosenLocalization

end DifferentialGradedModule.Derived
