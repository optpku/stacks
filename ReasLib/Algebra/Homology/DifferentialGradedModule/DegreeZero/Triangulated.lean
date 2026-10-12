/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Homology.DifferentialGradedModule.DegreeZero
public import ReasLib.Algebra.Homology.DifferentialGradedModule.Shift.Category
public import ReasLib.CategoryTheory.Pretriangulated.Functor.Localization.Lift
public import ReasLib.CategoryTheory.Pretriangulated.Functor.RLinearEquivalence
public import Mathlib.CategoryTheory.Shift.Adjunction

/-!
# Triangulated Degree-Zero Comparisons

The concrete passage from complexes of ordinary modules to modules over a degree-zero DGA
commutes with shifts degreewise.  This file descends that comparison first to homotopy
categories and then through the derived localization.
-/

@[expose] public section

noncomputable section

universe uR uA w

open CategoryTheory ComplexShape DifferentialGradedCategory
open scoped ModuleCat.Algebra

namespace DifferentialGradedModule.DegreeZero

variable (R : Type uR) [CommRing R]
variable (A : Type uA) [Ring A] [Algebra R A]

/-- The degreewise identity identifies conversion after shifting an ordinary complex with
shifting the associated module over the degree-zero DGA. -/
def ofComplexShiftApp (K : CochainComplex (ModuleCat.{w} (Aᵐᵒᵖ)) ℤ) (k : ℤ) :
    ((shiftFunctor (CochainComplex (ModuleCat.{w} (Aᵐᵒᵖ)) ℤ) k ⋙
        ofComplexFunctor R A).obj K) ≅
      ((ofComplexFunctor R A ⋙ shiftFunctor
        (DifferentialGradedModule.{uR, w} (CochainDGAlgebra.ofAlgebra R A)) k).obj K) where
  hom :=
    { hom := fun _ ↦ LinearMap.id
      comm_d := sorry
      comm_smul := sorry }
  inv :=
    { hom := fun _ ↦ LinearMap.id
      comm_d := sorry
      comm_smul := sorry }
  hom_inv_id := sorry
  inv_hom_id := sorry

/-- The degreewise shift comparison for `ofComplexFunctor` is natural. -/
theorem ofComplexShiftApp_naturality
    (k : ℤ) {K L : CochainComplex (ModuleCat.{w} (Aᵐᵒᵖ)) ℤ} (f : K ⟶ L) :
    (shiftFunctor (CochainComplex (ModuleCat.{w} (Aᵐᵒᵖ)) ℤ) k ⋙
          ofComplexFunctor R A).map f ≫
        (ofComplexShiftApp R A L k).hom =
      (ofComplexShiftApp R A K k).hom ≫
        (ofComplexFunctor R A ⋙ shiftFunctor
          (DifferentialGradedModule.{uR, w} (CochainDGAlgebra.ofAlgebra R A)) k).map f := sorry

/-- The conversion from ordinary complexes to degree-zero DG modules commutes naturally with
integer shifts. -/
def ofComplexShiftIso (k : ℤ) :
    shiftFunctor (CochainComplex (ModuleCat.{w} (Aᵐᵒᵖ)) ℤ) k ⋙
        ofComplexFunctor R A ≅
      ofComplexFunctor R A ⋙ shiftFunctor
        (DifferentialGradedModule.{uR, w} (CochainDGAlgebra.ofAlgebra R A)) k :=
  NatIso.ofComponents (fun K ↦ ofComplexShiftApp R A K k)
    (fun f ↦ ofComplexShiftApp_naturality R A k f)

/-- The concrete ordinary-complex-to-DG-module functor has its canonical global shift
compatibility. -/
noncomputable instance ofComplexFunctor_commShift :
    (ofComplexFunctor R A).CommShift ℤ where
  commShiftIso := ofComplexShiftIso R A
  commShiftIso_zero := sorry
  commShiftIso_add := sorry

/-- The induced functor between the two homotopy categories commutes with integer shifts. -/
noncomputable instance toDGK_commShift : (toDGK R A).CommShift ℤ :=
  CategoryTheory.Quotient.liftCommShift
    (F := ofComplexFunctor R A ⋙
      DifferentialGradedModule.toK (CochainDGAlgebra.ofAlgebra R A))
    (r := homotopic (ModuleCat.{w} (Aᵐᵒᵖ)) (up ℤ))
    (A := ℤ)
    (fun _ _ _ _ h ↦ ofComplexFunctor_homotopic R A h)

/-- The concrete ordinary-to-DG derived comparison commutes with integer shifts. -/
noncomputable instance toDerived_commShift : (toDerived R A).CommShift ℤ :=
  Localization.liftCommShift
    (HomotopyCategory.quasiIso (ModuleCat.{w} (Aᵐᵒᵖ)) (up ℤ))
    (DerivedCategory.Qh :
      HomotopyCategory (ModuleCat.{w} (Aᵐᵒᵖ)) (up ℤ) ⥤
        DerivedCategory (ModuleCat.{w} (Aᵐᵒᵖ)))
    (toDGK R A ⋙ DifferentialGradedModule.Derived.Q
      (CochainDGAlgebra.ofAlgebra R A))
    (toDGK_inverts_quasiIso R A)

/-- The forward functor of the bundled degree-zero equivalence uses the canonical shift
comparison of `toDerived R A`. -/
noncomputable instance equivalenceFunctor_commShift :
    (equivalence R A).functor.CommShift ℤ :=
  toDerived_commShift R A

/-- The inverse functor of the bundled degree-zero equivalence carries the shift comparison
canonically induced by the equivalence adjunction. -/
noncomputable instance equivalenceInverse_commShift :
    (equivalence R A).inverse.CommShift ℤ :=
  (equivalence R A).commShiftInverse ℤ

/-- The standard quasi-inverse degree-zero comparison inherits the canonical compatible shift. -/
noncomputable instance fromDerived_commShift : (fromDerived R A).CommShift ℤ :=
  equivalenceInverse_commShift R A

/-- The ordinary-to-DG degree-zero comparison preserves distinguished triangles. -/
instance toDerived_isTriangulated : (toDerived R A).IsTriangulated := sorry

/-- The DG-to-ordinary degree-zero comparison preserves distinguished triangles. -/
instance fromDerived_isTriangulated : (fromDerived R A).IsTriangulated := sorry

/-- The canonical `R`-linear triangulated equivalence between the ordinary derived category and
the derived category of modules over the degree-zero DGA. -/
@[stacks 09SC "linear triangulated degree-zero comparison"]
noncomputable def triangulatedEquivalence :
    RLinear.TriangulatedEquivalence R
      (DerivedCategory (ModuleCat.{w} (Aᵐᵒᵖ)))
      (DifferentialGradedModule.Derived.Category.{uR, w}
        (CochainDGAlgebra.ofAlgebra R A)) :=
  { toEquivalence := equivalence R A
    functor_commShift := equivalenceFunctor_commShift R A
    inverse_commShift := equivalenceInverse_commShift R A
    functor_isTriangulated := toDerived_isTriangulated R A
    inverse_isTriangulated := fromDerived_isTriangulated R A
    functor_linear := toDerived_linear R A
    inverse_linear := fromDerived_linear R A }

end DifferentialGradedModule.DegreeZero
