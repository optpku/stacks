module

public import ReasLib.Algebra.Category.ModuleCat.ChangeOfRings.Pushout
public import ReasLib.RingTheory.Algebra.TensorProduct.RightAlgebra
import Mathlib.Tactic.CrossRefAttribute

/-!
# Tensor-product pushout comparisons

This leaf specializes the generic pushout comparison to the canonical square
`R → A`, `R → R'`, `A' = A ⊗[R] R'`.  The canonical right-hand tensor algebra is provided by the
shared `Algebra.TensorProduct.Right` scope because mathlib deliberately does not register it
globally.
@stack 0E1U
-/

@[expose] public section

noncomputable section

open CategoryTheory
open scoped TensorProduct Algebra.TensorProduct.Right

universe uR uA uR' w v

namespace CategoryTheory.ModuleCat.Pushout.Tensor

variable {R : Type uR} {A : Type uA} {R' : Type uR'}
variable [CommRing R] [CommRing A] [CommRing R']
variable [Algebra R A] [Algebra R R']

/-- The module-level comparison for the canonical tensor-product pushout. -/
@[stacks 0E1U "tensor-product pushout comparison for modules"]
noncomputable def moduleIso
    (E : ModuleCat.{max uA uR' w, uA} A) :
    (fromAlgebra (A := A) (R' := R') (A' := A ⊗[R] R')).obj E ≅
      (fromBase (R := R) (A := A) (R' := R')).obj E :=
  CategoryTheory.ModuleCat.Pushout.moduleIso
    (R := R) (A := A) (R' := R') (A' := A ⊗[R] R') E

/-- The natural tensor-product pushout comparison for module categories. -/
@[stacks 0E1U "tensor-product pushout natural isomorphism"]
noncomputable def natIso :
    (fromAlgebra (A := A) (R' := R') (A' := A ⊗[R] R') :
      ModuleCat.{max uA uR' w, uA} A ⥤ ModuleCat.{max uA uR' w, uR'} R') ≅
      (fromBase (R := R) (A := A) (R' := R') :
        ModuleCat.{max uA uR' w, uA} A ⥤ ModuleCat.{max uA uR' w, uR'} R') :=
  CategoryTheory.ModuleCat.Pushout.natIso
    (R := R) (A := A) (R' := R') (A' := A ⊗[R] R')

/-- The canonical `A ⊗[R] R'`-valued scalar extension of a cochain complex. -/
@[stacks 0E1U "tensor-product algebra-valued base-change route"]
abbrev algebraBaseChange
    (E : CochainComplex (ModuleCat.{max uA uR' w, uA} A) ℤ) :
    CochainComplex (ModuleCat (A ⊗[R] R')) ℤ :=
  CategoryTheory.ModuleCat.Pushout.algebraBaseChange
    (A := A) (A' := A ⊗[R] R') E

/-- The tensor-product pushout comparison on homological complexes of any shape. -/
@[stacks 0E1U "tensor-product pushout comparison on complexes"]
noncomputable def complexNatIso
    {ι : Type v} (c : ComplexShape ι) :
    ((fromAlgebra (A := A) (R' := R') (A' := A ⊗[R] R') :
      ModuleCat.{max uA uR' w, uA} A ⥤ ModuleCat.{max uA uR' w, uR'} R').mapHomologicalComplex c) ≅
      ((fromBase (R := R) (A := A) (R' := R') :
        ModuleCat.{max uA uR' w, uA} A ⥤ ModuleCat.{max uA uR' w, uR'} R').mapHomologicalComplex c) :=
  CategoryTheory.ModuleCat.Pushout.complexNatIso
    (R := R) (A := A) (R' := R')
    (A' := A ⊗[R] R') c

/-- The cochain-level tensor-product pushout comparison, with the base route exposed as
`E ⊗[R] R'` and the target route as the object
`(ModuleCat.restrictScalars (algebraMap R' (A ⊗[R] R'))).obj
  ((ModuleCat.extendScalars (algebraMap A (A ⊗[R] R'))).obj E)`. -/
@[stacks 0E1U "tensor-product pushout comparison on cochain complexes"]
noncomputable def cochainIso
  (E : CochainComplex (ModuleCat.{max uA uR' w, uA} A) ℤ) :
    algebraCochain (A := A) (R' := R') (A' := A ⊗[R] R') E ≅
      baseChangeCochain (R := R) (A := A) (R' := R') E :=
  CategoryTheory.ModuleCat.Pushout.cochainIso (R := R) (A := A) (R' := R')
    (A' := A ⊗[R] R') E

end CategoryTheory.ModuleCat.Pushout.Tensor
