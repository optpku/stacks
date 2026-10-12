/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Abelian.FunctorialInjectives.Definition
import StacksCheckRecall

@[expose] public section

open CategoryTheory

universe v u

variable {C : Type u} [Category.{v} C] [HasFunctorialInjectives C]
variable {A B : C} (f : A ⟶ B)

/-!
# Definition 12.27.5

Compatibility facade for the reusable functorial-injective-embedding interface.
-/

/- Definition 12.27.5 [0139]: a functorial choice of monomorphisms into injective objects is
the canonical `CategoryTheory.HasFunctorialInjectives` structure. -/
@[stacks 0139]
#check (CategoryTheory.HasFunctorialInjectives C : Type (max u v))

#check (CategoryTheory.HasFunctorialInjectives.functor (C := C) : C ⥤ C)
#check (CategoryTheory.HasFunctorialInjectives.ι (C := C) :
  𝟭 C ⟶ CategoryTheory.HasFunctorialInjectives.functor)
#check (CategoryTheory.HasFunctorialInjectives.obj A : C)
#check (CategoryTheory.HasFunctorialInjectives.ι.app A :
  A ⟶ CategoryTheory.HasFunctorialInjectives.obj A)
#check (CategoryTheory.HasFunctorialInjectives.map f :
  CategoryTheory.HasFunctorialInjectives.obj A ⟶
    CategoryTheory.HasFunctorialInjectives.obj B)
#check (CategoryTheory.HasFunctorialInjectives.presentation A :
  CategoryTheory.InjectivePresentation A)
#check (CategoryTheory.HasFunctorialInjectives.arrowFunctor (C := C) :
  C ⥤ CategoryTheory.Arrow C)
#check @CategoryTheory.HasFunctorialInjectives.ofArrowFunctor
