/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Abelian.FunctorialProjectiveSurjections
import StacksCheckRecall

@[expose] public section

open CategoryTheory

universe v u

variable {C : Type u} [Category.{v} C] [HasFunctorialProjectiveSurjections C]
variable {A B : C} (f : A ⟶ B)

/-!
# Definition 12.28.5

Compatibility facade for the reusable functorial-projective-surjection interface.
-/

/- Definition 12.28.5 [013F]: a functorial choice of epimorphisms from projective objects is
the canonical `CategoryTheory.HasFunctorialProjectiveSurjections` structure. -/
@[stacks 013F]
#check (CategoryTheory.HasFunctorialProjectiveSurjections C : Type (max u v))

#check (CategoryTheory.HasFunctorialProjectiveSurjections.overFunctor (C := C) : C ⥤ C)
#check (CategoryTheory.HasFunctorialProjectiveSurjections.πNatTrans (C := C) :
  CategoryTheory.HasFunctorialProjectiveSurjections.overFunctor ⟶ 𝟭 C)
#check (CategoryTheory.HasFunctorialProjectiveSurjections.over A : C)
#check (CategoryTheory.HasFunctorialProjectiveSurjections.π A :
  CategoryTheory.HasFunctorialProjectiveSurjections.over A ⟶ A)
#check (CategoryTheory.HasFunctorialProjectiveSurjections.overMap f :
  CategoryTheory.HasFunctorialProjectiveSurjections.over A ⟶
    CategoryTheory.HasFunctorialProjectiveSurjections.over B)
#check (CategoryTheory.HasFunctorialProjectiveSurjections.presentation A :
  CategoryTheory.ProjectivePresentation A)
#check (CategoryTheory.HasFunctorialProjectiveSurjections.arrowFunctor (C := C) :
  C ⥤ CategoryTheory.Arrow C)
#check @CategoryTheory.HasFunctorialProjectiveSurjections.toLeftResolution
#check @CategoryTheory.Abelian.LeftResolution.hasFunctorialProjectiveSurjections
#check @CategoryTheory.Abelian.LeftResolution.toEnoughProjectives
