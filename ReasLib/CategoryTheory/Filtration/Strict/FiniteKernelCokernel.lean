module

public import ReasLib.CategoryTheory.Filtration.Finite
public import ReasLib.CategoryTheory.Filtration.Strict.Abelian

/-!
# Finite Induced and Quotient Filtrations

Finite filtrations are stable under passage to an induced filtration on a subobject and under
the quotient filtration along an epimorphism.  The filtered kernel and cokernel constructions
are exposed as direct specializations for downstream truncation and exactness arguments.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe v u

namespace CategoryTheory

namespace IndexedFiltration.IsFinite

variable {C : Type u} [Category.{v} C]
variable {I : Type*} [Preorder I] {A B : C}

/-- Pulling a finite indexed filtration back to a subobject gives a finite induced filtration. -/
theorem induced [HasPullbacks C] [HasZeroMorphisms C] [HasZeroObject C]
    {F : IndexedFiltration I A} (hF : IndexedFiltration.IsFinite F) (X : Subobject A) :
    IndexedFiltration.IsFinite (F.induced X) := sorry

/-- Pushing a finite indexed filtration forward along an epimorphism gives a finite quotient
filtration. -/
theorem quotient [HasImages C] [HasEqualizers C] [Balanced C] [HasZeroMorphisms C]
    [HasZeroObject C] {F : IndexedFiltration I A} (hF : IndexedFiltration.IsFinite F)
    (π : A ⟶ B) [Epi π] :
    IndexedFiltration.IsFinite (F.quotient π) := sorry

end IndexedFiltration.IsFinite

namespace FilteredObject.IsFinite

variable {C : Type u} [Category.{v} C]

/-- A finite filtered object induces a finite filtration on every subobject. -/
theorem subobject [HasPullbacks C] [HasZeroMorphisms C] [HasZeroObject C]
    {A : FilteredObject C} (hA : A.IsFinite) (X : Subobject A.obj) :
    (A.subobject X).IsFinite := sorry

/-- The quotient of a finite filtered object by a subobject has a finite quotient filtration. -/
theorem quotient [HasPullbacks C] [HasImages C] [HasZeroMorphisms C] [HasCokernels C]
    [HasEqualizers C] [Balanced C] [HasZeroObject C] {A : FilteredObject C}
    (hA : A.IsFinite) (X : Subobject A.obj) :
    (FilteredObject.Subobject.quotient A X).IsFinite := sorry

section Abelian

variable [Abelian C] {A B : FilteredObject C}

/-- The filtered kernel of a morphism with finite source has a finite induced filtration. -/
theorem kernel (hA : A.IsFinite) (f : A ⟶ B) :
    (FilteredObject.Hom.kernel f).IsFinite := sorry

/-- The filtered cokernel of a morphism with finite target has a finite quotient filtration. -/
theorem cokernel (hB : B.IsFinite) (f : A ⟶ B) :
    (FilteredObject.Hom.cokernel f).IsFinite := sorry

end Abelian

end FilteredObject.IsFinite

end CategoryTheory
