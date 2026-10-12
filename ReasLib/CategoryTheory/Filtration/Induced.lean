/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Filtration.ZeroMorphisms

/-!
# Induced and Quotient Filtrations

The pullback-induced filtration on a subobject and the image-quotient filtration on a target.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe v u

namespace CategoryTheory

variable {C : Type u} [Category.{v} C]

namespace IndexedFiltration

variable {I : Type*} [Preorder I] {A : C}

section Pullbacks

variable [HasPullbacks C]

/-- The filtration induced on a subobject by pulling back each stage. -/
noncomputable def induced (F : IndexedFiltration I A) (X : Subobject A) :
    IndexedFiltration I (X : C) :=
  (Subobject.pullback X.arrow).toOrderHom.comp F

end Pullbacks

section Images

variable [HasImages C]

/-- The filtration on a target obtained by taking images of the stages under a morphism. -/
noncomputable def quotient (F : IndexedFiltration I A) {B : C} (π : A ⟶ B) :
    IndexedFiltration I B :=
  (Subobject.«exists» π).toOrderHom.comp F

end Images

end IndexedFiltration

namespace FilteredObject

variable (A : FilteredObject C)

/-- Transport a filtered object across an isomorphism of its underlying object. -/
abbrev ofIso {X : C} (e : A.obj ≅ X) : FilteredObject C where
  obj := X
  filtration := ((Subobject.mapIsoToOrderIso e : Subobject A.obj →o Subobject X)).comp A.filtration

section Pushforward

variable [HasImages C] {X : C} (f : A.obj ⟶ X)

/-- The filtered object on `X` with the image filtration induced by `f`. -/
noncomputable def pushforward : FilteredObject C where
  obj := X
  filtration := A.filtration.quotient f

/-- The map `f` preserves the image filtration that it induces on its target. -/
theorem toPushforward_preserves (i : ℤ) :
    ((A.pushforward f).filtration i).Factors ((A.filtration i).arrow ≫ f) := sorry

/-- The canonical filtered morphism into the target equipped with the image filtration induced
by `f`. -/
noncomputable def toPushforward : A ⟶ A.pushforward f where
  hom := f
  preserves := A.toPushforward_preserves f

end Pushforward

section Subobject

variable [HasPullbacks C] (X : Subobject A.obj)

/-- The filtered object on a subobject, with the filtration induced from the ambient object. -/
noncomputable def subobject : FilteredObject C where
  obj := X
  filtration := A.filtration.induced X

/-- The ambient subobject inclusion preserves the induced filtration. -/
theorem subobjectι_preserves (i : ℤ) :
    (A.filtration.stage i).Factors (((A.subobject X).filtration i).arrow ≫ X.arrow) := sorry

/-- The inclusion of a filtered subobject into its ambient filtered object. -/
noncomputable def subobjectι : A.subobject X ⟶ A where
  hom := X.arrow
  preserves := A.subobjectι_preserves X

end Subobject

section Quotient

namespace Subobject

variable [HasZeroMorphisms C] [HasImages C] [HasCokernels C] (X : Subobject A.obj)

/-- The quotient filtered object `A / X`, with the image filtration induced by the quotient map. -/
noncomputable def quotient : FilteredObject C :=
  A.pushforward (cokernel.π X.arrow)

/-- The canonical map from a filtered object to its quotient by a subobject. -/
noncomputable def quotientπ : A ⟶ quotient A X :=
  A.toPushforward (cokernel.π X.arrow)

end Subobject

end Quotient

section SubobjectQuotient

namespace Subobject

variable [HasPullbacks C] [HasZeroMorphisms C] [HasImages C] [HasCokernels C]
variable (X : Subobject A.obj)

/-- The filtered subobject inclusion followed by the quotient map is zero. -/
theorem subobjectι_comp_quotientπ : A.subobjectι X ≫ quotientπ A X = 0 := sorry

end Subobject

end SubobjectQuotient

end FilteredObject

end CategoryTheory
