module

public import ReasLib.CategoryTheory.Filtration.Complex.Definition
public import ReasLib.CategoryTheory.Filtration.Finite
public import ReasLib.CategoryTheory.Filtration.FinitePreadditive
public import ReasLib.CategoryTheory.Filtration.Complex.Functors
public import ReasLib.CategoryTheory.GradedObject.Homology
public import ReasLib.Algebra.Homology.HomotopyCategory.Acyclic
public import Mathlib.Algebra.Homology.HomotopyCategory
public import Mathlib.Algebra.Homology.HomotopyCategory.Shift
public import Mathlib.Algebra.Homology.Localization
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Finite Filtered Complexes

@stack 05RZ
@stack 05TW

This module contains the termwise finiteness condition for a filtered cochain complex.
It is deliberately separate from constructions such as truncation filtrations and from the
stage/graded functor API, so applications can depend on the condition without importing either.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe v u

namespace CategoryTheory

namespace FilteredComplex

variable {𝒜 : Type u} [Category.{v} 𝒜] [HasZeroMorphisms 𝒜] [HasZeroObject 𝒜]

/-- A filtered cochain complex has finite filtrations when every term has a finite filtration. -/
@[stacks 05TW "termwise finite filtration"]
abbrev HasFiniteFiltrations (K : FilteredComplex 𝒜) : Prop :=
  ∀ n : ℤ, (K.X n).IsFinite

end FilteredComplex

namespace FilteredObject

/-! ## Associated graded functors on finite filtered objects -/

section Basic

section AssociatedGraded

variable (C : Type u) [Category.{v} C] [HasZeroObject C] [HasZeroMorphisms C]
  [HasCokernels C]

namespace Finite.AssociatedGraded

/-- The associated-graded functor restricted to finite filtered objects. -/
@[stacks 05RZ "finite filtered associated graded functor"]
noncomputable def functor :
    FilteredObject.Finite.category C ⥤ GradedObject ℤ C :=
  FilteredObject.Finite.inclusion C ⋙ associatedGradedFunctor

/-- Evaluation of `Finite.AssociatedGraded.functor` on a finite filtered object. -/
@[stacks 05RZ "finite filtered associated graded functor", simp]
theorem obj (A : FilteredObject.Finite.category C) :
    (functor C).obj A = A.obj.associatedGraded := sorry

/-- Evaluation of `Finite.AssociatedGraded.functor` on a morphism of finite filtered objects. -/
@[stacks 05RZ "finite filtered associated graded functor", simp]
theorem map {A B : FilteredObject.Finite.category C} (f : A ⟶ B) :
    (functor C).map f =
      ((FilteredObject.Finite.inclusion C).map f).associatedGradedMap := sorry

end Finite.AssociatedGraded

end AssociatedGraded

end Basic

section Homotopy

section Forget

variable (C : Type u) [Category.{v} C] [Preadditive C] [HasZeroObject C]

namespace Finite.Forget

/-- The finite filtered forgetful functor is additive. -/
@[stacks 05RZ "finite filtered forgetful functor"]
instance additive : (Finite.Forget.functor C).Additive := sorry

end Finite.Forget

end Forget

section AssociatedGraded

variable (C : Type u) [Category.{v} C] [Preadditive C] [HasZeroObject C]
  [HasCokernels C]

namespace Finite.AssociatedGraded

/-- The finite filtered associated-graded functor is additive. -/
@[stacks 05RZ "finite filtered associated graded functor"]
instance additive :
    (Finite.AssociatedGraded.functor C).Additive := sorry

/-- The finite associated-graded functor preserves the canonical zero morphisms used by
homological complexes of finite filtered and graded objects. -/
@[stacks 05RZ "finite filtered associated graded functor"]
instance preservesZeroMorphisms :
    (Finite.AssociatedGraded.functor C).PreservesZeroMorphisms := sorry

/-- The associated-graded functor on cochain complexes of finite filtered objects. -/
@[stacks 05RZ "finite filtered associated graded cochain functor"]
noncomputable abbrev cochain :
    CochainComplex (FilteredObject.Finite.category C) ℤ ⥤ CochainComplex (GradedObject ℤ C) ℤ :=
  (Finite.AssociatedGraded.functor C).mapHomologicalComplex (ComplexShape.up ℤ)

/-- The associated-graded functor induced on the homotopy category of finite filtered complexes. -/
@[stacks 05RZ "finite filtered associated graded homotopy functor"]
noncomputable def homotopy :
    HomotopyCategory (FilteredObject.Finite.category C) (ComplexShape.up ℤ) ⥤
      HomotopyCategory (GradedObject ℤ C) (ComplexShape.up ℤ) :=
  (Finite.AssociatedGraded.functor C).mapHomotopyCategory (ComplexShape.up ℤ)

namespace Homotopy

/-- The finite associated-graded homotopy functor commutes with cohomological shifts. -/
@[stacks 05RZ "finite filtered associated graded homotopy functor"]
noncomputable instance commShift : (homotopy C).CommShift ℤ :=
  inferInstanceAs
    (((Finite.AssociatedGraded.functor C).mapHomotopyCategory (ComplexShape.up ℤ)).CommShift ℤ)

/-- The finite filtered associated-graded homotopy functor is induced by the finite associated
graded functor. -/
@[stacks 05RZ "finite filtered associated graded homotopy functor"]
theorem eq_map :
    homotopy C =
      (Finite.AssociatedGraded.functor C).mapHomotopyCategory (ComplexShape.up ℤ) := sorry

end Homotopy

end Finite.AssociatedGraded

end AssociatedGraded

section Homology

variable (C : Type u) [Category.{v} C] [Preadditive C] [HasZeroObject C]
  [HasCokernels C]

variable [CategoryWithHomology (GradedObject ℤ C)]

namespace Finite.CochainComplex

/-- A cochain map of finite filtered objects is a filtered quasi-isomorphism when its image under
the finite associated-graded cochain functor is a quasi-isomorphism. -/
@[stacks 05RZ "finite filtered cochain quasi-isomorphism"]
abbrev quasiIso
    {K L : CochainComplex (FilteredObject.Finite.category C) ℤ} (f : K ⟶ L) : Prop :=
  QuasiIso ((Finite.AssociatedGraded.cochain C).map f)

end Finite.CochainComplex

namespace Finite.Homotopy

/-- A morphism of finite filtered complexes is a quasi-isomorphism when its associated graded
image is a quasi-isomorphism. -/
@[stacks 05RZ "finite filtered quasi-isomorphism"]
noncomputable def quasiIso :
    MorphismProperty (HomotopyCategory (FilteredObject.Finite.category C) (ComplexShape.up ℤ)) :=
  (HomotopyCategory.quasiIso (GradedObject ℤ C) (ComplexShape.up ℤ)).inverseImage
    (Finite.AssociatedGraded.homotopy C)

/-- Membership in `Finite.Homotopy.quasiIso` is detected after applying the finite associated-graded
homotopy functor. -/
@[stacks 05RZ "finite filtered quasi-isomorphism"]
theorem quasiIso_iff {K L : HomotopyCategory (FilteredObject.Finite.category C) (ComplexShape.up ℤ)}
    (f : K ⟶ L) :
    quasiIso C f ↔
      HomotopyCategory.quasiIso (GradedObject ℤ C) (ComplexShape.up ℤ)
        ((Finite.AssociatedGraded.homotopy C).map f) := sorry

/-- The homotopy-class of a finite filtered cochain map is a finite filtered quasi-isomorphism
exactly when the original cochain map is one. -/
@[stacks 05RZ "finite filtered cochain quasi-isomorphism"]
theorem quasiIso_quotient_map_iff
    {K L : CochainComplex (FilteredObject.Finite.category C) ℤ} (f : K ⟶ L) :
    quasiIso C
        ((HomotopyCategory.quotient (FilteredObject.Finite.category C) (ComplexShape.up ℤ)).map f) ↔
      Finite.CochainComplex.quasiIso C f := sorry

/-- A finite filtered complex is acyclic when its associated graded complex has zero homology in
every degree. -/
@[stacks 05RZ "finite filtered acyclic complex"]
noncomputable def acyclic :
    ObjectProperty (HomotopyCategory (FilteredObject.Finite.category C) (ComplexShape.up ℤ)) :=
    (HomotopyCategory.Homology.acyclic (GradedObject ℤ C)).inverseImage
    (Finite.AssociatedGraded.homotopy C)

/-- Membership in `Finite.Homotopy.acyclic` is detected after applying the finite associated-graded
homotopy functor. -/
@[stacks 05RZ "finite filtered acyclic complex"]
theorem acyclic_iff (K : HomotopyCategory (FilteredObject.Finite.category C) (ComplexShape.up ℤ)) :
    acyclic C K ↔
      HomotopyCategory.Homology.acyclic (GradedObject ℤ C)
        ((Finite.AssociatedGraded.homotopy C).obj K) := sorry

end Finite.Homotopy

end Homology

end Homotopy

end FilteredObject

end CategoryTheory
