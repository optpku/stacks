module

public import ReasLib.CategoryTheory.Filtration.Complex.Finite.Bounded
public import ReasLib.CategoryTheory.Filtration.Complex.FiniteAcyclic
public import ReasLib.CategoryTheory.Filtration.Complex.Finite.Stage
public import ReasLib.CategoryTheory.Filtration.Complex.Finite.Quotient
public import ReasLib.CategoryTheory.Filtration.Complex.Finite.Acyclic
public import ReasLib.CategoryTheory.Filtration.FiniteBiproduct
public import ReasLib.CategoryTheory.Filtration.Complex.QuasiIso
public import Mathlib.Algebra.Homology.HomotopyCategory.MappingCone

/-!
# Quasi-isomorphisms of bounded-below finite filtered complexes

This file owns the cochain-level morphism property for bounded-below finite filtered complexes.
It exposes graded-piece and underlying-complex bridges without choosing a localization or
duplicating the homotopy-level owner used by finite filtered derived categories.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits ComplexShape

noncomputable section

universe v u

namespace CategoryTheory.FilteredObject.Finite.Plus

section Basic

variable (C : Type u) [Category.{v} C] [Preadditive C] [HasZeroObject C]
  [HasCokernels C] [CategoryWithHomology (GradedObject ℤ C)]

/-- The morphism property of bounded-below finite filtered cochain maps whose associated-graded
maps are quasi-isomorphisms. -/
@[stacks 05RZ "bounded-below finite filtered cochain quasi-isomorphism"]
abbrev QuasiIso :
    MorphismProperty (CochainComplex.Plus (FilteredObject.Finite.category C)) :=
  fun _ _ f => FilteredObject.Finite.CochainComplex.quasiIso C f.hom

namespace QuasiIso

/-- Membership in the bounded-below finite filtered quasi-isomorphism property is exactly the
ambient cochain-level filtered quasi-isomorphism condition. -/
@[stacks 05RZ "bounded-below finite filtered cochain quasi-isomorphism"]
theorem iff {K L : CochainComplex.Plus (FilteredObject.Finite.category C)} (f : K ⟶ L) :
    Plus.QuasiIso C f ↔
      FilteredObject.Finite.CochainComplex.quasiIso C f.hom := sorry

/-- A bounded-below finite filtered quasi-isomorphism yields its ambient cochain-level
membership certificate. -/
@[stacks 05RZ "bounded-below finite filtered cochain quasi-isomorphism"]
theorem hom {K L : CochainComplex.Plus (FilteredObject.Finite.category C)}
    {f : K ⟶ L} (hf : Plus.QuasiIso C f) :
    FilteredObject.Finite.CochainComplex.quasiIso C f.hom := sorry

/-- Passing a bounded-below finite filtered map to the ambient homotopy category preserves and
reflects membership in the filtered quasi-isomorphism property. -/
@[stacks 05RZ "homotopy image of a bounded-below finite filtered quasi-isomorphism"]
theorem quotient_iff
    {K L : CochainComplex.Plus (FilteredObject.Finite.category C)} (f : K ⟶ L) :
    Plus.QuasiIso C f ↔
      FilteredObject.Finite.Homotopy.quasiIso C
        ((HomotopyCategory.quotient
          (FilteredObject.Finite.category C) (up ℤ)).map f.hom) := sorry

end QuasiIso

end Basic

namespace QuasiIso

/-- Every graded-piece cochain map of a bounded-below finite filtered quasi-isomorphism is an
ordinary quasi-isomorphism. -/
@[stacks 05RZ "graded piece of a bounded-below finite filtered quasi-isomorphism"]
theorem gradedPiece
    (C : Type u) [Category.{v} C] [Preadditive C] [HasZeroObject C]
    [HasCokernels C] [CategoryWithHomology C]
    [CategoryWithHomology (GradedObject ℤ C)]
    {K L : CochainComplex.Plus (FilteredObject.Finite.category C)}
    {f : K ⟶ L} (hf : Plus.QuasiIso C f) (p : ℤ) :
    _root_.QuasiIso (((GradedPiece.cochain C p).map f).hom) := sorry

/-- Forgetting a finite filtration sends a bounded-below filtered quasi-isomorphism to an
ordinary quasi-isomorphism of underlying cochain complexes. -/
@[stacks 05RZ "underlying map of a bounded-below finite filtered quasi-isomorphism"]
theorem underlying
    (C : Type u) [Category.{v} C] [Abelian C]
    {K L : CochainComplex.Plus (FilteredObject.Finite.category C)}
    {f : K ⟶ L} (hf : Plus.QuasiIso C f) :
    _root_.QuasiIso (((Forget.cochain C).map f).hom) := sorry

end QuasiIso

section Abelian

variable {C : Type u} [Category.{v} C] [Abelian C]
variable {K L : CochainComplex.Plus (FilteredObject.Finite.category C)}

/-- A morphism of bounded-below complexes of finite filtered objects is a filtered
quasi-isomorphism if and only if every induced filtration-stage map is a quasi-isomorphism. -/
theorem QuasiIso.stageMap_iff (f : K ⟶ L) :
    QuasiIso C f ↔
      ∀ p : ℤ, _root_.QuasiIso (((Stage.cochain C p).map f).hom) := sorry

/-- A morphism of bounded-below complexes of finite filtered objects is a filtered
quasi-isomorphism if and only if every induced quotient-by-stage map is a quasi-isomorphism. -/
theorem QuasiIso.quotientMap_iff (f : K ⟶ L) :
    QuasiIso C f ↔
      ∀ p : ℤ, _root_.QuasiIso (((Quotient.cochain C p).map f).hom) := sorry

/-- A morphism of bounded-below complexes of finite filtered objects is a filtered
quasi-isomorphism if and only if its canonical mapping cone is filtered acyclic. -/
theorem QuasiIso.mappingCone_iff (f : K ⟶ L) :
    QuasiIso C f ↔
      CochainComplex.acyclic (_root_.CochainComplex.mappingCone f.hom) := sorry

/-- A morphism of bounded-below complexes of finite filtered objects is a finite filtered
quasi-isomorphism if and only if its inclusion into all filtered complexes is a filtered
quasi-isomorphism. -/
theorem QuasiIso.isFilteredQuasiIso_iff (f : K ⟶ L) :
    QuasiIso C f ↔
      FilteredComplex.IsFilteredQuasiIso
        ((CochainComplex.inclusion C).map f.hom) := sorry

end Abelian

end CategoryTheory.FilteredObject.Finite.Plus
