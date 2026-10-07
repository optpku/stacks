module

public import stacks_project.Chap111.Exercise_111_30_8_Quotient
public import ReasLib.CategoryTheory.Filtration.Complex.Finite.QuasiIso
public import ReasLib.CategoryTheory.Filtration.Complex.Finite.Stage
public import ReasLib.CategoryTheory.Filtration.FiniteBiproduct
public import ReasLib.CategoryTheory.Filtration.FinitePreadditive
public import ReasLib.CategoryTheory.GradedObject.Homology
public import ReasLib.Algebra.Homology.CochainComplex.MappingCone.Bounded
public import stacks_project.Chap111.Definition_111_30_6_QuasiIso
public import stacks_project.Chap111.Definition_111_30_7_Acyclic
import Mathlib.Tactic.CrossRefAttribute

/-!
# Filtered quasi-isomorphisms of bounded-below finite filtered complexes

In an abelian category, a morphism of bounded-below complexes of finite filtered objects is a
filtered quasi-isomorphism if and only if each stage map, and each quotient-by-stage map, is an
ordinary quasi-isomorphism, and if and only if its mapping cone is filtered acyclic.  A filtered
quasi-isomorphism is in particular an ordinary quasi-isomorphism of underlying complexes.
-/

@[expose] public section

open CategoryTheory
open ComplexShape
open CochainComplex (mappingCone)
open FilteredObject.Finite

noncomputable section

universe v u

namespace CategoryTheory
namespace FilteredObject.Finite.Plus

variable {C : Type u} [Category.{v} C] [Abelian C]
variable {K L : CochainComplex.Plus (FilteredObject.Finite.category C)}

/-- Exercise 111.30.8 (1): a morphism `f` of bounded-below complexes of `Filᶠ(C)` is a
filtered quasi-isomorphism if and only if for every `p : ℤ` the induced map of stage complexes
`(Stage.cochain C p).map f` is a quasi-isomorphism. -/
@[stacks 028F]
theorem QuasiIso.stageMap_iff (f : K ⟶ L) :
    QuasiIso C f ↔
      ∀ p : ℤ, _root_.QuasiIso (((Stage.cochain C p).map f).hom) := sorry

/-- Exercise 111.30.8 (2): a morphism `f` of bounded-below complexes of `Filᶠ(C)` is a
filtered quasi-isomorphism if and only if for every `p : ℤ` the induced map of quotient complexes
`(Quotient.cochain C p).map f` is a quasi-isomorphism. -/
@[stacks 028F]
theorem QuasiIso.quotientMap_iff (f : K ⟶ L) :
    QuasiIso C f ↔
      ∀ p : ℤ, _root_.QuasiIso (((Quotient.cochain C p).map f).hom) := sorry

/-- Exercise 111.30.8 (3): a morphism `f` of bounded-below complexes of `Filᶠ(C)` is a
filtered quasi-isomorphism if and only if the canonical mapping cone `mappingCone f.hom`
is filtered acyclic as a cochain complex of `Filᶠ(C)`. -/
@[stacks 028F]
theorem QuasiIso.mappingCone_iff (f : K ⟶ L) :
    QuasiIso C f ↔
      CochainComplex.acyclic (mappingCone f.hom) := sorry

/-- Exercise 111.30.8 (4): a filtered quasi-isomorphism of bounded-below complexes of `Filᶠ(C)`
is a quasi-isomorphism of the underlying complexes. -/
@[stacks 028F]
theorem QuasiIso.toQuasiIso {f : K ⟶ L} (hf : QuasiIso C f) :
    _root_.QuasiIso (((Forget.cochain C).map f).hom) := sorry

/-- A morphism of bounded-below complexes of `Filᶠ(C)` is a finite filtered quasi-isomorphism
if and only if the included map of complexes in `Fil(C)` is a filtered quasi-isomorphism. -/
theorem QuasiIso.isFilteredQuasiIso_iff (f : K ⟶ L) :
    QuasiIso C f ↔
      FilteredComplex.IsFilteredQuasiIso
        ((CochainComplex.inclusion C).map f.hom) := sorry

end Plus
end Finite
end FilteredObject
end CategoryTheory
