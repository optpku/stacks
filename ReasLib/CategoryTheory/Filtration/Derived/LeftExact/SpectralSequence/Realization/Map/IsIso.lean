module

public import ReasLib.CategoryTheory.Filtration.Derived.LeftExact.SpectralSequence.Realization.Map.Category
public import ReasLib.CategoryTheory.Filtration.Complex.SpectralSequence.AssociationMorphism.IsIso
import Mathlib.Tactic.CrossRefAttribute

/-!
# Isomorphism transport for finite filtered right-derived realization maps

This leaf exposes the standard `IsIso` interface for the specialized realization-map owner.
The filtered-model component is the canonical input; the associated spectral-sequence component
and its page components are then available through ordinary typeclass search.  Target maps are
provided as explicit theorems because a target map alone does not determine the realization map
from which its comparison square came.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits ComplexShape
open CochainComplex.FilteredInjectivePlus

noncomputable section

universe w v₁ v₂ u₁ u₂

namespace CategoryTheory.FilteredObject.Finite.RightDerived.SpectralSequence

variable {A : Type u₁} {B : Type u₂}
  [_root_.CategoryTheory.Category.{v₁} A]
  [_root_.CategoryTheory.Category.{v₂} B]
  [Abelian A] [Abelian B] [HasDerivedCategory.{w} B]

namespace Realization.Map

/-- The spectral-sequence component of an isomorphic finite right-derived realization map is an
isomorphism. -/
@[stacks 015W "isomorphism transport for finite right-derived realization maps"]
noncomputable instance sequenceMap_isIso {T : A ⥤ₗ B} [EnoughInjectives A]
    {K L : CochainComplex.Plus (FilteredObject.Finite.category A)} {f : K ⟶ L}
    {S : Realization T K} {R : Realization T L} (m : Map f S R)
    [IsIso m.filteredMap] : IsIso m.sequenceMap := sorry

/-- Every page component of an isomorphic finite right-derived realization map is an isomorphism. -/
@[stacks 015W "page-component isomorphism transport for finite right-derived realization maps"]
noncomputable instance sequenceMap_f_isIso {T : A ⥤ₗ B} [EnoughInjectives A]
    {K L : CochainComplex.Plus (FilteredObject.Finite.category A)} {f : K ⟶ L}
    {S : Realization T K} {R : Realization T L} (m : Map f S R)
    (r : ℤ) (hr : 0 ≤ r) (p q : ℤ) [IsIso m.filteredMap] :
    IsIso ((m.sequenceMap.hom r hr).f (p, q)) := sorry

/-- The degree-`(p, q)` first-page target map is an isomorphism whenever it is induced by an
isomorphic finite filtered model. -/
@[stacks 015W "first-page target isomorphism for finite right-derived realization maps"]
theorem pageOneMap_isIso_of_filteredMap {T : A ⥤ₗ B} [EnoughInjectives A]
    {K L : CochainComplex.Plus (FilteredObject.Finite.category A)} {f : K ⟶ L}
    {S : Realization T K} {R : Realization T L} (m : Map f S R) (p q : ℤ)
    [IsIso m.filteredMap] : IsIso (PageOne.map T f p q) := sorry

/-- The degree-`n` abutment target map is an isomorphism whenever it is induced by an isomorphic
finite filtered model. -/
@[stacks 015W "abutment target isomorphism for finite right-derived realization maps"]
theorem abutmentMap_isIso_of_filteredMap {T : A ⥤ₗ B} [EnoughInjectives A]
    {K L : CochainComplex.Plus (FilteredObject.Finite.category A)} {f : K ⟶ L}
    {S : Realization T K} {R : Realization T L} (m : Map f S R) (n : ℤ)
    [IsIso m.filteredMap] : IsIso (Abutment.map T f n) := sorry

variable {T : A ⥤ₗ B} [EnoughInjectives A]
variable {K L : CochainComplex.Plus (FilteredObject.Finite.category A)} {f : K ⟶ L}
variable {S : Realization T K} {R : Realization T L}
variable (m : Map f S R) [IsIso m.filteredMap]

#synth IsIso m.sequenceMap
#synth IsIso ((m.sequenceMap.hom 1 zero_le_one).f (0, 0))

/- Axiom audit: the registered instances are proposition-valued transport; all concrete
resolution, filtered-model, and association data remain owned by `Map.Definition`. -/

end Realization.Map

end CategoryTheory.FilteredObject.Finite.RightDerived.SpectralSequence
