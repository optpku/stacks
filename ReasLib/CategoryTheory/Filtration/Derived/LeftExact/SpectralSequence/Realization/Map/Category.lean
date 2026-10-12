/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Filtration.Derived.LeftExact.SpectralSequence.Realization.Map.Identity
public import ReasLib.CategoryTheory.Filtration.Derived.LeftExact.SpectralSequence.Realization.Map.Composition
public import ReasLib.CategoryTheory.Filtration.Derived.LeftExact.SpectralSequence.Realization.Map.Reindex
public import ReasLib.CategoryTheory.Homology.SpectralSequence.Comparison
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Category laws for finite filtered right-derived realization maps

This file is a reusable leaf of the finite filtered right-derived spectral-sequence API.
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

/-- The identity realization map is a left identity after reindexing. -/
@[stacks 015W "left identity for finite filtered right-derived spectral-sequence maps"]
theorem id_comp {T : A ⥤ₗ B} [EnoughInjectives A]
    {K L : CochainComplex.Plus (FilteredObject.Finite.category A)} {f : K ⟶ L}
    {S : Realization T K} {R : Realization T L} (m : Map f S R) :
    reindex (Category.id_comp f) (comp (id S) m) = m := sorry

/-- The identity realization map is a right identity after reindexing. -/
@[stacks 015W "right identity for finite filtered right-derived spectral-sequence maps"]
theorem comp_id {T : A ⥤ₗ B} [EnoughInjectives A]
    {K L : CochainComplex.Plus (FilteredObject.Finite.category A)} {f : K ⟶ L}
    {S : Realization T K} {R : Realization T L} (m : Map f S R) :
    reindex (Category.comp_id f) (comp m (id R)) = m := sorry

/-- Composition of realization maps is associative after reindexing. -/
@[stacks 015W "associativity of finite filtered right-derived spectral-sequence maps"]
theorem assoc {T : A ⥤ₗ B} [EnoughInjectives A]
    {K L M N : CochainComplex.Plus (FilteredObject.Finite.category A)}
    {f : K ⟶ L} {g : L ⟶ M} {h : M ⟶ N}
    {S : Realization T K} {R : Realization T L}
    {U : Realization T M} {V : Realization T N}
    (m : Map f S R) (n : Map g R U) (k : Map h U V) :
    reindex (Category.assoc f g h) (comp (comp m n) k) = comp m (comp n k) := sorry

/-- A compatible realization map is an isomorphism from the first page onward whenever its
canonical maps on derived graded-piece cohomology are isomorphisms. -/
@[stacks 015W "page-one comparison for finite filtered right-derived spectral sequences"]
theorem isIsoFrom {T : A ⥤ₗ B} [EnoughInjectives A]
    {K L : CochainComplex.Plus (FilteredObject.Finite.category A)} {f : K ⟶ L}
    {S : Realization T K} {R : Realization T L} (m : Map f S R)
    (hpage : ∀ p q : ℤ, IsIso (PageOne.map T f p q)) :
    m.sequenceMap.IsIsoFrom 1 zero_le_one := sorry

/-- Every compatible realization map over an identity is an isomorphism from the first page
onward. -/
@[stacks 015W "independence of a finite filtered right-derived spectral sequence"]
theorem isIsoFromOne {T : A ⥤ₗ B} [EnoughInjectives A]
    {K : CochainComplex.Plus (FilteredObject.Finite.category A)}
    {S R : Realization T K} (m : Map (𝟙 K) S R) :
    m.sequenceMap.IsIsoFrom 1 zero_le_one := sorry

end Realization.Map

end CategoryTheory.FilteredObject.Finite.RightDerived.SpectralSequence
