/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Homology.CochainComplex.Filtration.FilteredInjective
public import ReasLib.CategoryTheory.Filtration.FinitePreadditive
public import ReasLib.CategoryTheory.Filtration.Derived.Quotient
public import Mathlib.CategoryTheory.Triangulated.Orthogonal
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Preadditive Normalization for Finite Filtered Derived Categories

The finite-filtered category has a canonical preadditive structure and the canonical pointwise
zero morphisms inherited by its full subcategory. This module uses those lower-level owners to
form the homotopy image of a bounded-below filtered-injective complex directly. Downstream APIs
therefore use the canonical finite filtered homotopy category without transports of additive data.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MorphismProperty
open CategoryTheory.ObjectProperty
open ComplexShape

noncomputable section

universe v u

namespace CategoryTheory

namespace FilteredObject

namespace FiniteDerived

variable (C : Type u) [CategoryTheory.Category.{v} C] [Abelian C]

namespace Homotopy

/-- The canonical homotopy category of finite filtered cochain complexes. Its additive structure
is the one induced by `FilteredObject.Finite.preadditive`, so it is stable across downstream
abelian assumptions. -/
@[stacks 05TX "finite filtered homotopy category"]
abbrev Category : Type (max u v) :=
  HomotopyCategory (FilteredObject.Finite.category C) (ComplexShape.up ℤ)

/-- The quotient functor from finite filtered cochain complexes to their canonical homotopy
category.  This pins the canonical finite-filtered preadditive structure once, rather than making
downstream declarations expose an explicit `@HomotopyCategory.quotient` term. -/
@[stacks 05TX "finite filtered homotopy category"]
abbrev quotient :
    CochainComplex (FilteredObject.Finite.category C) ℤ ⥤ Category C :=
  HomotopyCategory.quotient (FilteredObject.Finite.category C) (ComplexShape.up ℤ)

end Homotopy

namespace FilteredInjective

/-- The homotopy image of bounded-below finite filtered-injective complexes in the canonical
finite filtered homotopy category. -/
@[stacks 05TX "finite filtered injective homotopy image"]
noncomputable def homotopy :
    CochainComplex.FilteredInjectivePlus C ⥤ Homotopy.Category C :=
  CochainComplex.FilteredInjectivePlus.ι C ⋙ Homotopy.quotient C

variable {C}

/-- The canonical finite filtered homotopy object represented by a bounded-below filtered-injective
complex. -/
@[stacks 05TX "finite filtered injective homotopy image"]
noncomputable def homotopyObj
    (I : CochainComplex.FilteredInjectivePlus C) : Homotopy.Category C :=
  (homotopy C).obj I

/-- A bounded-below finite filtered-injective complex is right-orthogonal to finite filtered
acyclic complexes in the canonical finite filtered homotopy category. -/
@[stacks 05TX "finite filtered injective orthogonality"]
theorem rightOrthogonal
    (I : CochainComplex.FilteredInjectivePlus C) :
    (FilteredObject.Finite.Homotopy.acyclic C).rightOrthogonal (homotopyObj I) := sorry

/-- The normalized filtered-injective homotopy object is local for finite filtered
quasi-isomorphisms. -/
@[stacks 05TY "finite filtered injective locality"]
theorem isLocal
    (I : CochainComplex.FilteredInjectivePlus C) :
    (FilteredObject.Finite.Homotopy.quasiIso C).isLocal (homotopyObj I) := sorry

end FilteredInjective

namespace Locality

variable {C}

/-- Precomposition with a finite filtered quasi-isomorphism is bijective on morphisms into a
normalized bounded-below filtered-injective homotopy object. -/
@[stacks 05TY "finite filtered injective locality"]
theorem precompBijective
    {K L : Homotopy.Category C} (I : CochainComplex.FilteredInjectivePlus C)
    (f : K ⟶ L) (hf : FilteredObject.Finite.Homotopy.quasiIso C f) :
    Function.Bijective
      (fun g : L ⟶ FilteredInjective.homotopyObj I => f ≫ g) := sorry

/-- The finite filtered derived quotient induces a bijection on maps into a normalized
bounded-below filtered-injective homotopy object.  The statement uses only the canonical
localization data, so it does not impose a false abelian structure on finite filtered objects. -/
@[stacks 05TY "finite filtered injective locality"]
theorem mapBijective
    (K : Homotopy.Category C) (I : CochainComplex.FilteredInjectivePlus C) :
    Function.Bijective
      ((Quotient.functor C).map :
        (K ⟶ FilteredInjective.homotopyObj I) → _) := sorry

end Locality

end FiniteDerived

end FilteredObject

end CategoryTheory
