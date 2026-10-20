module

public import Mathlib.Algebra.Category.Grp.Abelian
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.Algebra.Homology.ShortComplex.Abelian

@[expose] public section

/-!
# The Derived Category of Additive Commutative Groups

This module registers the standard derived-category structure on `AddCommGrpCat` for use by
homological and sheaf-theoretic constructions.
-/

open CategoryTheory

noncomputable section

universe u

namespace AddCommGrpCat

/-- The standard derived-category structure on additive commutative groups. -/
instance hasDerivedCategory : HasDerivedCategory AddCommGrpCat.{u} :=
  HasDerivedCategory.standard AddCommGrpCat.{u}

end AddCommGrpCat
