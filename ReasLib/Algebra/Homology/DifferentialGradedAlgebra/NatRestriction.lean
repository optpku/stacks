/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Homology.Embedding.UpNat
public import ReasLib.Algebra.Homology.DifferentialGradedAlgebra.Category

/-!
# Restricting integer-indexed chain DGAs to natural degrees

This leaf owns the generic forgetful bridge from an integer-indexed chain DGA to its
natural-degree chain complex.  Tate resolutions and powered Koszul systems use the same
restriction, so the embedding and its functoriality belong below either construction.
-/

@[expose] public section

open CategoryTheory

universe u v

namespace ChainDGAlgebra

variable {R : Type u} [CommRing R]

/-- The canonical embedding of natural chain degrees into integer chain degrees. -/
abbrev natEmbedding :
    ComplexShape.Embedding (ComplexShape.down ℕ) (ComplexShape.down ℤ) :=
  ComplexShape.embeddingDownNatInt

/-- The natural-degree restriction of an integer-indexed chain DGA. -/
abbrev natRestriction (A : ChainDGAlgebra.{u, v} R) :
    ChainComplex (ModuleCat.{v} R) ℕ :=
  A.toChainComplex.natRestriction

/-- Degree `n` of the natural restriction is canonically degree `n` of the original DGA. -/
def natRestrictionXIso (A : ChainDGAlgebra.{u, v} R) (n : ℕ) :
    A.natRestriction.X n ≅ A.toChainComplex.X (n : ℤ) :=
  A.toChainComplex.restrictionXIso natEmbedding rfl

namespace Hom

variable {A B C : ChainDGAlgebra.{u, v} R}

/-- Restriction of a chain-DGA homomorphism to the underlying natural-degree chain complexes. -/
def natRestriction (f : Hom A B) : A.natRestriction ⟶ B.natRestriction :=
  HomologicalComplex.restrictionMap f.toChainMap natEmbedding

/-- The degree-`n` component of a restricted homomorphism is its original degree-`n` component. -/
@[simp]
theorem natRestriction_f (f : Hom A B) (n : ℕ) :
    f.natRestriction.f n =
      (A.natRestrictionXIso n).hom ≫ f.toChainMap.f (n : ℤ) ≫
        (B.natRestrictionXIso n).inv := sorry

/-- Restricting the identity chain-DGA homomorphism gives the identity chain map. -/
@[simp]
theorem natRestriction_id (A : ChainDGAlgebra.{u, v} R) :
    (Hom.id A).natRestriction = 𝟙 A.natRestriction := sorry

/-- Natural-degree restriction preserves composition of chain-DGA homomorphisms. -/
@[simp]
theorem natRestriction_comp (g : Hom B C) (f : Hom A B) :
    (Hom.comp g f).natRestriction = f.natRestriction ≫ g.natRestriction := sorry

end Hom

/-- The functor forgetting multiplication and restricting a chain DGA to natural degrees. -/
def natRestrictionFunctor (R : Type u) [CommRing R] :
    ChainDGAlgebra.{u, v} R ⥤ ChainComplex (ModuleCat.{v} R) ℕ where
  obj A := A.natRestriction
  map f := Hom.natRestriction f
  map_id A := Hom.natRestriction_id A
  map_comp f g := Hom.natRestriction_comp g f

end ChainDGAlgebra
