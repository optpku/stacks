/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.RelativeSpectrum.Basic

/-!
# Contravariant maps of relative spectra

A morphism of quasi-coherent algebras over a fixed algebraic space induces a map of
relative spectra in the opposite direction. On a scheme point it leaves the base map
unchanged and precomposes the descended algebra map. This is the morphism part of the
affine/algebra correspondence of Stacks, Tag 081V.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

variable {S : Scheme.{u}}

/-- A morphism of quasi-coherent `𝒪_X`-algebras induces a morphism of relative spectra
in the opposite direction, by precomposition on functor-of-points algebra maps. -/
noncomputable def relativeSpecMap {X : AlgebraicSpace S} {A B : X.QcAlgebraUnder}
    (f : A ⟶ B) : relativeSpec B ⟶ relativeSpec A where
  app T :=
    TypeCat.ofHom fun p : relativeSpectrumPair B T.unop =>
      ⟨p.1, ⟨restrictUnderMap f.hom ≫ p.2.1, sorry⟩⟩
  naturality := sorry

/-- The first component of `relativeSpecMap f` is the same morphism to `X`. -/
theorem relativeSpecMap_fst {X : AlgebraicSpace S} {A B : X.QcAlgebraUnder}
    (f : A ⟶ B) (T : (Over S)ᵒᵖ) (p : relativeSpectrumPair B T.unop) :
    ((relativeSpecMap f).app T p).1 = p.1 := rfl

/-- The algebra map of `relativeSpecMap f` is precomposition with `restrictUnderMap f`. -/
theorem relativeSpecMap_snd {X : AlgebraicSpace S} {A B : X.QcAlgebraUnder}
    (f : A ⟶ B) (T : (Over S)ᵒᵖ) (p : relativeSpectrumPair B T.unop) :
    ((relativeSpecMap f).app T p).2.1 =
      restrictUnderMap f.hom ≫ p.2.1 := rfl

/-- `relativeSpecMap` is compatible with the structure morphisms to `X`. -/
theorem relativeSpecMap_comp_π {X : AlgebraicSpace S} {A B : X.QcAlgebraUnder}
    (f : A ⟶ B) :
    relativeSpecMap f ≫ relativeSpecπ A = relativeSpecπ B :=
  sorry

/-- Relative spectra send the identity algebra map to the identity map. -/
@[simp]
theorem relativeSpecMap_id {X : AlgebraicSpace S} (A : X.QcAlgebraUnder) :
    relativeSpecMap (𝟙 A) = 𝟙 (relativeSpec A) := sorry

/-- Relative spectra reverse composition of algebra morphisms over the same base. -/
theorem relativeSpecMap_comp {X : AlgebraicSpace S} {A B C : X.QcAlgebraUnder}
    (f : A ⟶ B) (g : B ⟶ C) :
    relativeSpecMap (f ≫ g) = relativeSpecMap g ≫ relativeSpecMap f := sorry

end AlgebraicGeometry.AlgebraicSpace
