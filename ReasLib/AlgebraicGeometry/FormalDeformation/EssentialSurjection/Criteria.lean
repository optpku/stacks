/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Data.List.TFAE
public import Mathlib.FieldTheory.Separable
public import ReasLib.Algebra.Algebra.ResidueImage
public import ReasLib.AlgebraicGeometry.FormalDeformation.ArtinianLocal.Cotangent
public import ReasLib.AlgebraicGeometry.FormalDeformation.ArtinianLocal.Kaehler
public import ReasLib.AlgebraicGeometry.FormalDeformation.EssentialSurjection
public import ReasLib.AlgebraicGeometry.FormalDeformation.SmallExtension

/-!
# Differential criteria for essential surjections

Surjectivity and essential surjectivity of residue-compatible Artinian local algebra
morphisms are detected by their induced Kähler tensor and conormal-image maps.
-/

@[expose] public section

open CategoryTheory

universe u

variable {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]

namespace ArtinianLocalAlgCat

/-- Surjectivity of a morphism is equivalent to surjectivity of its induced maps on
conormal images and residue-field tensors of Kähler differentials. -/
theorem surjective_tfae {B A : ArtinianLocalAlgCat Λ k} (f : B ⟶ A) :
    List.TFAE [Function.Surjective f.hom, Function.Surjective (Hom.conormalRangeMap f),
      Function.Surjective (Hom.kaehlerTensorMap f)] :=
  sorry

/-- A morphism is surjective if and only if its induced map on conormal images is surjective. -/
theorem surjective_iff_conormalRangeMap {B A : ArtinianLocalAlgCat Λ k} (f : B ⟶ A) :
    Function.Surjective f.hom ↔ Function.Surjective (Hom.conormalRangeMap f) :=
  sorry

/-- A morphism is surjective if and only if its induced Kähler tensor map is surjective. -/
theorem surjective_iff_kaehlerTensorMap {B A : ArtinianLocalAlgCat Λ k} (f : B ⟶ A) :
    Function.Surjective f.hom ↔ Function.Surjective (Hom.kaehlerTensorMap f) :=
  sorry

/-- Essential surjectivity of a morphism is equivalent to bijectivity of its induced maps on
conormal images and residue-field tensors of Kähler differentials. -/
theorem isEssentialSurjection_tfae {B A : ArtinianLocalAlgCat Λ k} (f : B ⟶ A) :
    List.TFAE [IsEssentialSurjection f, Function.Bijective (Hom.conormalRangeMap f),
      Function.Bijective (Hom.kaehlerTensorMap f)] :=
  sorry

/-- A morphism is an essential surjection if and only if its induced map on conormal images
is bijective. -/
theorem isEssentialSurjection_iff_bijective_conormalRangeMap
    {B A : ArtinianLocalAlgCat Λ k} (f : B ⟶ A) :
    IsEssentialSurjection f ↔ Function.Bijective (Hom.conormalRangeMap f) :=
  sorry

/-- A morphism is an essential surjection if and only if its induced Kähler tensor map
is bijective. -/
theorem isEssentialSurjection_iff_bijective_kaehlerTensorMap
    {B A : ArtinianLocalAlgCat Λ k} (f : B ⟶ A) :
    IsEssentialSurjection f ↔ Function.Bijective (Hom.kaehlerTensorMap f) :=
  sorry

/-- For a separable extension of the base residue field, a morphism is an essential
surjection if and only if its induced relative cotangent map is bijective. -/
theorem isEssentialSurjection_iff_bijective_mapRelative
    {B A : ArtinianLocalAlgCat Λ k} (f : B ⟶ A)
    [Algebra.IsSeparable (Algebra.residueImage Λ k) k] :
    IsEssentialSurjection f ↔ Function.Bijective (Hom.mapRelative f) :=
  sorry

/-- A small extension is not an essential surjection if and only if it has a section in the
category of residue-compatible Artinian local algebras. -/
theorem not_isEssentialSurjection_iff_exists_section
    {B A : ArtinianLocalAlgCat Λ k} (f : B ⟶ A) [IsSmallExtension f] :
    ¬ IsEssentialSurjection f ↔ ∃ s : A ⟶ B, s ≫ f = 𝟙 A :=
  sorry

end ArtinianLocalAlgCat
