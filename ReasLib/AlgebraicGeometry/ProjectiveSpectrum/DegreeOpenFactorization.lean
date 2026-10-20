/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.ProjectiveSpectrum.DegreeOpen
public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Scheme

/-!
# Factorizations through fixed-degree opens of projective spectra

Morphisms which factor through a fixed positive-degree open of a projective spectrum form a
contravariant functor after identifying factorizations with the same ambient morphism.
-/

@[expose] public section

open CategoryTheory Opposite

noncomputable section

universe u v

namespace AlgebraicGeometry.Proj

variable {A : Type u} {σ : Type v} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
variable (𝒜 : ℕ → σ) [GradedRing 𝒜]

/-- A factorization of a scheme morphism through a fixed positive-degree open of `Proj 𝒜`. -/
structure DegreeOpenFactorization (Y : Scheme.{u}) where
  /-- The positive degree defining the target open. -/
  degree : ℕ
  /-- Positivity of the degree defining the target open. -/
  positive : 0 < degree
  /-- The morphism from the test scheme into the fixed-degree open. -/
  map : Y ⟶ (degreeOpen 𝒜 degree).toScheme

namespace DegreeOpenFactorization

/-- The identity factorization of a fixed positive-degree open into itself. -/
def ofDegreeOpen (d : ℕ) (hd : 1 ≤ d) :
    DegreeOpenFactorization 𝒜 (degreeOpen 𝒜 d).toScheme where
  degree := d
  positive := hd
  map := 𝟙 _

/-- The ambient morphism to `Proj 𝒜` determined by a factorization through a degree open. -/
def toProj {Y : Scheme.{u}} (x : DegreeOpenFactorization 𝒜 Y) : Y ⟶ Proj 𝒜 :=
  x.map ≫ (degreeOpen 𝒜 x.degree).ι

/-- The kernel relation that identifies factorizations inducing the same morphism to `Proj 𝒜`. -/
def setoid (Y : Scheme.{u}) : Setoid (DegreeOpenFactorization 𝒜 Y) :=
  Setoid.ker (toProj 𝒜)

end DegreeOpenFactorization

/-- Equivalence classes of positive-degree-open factorizations into `Proj 𝒜`. -/
abbrev DegreeOpenFactorizationClass (Y : Scheme.{u}) : Type u :=
  Quotient (DegreeOpenFactorization.setoid 𝒜 Y)

namespace DegreeOpenFactorization

/-- Pull a degree-open factorization back along a morphism of test schemes. -/
def pullback {Y Z : Scheme.{u}} (f : Y ⟶ Z) (x : DegreeOpenFactorization 𝒜 Z) :
    DegreeOpenFactorization 𝒜 Y where
  degree := x.degree
  positive := x.positive
  map := f ≫ x.map

/-- Pullback preserves equality of the induced ambient morphisms to `Proj 𝒜`. -/
theorem pullback_respects {Y Z : Scheme.{u}} (f : Y ⟶ Z)
    {x y : DegreeOpenFactorization 𝒜 Z} :
    (setoid 𝒜 Z).r x y → (setoid 𝒜 Y).r (pullback 𝒜 f x) (pullback 𝒜 f y) := by
  intro h
  change toProj 𝒜 x = toProj 𝒜 y at h
  change toProj 𝒜 (pullback 𝒜 f x) = toProj 𝒜 (pullback 𝒜 f y)
  simpa only [toProj, pullback, Category.assoc] using
    congrArg (fun g ↦ f ≫ g) h

end DegreeOpenFactorization

/-- Pullback on equivalence classes of positive-degree-open factorizations. -/
def degreeOpenFactorizationMap {Y Z : Schemeᵒᵖ} (f : Y ⟶ Z) :
    DegreeOpenFactorizationClass 𝒜 Y.unop ⟶ DegreeOpenFactorizationClass 𝒜 Z.unop :=
  TypeCat.ofHom (Quotient.map (DegreeOpenFactorization.pullback 𝒜 f.unop)
    (fun _ _ h ↦ DegreeOpenFactorization.pullback_respects 𝒜 f.unop h))

/-- Pullback of degree-open factorization classes preserves identity morphisms. -/
theorem degreeOpenFactorizationMap_id (Y : Schemeᵒᵖ) :
    degreeOpenFactorizationMap 𝒜 (𝟙 Y) = 𝟙 (DegreeOpenFactorizationClass 𝒜 Y.unop) := sorry

/-- Pullback of degree-open factorization classes preserves composition. -/
theorem degreeOpenFactorizationMap_comp {Y Z W : Schemeᵒᵖ} (f : Y ⟶ Z) (g : Z ⟶ W) :
    degreeOpenFactorizationMap 𝒜 (f ≫ g) =
      degreeOpenFactorizationMap 𝒜 f ≫ degreeOpenFactorizationMap 𝒜 g := sorry

/-- The contravariant functor of positive-degree-open factorization classes into `Proj 𝒜`. -/
def degreeOpenFactorizationFunctor : Schemeᵒᵖ ⥤ Type u where
  obj Y := DegreeOpenFactorizationClass 𝒜 Y.unop
  map := degreeOpenFactorizationMap 𝒜
  map_id := degreeOpenFactorizationMap_id 𝒜
  map_comp := degreeOpenFactorizationMap_comp 𝒜

/-- Divisibility of positive degrees induces inclusion of the corresponding fixed-degree opens. -/
theorem degreeOpen_le_of_dvd {d d' : {n : ℕ // 1 ≤ n}} (hdd' : d.1 ∣ d'.1) :
    degreeOpen 𝒜 d.1 ≤ degreeOpen 𝒜 d'.1 := sorry

end AlgebraicGeometry.Proj
