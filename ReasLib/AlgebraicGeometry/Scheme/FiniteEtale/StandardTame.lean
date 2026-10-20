/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.FiniteEtale
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FiniteLocallyFree.UniformizerRoot

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped AlgebraicGeometry

@[expose] public section

universe u

namespace AlgebraicGeometry.Scheme.FiniteEtale

/-- The finite étale standard root cover of the principal open defined by `f` with exponent `e`. -/
noncomputable def standardTameCoverAway {A : Type u} [CommRing A] (f : A) (e : ℕ)
    (he : 1 ≤ e) (he_unit : IsUnit (e : A)) :
    FiniteEtale (Spec (CommRingCat.of (Localization.Away f))) :=
  MorphismProperty.Over.mk ⊤
    (Spec.map (CommRingCat.ofHom
      (Localization.awayMap (algebraMap A (DVR.UniformizerRoot.RootRing f e)) f)))
    (AlgebraicGeometry.Scheme.Hom.isFiniteEtale_uniformizerRoot_away f e he he_unit)

/-- The finite coproduct of standard root covers indexed by a finite family of exponents. -/
noncomputable def sigmaStandardTameCoverAway {A : Type u} [CommRing A] (f : A) {n : ℕ}
    (e : Fin n → ℕ) (he : ∀ j, 1 ≤ e j ∧ IsUnit (e j : A)) :
    FiniteEtale (Spec (CommRingCat.of (Localization.Away f))) :=
  ∐ fun j : Fin n ↦ standardTameCoverAway f (e j) (he j).1 (he j).2

/-- The structural morphism of a standard root cover is the spectrum map induced by its localized
root-ring algebra map. -/
theorem standardTameCoverAway_hom {A : Type u} [CommRing A] (f : A) (e : ℕ)
    (he : 1 ≤ e) (he_unit : IsUnit (e : A)) :
    (standardTameCoverAway f e he he_unit).hom =
      Spec.map (CommRingCat.ofHom
        (Localization.awayMap (algebraMap A (DVR.UniformizerRoot.RootRing f e)) f)) := sorry

end AlgebraicGeometry.Scheme.FiniteEtale
