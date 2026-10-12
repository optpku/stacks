/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FiniteLocallyFree.Operations
public import ReasLib.RingTheory.DiscreteValuationRing.Extension.UniformizerRoot
public import ReasLib.RingTheory.Localization.Away.Relative

@[expose] public section

open AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Hom

/-- For a positive exponent, the spectrum of the algebra obtained by adjoining a root of
`X ^ e - f` is finite locally free over the base ring. -/
theorem isFiniteLocallyFree_uniformizerRoot
    {A : Type u} [CommRing A] (f : A) (e : ℕ) (he : 1 ≤ e) :
    IsFiniteLocallyFree
      (Spec.map (CommRingCat.ofHom
        (algebraMap A (DVR.UniformizerRoot.RootRing f e)))) := sorry

/-- If a positive exponent is a unit in the base ring, adjoining a root of `X ^ e - f`
and inverting `f` gives a finite étale spectrum morphism. -/
theorem isFiniteEtale_uniformizerRoot_away
    {A : Type u} [CommRing A] (f : A) (e : ℕ) (he : 1 ≤ e)
    (he_unit : IsUnit (e : A)) :
    let C := DVR.UniformizerRoot.RootRing f e
    let g := Localization.awayMap (algebraMap A C) f
    IsFinite (Spec.map (CommRingCat.ofHom g)) ∧
      Etale (Spec.map (CommRingCat.ofHom g)) := sorry

end AlgebraicGeometry.Scheme.Hom
