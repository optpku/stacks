/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.OpenImmersion.BasicOpen
public import ReasLib.RingTheory.RingHom.Local.Properties
import StacksCheckRecall

open AlgebraicGeometry

universe u

/- Lemma 29.14.9 (1): isomorphisms on all target local rings are stable under
composition of commutative ring maps. -/
@[stacks 01SZ] #check
  (RingHom.IsIsoOnLocalRings.stableUnderComposition :
    RingHom.StableUnderComposition RingHom.IsIsoOnLocalRings)

/- Lemma 29.14.9 (2): affine spectrum maps that are open immersions are stable
under composition of the inducing commutative ring maps. -/
@[stacks 01SZ] #check
  (AlgebraicGeometry.IsOpenImmersion.specMap_stableUnderComposition :
    RingHom.StableUnderComposition
      (fun {R A : Type u} [CommRing R] [CommRing A] (φ : R →+* A) ↦
        AlgebraicGeometry.IsOpenImmersion (Spec.map (CommRingCat.ofHom φ))))

#check
  (AlgebraicGeometry.IsOpenImmersion.specMap_iff_exists_awayMap_bijective :
    ∀ {R A : Type u} [CommRing R] [CommRing A] (φ : R →+* A),
      AlgebraicGeometry.IsOpenImmersion (Spec.map (CommRingCat.ofHom φ)) ↔
        ∀ q : PrimeSpectrum A, ∃ f : R,
          φ f ∉ q.asIdeal ∧ Function.Bijective (Localization.awayMap φ f))

/- Lemma 29.14.9 (3): having Noetherian target is stable under composition of
commutative ring maps. -/
@[stacks 01SZ] #check
  (RingHom.TargetIsNoetherian.stableUnderComposition :
    RingHom.StableUnderComposition RingHom.TargetIsNoetherian)
