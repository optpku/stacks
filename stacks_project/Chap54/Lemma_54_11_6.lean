/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Normalization.Completion
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits IsLocalRing
open scoped AlgebraicGeometry

universe u

/- Lemma 54.11.6 (1): if the complement of the special fibre in the completion base change
of a locally finite type scheme over a Noetherian local ring is normal, then the normalization
morphism of the original scheme is finite. -/
@[stacks 0BG9] #check
  (AlgebraicGeometry.Scheme.Normalization.isFinite_of_isNormal_completionPuncture :
    ∀ (A : Type u) [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
      {X : Scheme.{u}} (f : X ⟶ Spec (.of A)) [LocallyOfFiniteType f],
    let Ahat := AdicCompletion (maximalIdeal A) A
    let g : Spec (.of Ahat) ⟶ Spec (.of A) :=
      Spec.map (CommRingCat.ofHom (algebraMap A Ahat))
    ∀ (h_normal :
        ((pullback.snd f g ⁻¹ᵁ PuncturedSpectrum.puncturedOpen Ahat).toScheme).isNormal),
      -- Local instance justification (search instability): `f` canonically makes `X` locally Noetherian, but `X` alone does not determine `f` for instance search.
      letI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
      IsFinite X.normalizationTo)

/- Lemma 54.11.6 (2): under the same normality hypothesis, base change of the normalization
to the maximal-ideal completion is the normalization of the completed base change, compatibly
over that base-changed scheme. -/
@[stacks 0BG9] #check
  (AlgebraicGeometry.Scheme.Normalization.completionBaseChange_isIsomorphic :
    ∀ (A : Type u) [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
      {X : Scheme.{u}} (f : X ⟶ Spec (.of A)) [LocallyOfFiniteType f],
    let Ahat := AdicCompletion (maximalIdeal A) A
    let g : Spec (.of Ahat) ⟶ Spec (.of A) :=
      Spec.map (CommRingCat.ofHom (algebraMap A Ahat))
    let Y := pullback f g
    ∀ (h_normal :
        ((pullback.snd f g ⁻¹ᵁ PuncturedSpectrum.puncturedOpen Ahat).toScheme).isNormal),
      -- Local instance justification (search instability): `f` canonically makes `X` locally Noetherian, but `X` alone does not determine `f` for instance search.
      letI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
      -- Local instance justification (search instability): `pullback.snd f g` canonically makes `Y` locally Noetherian, but `Y` alone does not determine this projection.
      letI : IsLocallyNoetherian Y :=
        LocallyOfFiniteType.isLocallyNoetherian (pullback.snd f g)
      IsIsomorphic
        (Over.mk (pullback.snd X.normalizationTo (pullback.fst f g)))
        (Over.mk Y.normalizationTo))
