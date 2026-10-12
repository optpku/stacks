/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import ReasLib.AlgebraicGeometry.PuncturedSpectrum
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.QuasiSeparated.LocallyOfFiniteType
public import ReasLib.AlgebraicGeometry.Scheme.Normalization.LocallyNoetherian
public import ReasLib.RingTheory.AdicCompletion.Noetherian

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits IsLocalRing
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Normalization

/-- If the complement of the special fibre in the completion base change of a locally
finite type scheme over a Noetherian local ring is normal, its normalization morphism
is finite. -/
theorem isFinite_of_isNormal_completionPuncture
    (A : Type u) [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of A)) [LocallyOfFiniteType f] :
    let Ahat := AdicCompletion (maximalIdeal A) A
    let g : Spec (.of Ahat) ⟶ Spec (.of A) :=
      Spec.map (CommRingCat.ofHom (algebraMap A Ahat))
    ∀ (h_normal :
        ((pullback.snd f g ⁻¹ᵁ PuncturedSpectrum.puncturedOpen Ahat).toScheme).isNormal),
      -- Local instance justification (search instability): `f` canonically makes `X` locally Noetherian, but `X` alone does not determine `f` for instance search.
      letI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
      IsFinite X.normalizationTo := sorry

/-- If the complement of the special fibre in the completion base change of a locally
finite type scheme over a Noetherian local ring is normal, base change of its normalization
is isomorphic to the normalization of that base change, as schemes over the base change. -/
theorem completionBaseChange_isIsomorphic
    (A : Type u) [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of A)) [LocallyOfFiniteType f] :
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
        (Over.mk Y.normalizationTo) := sorry

end AlgebraicGeometry.Scheme.Normalization
