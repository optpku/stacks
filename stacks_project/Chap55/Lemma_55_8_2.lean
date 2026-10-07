module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.Normalization.GeometricallyNormalModel

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits IsLocalRing
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Normalization

/- Lemma 55.8.2 (1): the normalization morphism of a flat finite-type model of a
geometrically normal variety over the fraction field of a discrete valuation ring is finite. -/
@[stacks 0C2T] #check
  (AlgebraicGeometry.Scheme.Normalization.isFinite_of_geometricallyNormalModel :
    ∀ (R K : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [Field K] [Algebra R K] [IsFractionRing R K]
    (V : SchemeOverField K) [Variety V]
    (hV : SchemeOverField.geometricallyNormal V)
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R)) [Flat f] [Scheme.Hom.FiniteType f]
    (e : V ≅ Over.mk
      (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap R K))))),
    -- Local instance justification (search instability): `f` canonically makes `X` locally Noetherian, but `X` alone does not determine `f` for instance search.
    letI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
    IsFinite X.normalizationTo)

/- Lemma 55.8.2 (2): after base change to the maximal-ideal completion of the discrete
valuation ring, the base change of the model's normalization is the normalization of the
base-changed model, compatibly over that model. -/
@[stacks 0C2T] #check
  (AlgebraicGeometry.Scheme.Normalization.completionBaseChange_isIsomorphic_of_geometricallyNormalModel :
    ∀ (R K : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [Field K] [Algebra R K] [IsFractionRing R K]
    (V : SchemeOverField K) [Variety V]
    (hV : SchemeOverField.geometricallyNormal V)
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R)) [Flat f] [Scheme.Hom.FiniteType f]
    (e : V ≅ Over.mk
      (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap R K))))),
    let Rhat := AdicCompletion (maximalIdeal R) R
    let g : Spec (CommRingCat.of Rhat) ⟶ Spec (CommRingCat.of R) :=
      Spec.map (CommRingCat.ofHom (algebraMap R Rhat))
    let Y := pullback f g
    -- Local instance justification (search instability): `f` canonically makes `X` locally Noetherian, but `X` alone does not determine `f` for instance search.
    letI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
    -- Local instance justification (search instability): `pullback.snd f g` canonically makes `Y` locally Noetherian, but `Y` alone does not determine this projection.
    letI : IsLocallyNoetherian Y :=
      LocallyOfFiniteType.isLocallyNoetherian (pullback.snd f g)
    IsIsomorphic
      (Over.mk (pullback.snd X.normalizationTo (pullback.fst f g)))
      (Over.mk Y.normalizationTo))

/- Lemma 55.8.2 (3): every completed local ring of the normalization of a flat finite-type
model of a geometrically normal variety is normal. -/
@[stacks 0C2T] #check
  (AlgebraicGeometry.Scheme.Normalization.stalkCompletion_isNormal_of_geometricallyNormalModel :
    ∀ (R K : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [Field K] [Algebra R K] [IsFractionRing R K]
    (V : SchemeOverField K) [Variety V]
    (hV : SchemeOverField.geometricallyNormal V)
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R)) [Flat f] [Scheme.Hom.FiniteType f]
    (e : V ≅ Over.mk
      (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap R K))))),
    -- Local instance justification (search instability): `f` canonically makes `X` locally Noetherian, but `X` alone does not determine `f` for instance search.
    letI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
    let Xn := X.normalization
    ∀ x : Xn,
      IsNormalRing
        (AdicCompletion (maximalIdeal (Xn.presheaf.stalk x))
          (Xn.presheaf.stalk x)))

end AlgebraicGeometry.Scheme.Normalization
