module

public import ReasLib.AlgebraicGeometry.FormalDeformation.CompleteLocal.ResidueMap
public import ReasLib.AlgebraicGeometry.FormalDeformation.CompleteLocal.Smooth
public import ReasLib.RingTheory.Kaehler.ExtendedConormal

/-!
# Smooth complete local algebras with canonical cotangent identifications
-/

@[expose] public section

open CategoryTheory Algebra.H1Cotangent KaehlerDifferential

universe u

variable {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]

namespace CompleteLocalAlgCat

/-- There exists a complete local algebra with identified residue field that is
maximal-adically formally smooth over the base and whose canonical maps from
first cotangent homology to the residue-kernel cotangent and from base-changed
Kähler differentials to residue-field differentials are bijective. -/
theorem exists_formallySmooth_h1Cotangent_mapBaseChange :
    ∃ R : CompleteLocalAlgCat Λ k,
      (algebraMap Λ R.carrier).formally_smooth_for_adic (IsLocalRing.maximalIdeal R.carrier) ∧
        Function.Bijective (toKerCotangent Λ R.carrier k (algebraMap_surjective R)) ∧
        Function.Bijective (mapBaseChange Λ R.carrier k) :=
  sorry

/-- There exists a complete local algebra with identified residue field whose
restricted coyoneda is smooth and whose canonical maps from first cotangent
homology to the residue-kernel cotangent and from base-changed Kähler
differentials to residue-field differentials are bijective. -/
theorem exists_isSmooth_h1Cotangent_mapBaseChange :
    ∃ R : CompleteLocalAlgCat Λ k,
      Functor.IsSmooth (CategoryOfElements.π (restrictedCoyoneda R)) ∧
        Function.Bijective (toKerCotangent Λ R.carrier k (algebraMap_surjective R)) ∧
        Function.Bijective (mapBaseChange Λ R.carrier k) :=
  sorry

end CompleteLocalAlgCat
