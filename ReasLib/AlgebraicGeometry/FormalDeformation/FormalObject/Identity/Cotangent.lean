module

public import ReasLib.AlgebraicGeometry.FormalDeformation.FormalObject.Identity
public import ReasLib.AlgebraicGeometry.FormalDeformation.FormalObject.Existence
public import ReasLib.AlgebraicGeometry.FormalDeformation.CompleteLocal.Smooth
public import ReasLib.AlgebraicGeometry.FormalDeformation.CompleteLocal.ResidueMap
public import ReasLib.RingTheory.Kaehler.ExtendedConormal

/-!
# Cotangent comparisons for identity formal objects

Minimal versal objects of the lifted identity projection have formally smooth
bases and canonical cotangent identifications. Conversely these identifications
make the truncation object minimal versal, and determine its base up to isomorphism.
-/

@[expose] public section

open CategoryTheory IsLocalRing Algebra.H1Cotangent KaehlerDifferential
open FormalObject

universe u

variable {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]

namespace FormalObject

/-- The lifted identity projection admits a minimal versal formal object with
orbit-bijective differential. -/
theorem exists_isMinimalVersal_identity :
    ∃ ξ : FormalObject (ArtinianLocalAlgCat.identityDown Λ k),
      IsMinimalVersal ξ ∧ BijectiveDifferentialOnOrbits ξ :=
  sorry

/-- The base of a versal formal object of the lifted identity projection is
formally smooth in its maximal-ideal-adic topology. -/
theorem formallySmooth_base_identity
    (ξ : FormalObject (ArtinianLocalAlgCat.identityDown Λ k)) [IsVersal ξ] :
    (algebraMap Λ ξ.base.carrier).formally_smooth_for_adic (maximalIdeal ξ.base.carrier) :=
  sorry

/-- Orbit bijectivity for an identity formal object makes restriction of
residue-field derivations to its complete local base bijective. -/
theorem bijective_compAlgebraMap_identity
    (ξ : FormalObject (ArtinianLocalAlgCat.identityDown Λ k))
    (h : BijectiveDifferentialOnOrbits ξ) :
    Function.Bijective fun D : Derivation Λ k k ↦ D.compAlgebraMap ξ.base.carrier :=
  sorry

/-- Orbit bijectivity for an identity formal object makes the canonical
base-change map on Kähler differentials bijective. -/
theorem bijective_mapBaseChange_identity
    (ξ : FormalObject (ArtinianLocalAlgCat.identityDown Λ k))
    (h : BijectiveDifferentialOnOrbits ξ) :
    Function.Bijective (mapBaseChange Λ ξ.base.carrier k) :=
  sorry

/-- For a versal identity formal object with orbit-bijective differential, the
canonical map from first cotangent homology to the residue-kernel cotangent is bijective. -/
theorem bijective_toKerCotangent_identity
    (ξ : FormalObject (ArtinianLocalAlgCat.identityDown Λ k)) [IsVersal ξ]
    (h : BijectiveDifferentialOnOrbits ξ) :
    Function.Bijective
      (toKerCotangent Λ ξ.base.carrier k (CompleteLocalAlgCat.algebraMap_surjective ξ.base)) :=
  sorry

end FormalObject

namespace ArtinianLocalAlgCat

/-- A maximal-adically formally smooth complete local algebra with bijective
canonical cotangent comparison maps has a minimal versal truncation formal object
with orbit-bijective differential. -/
theorem isMinimalVersal_truncationFormalObject (R : CompleteLocalAlgCat Λ k)
    (h_smooth :
      (algebraMap Λ R.carrier).formally_smooth_for_adic (maximalIdeal R.carrier))
    (h_h1 :
      Function.Bijective (toKerCotangent Λ R.carrier k (CompleteLocalAlgCat.algebraMap_surjective R)))
    (h_omega : Function.Bijective (mapBaseChange Λ R.carrier k)) :
    FormalObject.IsMinimalVersal (truncationFormalObject Λ k R) ∧
      FormalObject.BijectiveDifferentialOnOrbits (truncationFormalObject Λ k R) :=
  sorry

/-- A maximal-adically formally smooth complete local algebra with bijective
canonical cotangent comparison maps is isomorphic to the base of any minimal
versal identity formal object with orbit-bijective differential. -/
theorem nonempty_iso_base_identity (R : CompleteLocalAlgCat Λ k)
    (h_smooth :
      (algebraMap Λ R.carrier).formally_smooth_for_adic (maximalIdeal R.carrier))
    (h_h1 :
      Function.Bijective (toKerCotangent Λ R.carrier k (CompleteLocalAlgCat.algebraMap_surjective R)))
    (h_omega : Function.Bijective (mapBaseChange Λ R.carrier k))
    (ξ : FormalObject (identityDown Λ k)) [FormalObject.IsMinimalVersal ξ]
    (h : FormalObject.BijectiveDifferentialOnOrbits ξ) :
    Nonempty (R ≅ ξ.base) :=
  sorry

end ArtinianLocalAlgCat
