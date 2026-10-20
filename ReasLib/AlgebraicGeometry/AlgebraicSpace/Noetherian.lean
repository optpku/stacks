module

public import Mathlib.AlgebraicGeometry.Noetherian
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.FunctorOfPoints
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Separation.Absolute.Relative
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.QuasiCompact

/-!
# Noetherian algebraic spaces

An algebraic space is locally Noetherian when it admits a representable étale locally-surjective
atlas from a locally Noetherian scheme. It is Noetherian when it is quasi-compact, absolutely
quasi-separated, and locally Noetherian, independently of the chosen base scheme.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- An algebraic space is locally Noetherian if it admits a representable étale locally-surjective
atlas whose source is a locally Noetherian scheme. -/
@[mk_iff]
class IsLocallyNoetherian {S : Scheme.{u}} (X : AlgebraicSpace S) : Prop where
  /-- There is a representable étale locally-surjective atlas from a locally Noetherian scheme. -/
  exists_noetherian_etaleCover :
    ∃ (U : Over S) (p : yoneda.obj U ⟶ X.functorOfPoints),
      (MorphismProperty.over (@Etale)).presheaf p ∧
        Presheaf.IsLocallySurjective (Scheme.etaleTopology.over S) p ∧
          AlgebraicGeometry.IsLocallyNoetherian U.left

namespace IsLocallyNoetherian

/-- A locally Noetherian algebraic space admits a representable étale locally-surjective atlas from
a locally Noetherian scheme. -/
theorem spec {S : Scheme.{u}} (X : AlgebraicSpace S) [IsLocallyNoetherian X] :
    ∃ (U : Over S) (p : yoneda.obj U ⟶ X.functorOfPoints),
      (MorphismProperty.over (@Etale)).presheaf p ∧
        Presheaf.IsLocallySurjective (Scheme.etaleTopology.over S) p ∧
          AlgebraicGeometry.IsLocallyNoetherian U.left := sorry

/-- A representable étale locally-surjective atlas from a locally Noetherian scheme witnesses that
the algebraic space is locally Noetherian. -/
theorem of {S : Scheme.{u}} {X : AlgebraicSpace S} {U : Over S}
    (p : yoneda.obj U ⟶ X.functorOfPoints)
    (h_etale : (MorphismProperty.over (@Etale)).presheaf p)
    (h_surj : Presheaf.IsLocallySurjective (Scheme.etaleTopology.over S) p)
    [AlgebraicGeometry.IsLocallyNoetherian U.left] : IsLocallyNoetherian X := sorry

end IsLocallyNoetherian

/-- A locally Noetherian scheme over `S`, viewed as an algebraic space, is locally Noetherian. -/
instance instIsLocallyNoetherian_ofOver {S : Scheme.{u}} (T : Over S)
    [AlgebraicGeometry.IsLocallyNoetherian T.left] :
    IsLocallyNoetherian (ofOver T) where
  exists_noetherian_etaleCover :=
    ⟨T, 𝟙 (yoneda.obj T), ofOver_id_presheaf_etale T, ofOver_id_locallySurjective T,
      inferInstance⟩

/-- An algebraic space is locally Noetherian if and only if it admits a surjective étale morphism
from a locally Noetherian scheme, as a morphism of algebraic spaces. -/
theorem isLocallyNoetherian_iff_exists_hom {S : Scheme.{u}} (X : AlgebraicSpace S) :
    IsLocallyNoetherian X ↔
      ∃ (U : Over S) (f : ofOver U ⟶ X),
        (MorphismProperty.over (@Etale)).presheaf f ∧
          Presheaf.IsLocallySurjective (Scheme.etaleTopology.over S) f ∧
            AlgebraicGeometry.IsLocallyNoetherian U.left := sorry

/-- An algebraic space is Noetherian if it is quasi-compact, absolutely quasi-separated, and
locally Noetherian. -/
@[mk_iff]
class IsNoetherian {S : Scheme.{u}} (X : AlgebraicSpace S) : Prop extends
    IsQuasiCompact X, IsAbsolutelyQuasiSeparated X, IsLocallyNoetherian X

namespace IsNoetherian

/-- A Noetherian algebraic space is quasi-compact, absolutely quasi-separated, and locally
Noetherian. -/
theorem spec {S : Scheme.{u}} (X : AlgebraicSpace S) [IsNoetherian X] :
    IsQuasiCompact X ∧ IsAbsolutelyQuasiSeparated X ∧ IsLocallyNoetherian X := sorry

/-- Quasi-compactness, absolute quasi-separatedness, and local Noetherianity together witness
that an algebraic space is Noetherian. -/
theorem of {S : Scheme.{u}} {X : AlgebraicSpace S}
    [IsQuasiCompact X] [IsAbsolutelyQuasiSeparated X] [IsLocallyNoetherian X] :
    IsNoetherian X := sorry

end IsNoetherian

/-- A Noetherian scheme over `S`, viewed as an algebraic space, is Noetherian. -/
instance instIsNoetherian_ofOver {S : Scheme.{u}} (T : Over S)
    [AlgebraicGeometry.IsNoetherian T.left] : IsNoetherian (ofOver T) where
  toIsQuasiCompact := instIsQuasiCompact_ofOver T
  toIsAbsolutelyQuasiSeparated := sorry
  toIsLocallyNoetherian := instIsLocallyNoetherian_ofOver T

end AlgebraicGeometry.AlgebraicSpace
