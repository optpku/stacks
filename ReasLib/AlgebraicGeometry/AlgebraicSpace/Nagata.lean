module

public import ReasLib.AlgebraicGeometry.Scheme.Normal.Nagata.Basic
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Noetherian
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtaleLocal

/-!
# Nagata algebraic spaces

An algebraic space is Nagata when it admits a representable étale locally-surjective atlas
from a Nagata scheme, transferring `Scheme.Nagata` along étale atlases.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- An algebraic space is Nagata if it admits a representable étale locally-surjective atlas
whose source is a Nagata scheme. -/
@[mk_iff]
class IsNagata {S : Scheme.{u}} (X : AlgebraicSpace S) : Prop where
  /-- There is a representable étale locally-surjective atlas from a Nagata scheme. -/
  exists_nagata_etaleCover :
    ∃ (U : Over S) (p : yoneda.obj U ⟶ X.functorOfPoints),
      (MorphismProperty.over (@Etale)).presheaf p ∧
        Presheaf.IsLocallySurjective (Scheme.etaleTopology.over S) p ∧
          Scheme.Nagata U.left

namespace IsNagata

/-- A Nagata algebraic space admits a representable étale locally-surjective atlas from a
Nagata scheme. -/
theorem spec {S : Scheme.{u}} (X : AlgebraicSpace S) [IsNagata X] :
    ∃ (U : Over S) (p : yoneda.obj U ⟶ X.functorOfPoints),
      (MorphismProperty.over (@Etale)).presheaf p ∧
        Presheaf.IsLocallySurjective (Scheme.etaleTopology.over S) p ∧
          Scheme.Nagata U.left := sorry

/-- A representable étale locally-surjective atlas from a Nagata scheme witnesses that the
algebraic space is Nagata. -/
theorem of {S : Scheme.{u}} {X : AlgebraicSpace S} {U : Over S}
    (p : yoneda.obj U ⟶ X.functorOfPoints)
    (h_etale : (MorphismProperty.over (@Etale)).presheaf p)
    (h_surj : Presheaf.IsLocallySurjective (Scheme.etaleTopology.over S) p)
    [Scheme.Nagata U.left] : IsNagata X := sorry

/-- An algebraic space is Nagata if and only if it admits a surjective étale morphism from a
Nagata scheme, as a morphism of algebraic spaces. -/
theorem iff_exists_hom {S : Scheme.{u}} (X : AlgebraicSpace S) :
    IsNagata X ↔
      ∃ (U : Over S) (f : ofOver U ⟶ X),
        (MorphismProperty.over (@Etale)).presheaf f ∧
          Presheaf.IsLocallySurjective (Scheme.etaleTopology.over S) f ∧
            Scheme.Nagata U.left := sorry

/-- An algebraic space is Nagata if and only if some surjective étale scheme atlas is a Nagata
scheme. -/
theorem iff_existsSurjectiveEtale {S : Scheme.{u}} (X : AlgebraicSpace S) :
    IsNagata X ↔
      existsSurjectiveEtale (Scheme.Nagata : ObjectProperty Scheme.{u}) X := sorry

/-- An algebraic space is Nagata if and only if every étale morphism from a scheme has Nagata
source. -/
theorem iff_forallEtale {S : Scheme.{u}} (X : AlgebraicSpace S) :
    IsNagata X ↔ forallEtale (Scheme.Nagata : ObjectProperty Scheme.{u}) X := sorry

end IsNagata

/-- A Nagata scheme over `S`, viewed as an algebraic space, is Nagata. -/
instance instIsNagata_ofOver {S : Scheme.{u}} (T : Over S) [Scheme.Nagata T.left] :
    IsNagata (ofOver T) where
  exists_nagata_etaleCover :=
    ⟨T, 𝟙 (yoneda.obj T), ofOver_id_presheaf_etale T, ofOver_id_locallySurjective T,
      inferInstance⟩

/-- A Nagata algebraic space is locally Noetherian. -/
instance instIsLocallyNoetherian_of_isNagata {S : Scheme.{u}} (X : AlgebraicSpace S)
    [IsNagata X] : IsLocallyNoetherian X := sorry

end AlgebraicGeometry.AlgebraicSpace
