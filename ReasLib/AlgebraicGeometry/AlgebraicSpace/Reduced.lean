module

public import Mathlib.AlgebraicGeometry.Properties
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.FunctorOfPoints
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.SchemeFunctor
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtaleLocal
public import ReasLib.AlgebraicGeometry.Scheme.Reduced.Etale

/-!
# Reduced algebraic spaces

An algebraic space is reduced when it admits a representable étale locally-surjective
atlas from a reduced scheme.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- An algebraic space is reduced if it admits a representable étale locally-surjective
atlas whose source is a reduced scheme. -/
@[mk_iff]
class IsReduced {S : Scheme.{u}} (X : AlgebraicSpace S) : Prop where
  /-- There is a representable étale locally-surjective atlas from a reduced scheme. -/
  exists_reduced_etaleCover :
    ∃ (U : Over S) (p : yoneda.obj U ⟶ X.functorOfPoints),
      (MorphismProperty.over (@Etale)).presheaf p ∧
        Presheaf.IsLocallySurjective (Scheme.etaleTopology.over S) p ∧
          AlgebraicGeometry.IsReduced U.left

namespace IsReduced

/-- A reduced algebraic space admits a representable étale locally-surjective atlas from a
reduced scheme. -/
theorem spec {S : Scheme.{u}} (X : AlgebraicSpace S) [IsReduced X] :
    ∃ (U : Over S) (p : yoneda.obj U ⟶ X.functorOfPoints),
      (MorphismProperty.over (@Etale)).presheaf p ∧
        Presheaf.IsLocallySurjective (Scheme.etaleTopology.over S) p ∧
          AlgebraicGeometry.IsReduced U.left := sorry

/-- A representable étale locally-surjective atlas from a reduced scheme witnesses that the
algebraic space is reduced. -/
theorem of {S : Scheme.{u}} {X : AlgebraicSpace S} {U : Over S}
    (p : yoneda.obj U ⟶ X.functorOfPoints)
    (h_etale : (MorphismProperty.over (@Etale)).presheaf p)
    (h_surj : Presheaf.IsLocallySurjective (Scheme.etaleTopology.over S) p)
    [AlgebraicGeometry.IsReduced U.left] : IsReduced X := sorry

end IsReduced

/-- A reduced scheme over `S`, viewed as an algebraic space, is reduced. -/
instance instIsReduced_ofOver {S : Scheme.{u}} (T : Over S)
    [AlgebraicGeometry.IsReduced T.left] :
    IsReduced (ofOver T) where
  exists_reduced_etaleCover :=
    ⟨T, 𝟙 (yoneda.obj T), ofOver_id_presheaf_etale T, ofOver_id_locallySurjective T,
      inferInstance⟩

/-- An algebraic space is reduced if and only if it admits a surjective étale morphism
from a reduced scheme, as a morphism of algebraic spaces. -/
theorem isReduced_iff_exists_hom {S : Scheme.{u}} (X : AlgebraicSpace S) :
    IsReduced X ↔
      ∃ (U : Over S) (f : ofOver U ⟶ X),
        (MorphismProperty.over (@Etale)).presheaf f ∧
          Presheaf.IsLocallySurjective (Scheme.etaleTopology.over S) f ∧
            AlgebraicGeometry.IsReduced U.left := sorry

/-- An algebraic space is reduced if and only if every étale morphism from a scheme to it
has reduced source. -/
theorem isReduced_iff_forallEtale {S : Scheme.{u}} (X : AlgebraicSpace S) :
    IsReduced X ↔
      forallEtale (AlgebraicGeometry.IsReduced : ObjectProperty Scheme.{u}) X :=
  sorry

/-- Reducedness is the canonical étale-local extension of reducedness of schemes. -/
theorem isReduced_iff_hasEtaleLocal {S : Scheme.{u}} (X : AlgebraicSpace S) :
    IsReduced X ↔
      hasEtaleLocal (AlgebraicGeometry.IsReduced : ObjectProperty Scheme.{u}) X := sorry

end AlgebraicGeometry.AlgebraicSpace
