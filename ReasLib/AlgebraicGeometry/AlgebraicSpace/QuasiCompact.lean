
module

public import Mathlib.CategoryTheory.MorphismProperty.Limits
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.FunctorOfPoints

/-!
# Quasi-compact algebraic spaces

An algebraic space is quasi-compact when it admits a representable étale locally-surjective
atlas from a quasi-compact scheme.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits MorphismProperty

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- An algebraic space is quasi-compact if it admits a representable étale locally-surjective
atlas whose source is a quasi-compact scheme. -/
@[mk_iff]
class IsQuasiCompact {S : Scheme.{u}} (X : AlgebraicSpace S) : Prop where
  /-- There is a representable étale locally-surjective atlas from a quasi-compact scheme. -/
  exists_compact_etaleCover :
    ∃ (U : Over S) (p : yoneda.obj U ⟶ X.functorOfPoints),
      (MorphismProperty.over (@Etale)).presheaf p ∧
        Presheaf.IsLocallySurjective (Scheme.etaleTopology.over S) p ∧
          CompactSpace U.left

namespace IsQuasiCompact

/-- A quasi-compact algebraic space admits a representable étale locally-surjective atlas from a
quasi-compact scheme. -/
theorem spec {S : Scheme.{u}} (X : AlgebraicSpace S) [IsQuasiCompact X] :
    ∃ (U : Over S) (p : yoneda.obj U ⟶ X.functorOfPoints),
      (MorphismProperty.over (@Etale)).presheaf p ∧
        Presheaf.IsLocallySurjective (Scheme.etaleTopology.over S) p ∧
          CompactSpace U.left := sorry

/-- A representable étale locally-surjective atlas from a quasi-compact scheme witnesses that the
algebraic space is quasi-compact. -/
theorem of {S : Scheme.{u}} {X : AlgebraicSpace S} {U : Over S}
    (p : yoneda.obj U ⟶ X.functorOfPoints)
    (h_etale : (MorphismProperty.over (@Etale)).presheaf p)
    (h_surj : Presheaf.IsLocallySurjective (Scheme.etaleTopology.over S) p)
    [CompactSpace U.left] : IsQuasiCompact X := sorry

end IsQuasiCompact

/-- A quasi-compact scheme over `S`, viewed as an algebraic space, is quasi-compact. -/
instance instIsQuasiCompact_ofOver {S : Scheme.{u}} (T : Over S) [CompactSpace T.left] :
    IsQuasiCompact (ofOver T) where
  exists_compact_etaleCover :=
    ⟨T, 𝟙 (yoneda.obj T), ofOver_id_presheaf_etale T, ofOver_id_locallySurjective T,
      inferInstance⟩

/-- An algebraic space is quasi-compact if and only if it admits a surjective étale morphism
from a quasi-compact scheme, as a morphism of algebraic spaces. -/
theorem isQuasiCompact_iff_exists_hom {S : Scheme.{u}} (X : AlgebraicSpace S) :
    IsQuasiCompact X ↔
      ∃ (U : Over S) (f : ofOver U ⟶ X),
        (MorphismProperty.over (@Etale)).presheaf f ∧
          Presheaf.IsLocallySurjective (Scheme.etaleTopology.over S) f ∧
            CompactSpace U.left := sorry

/-- The morphism property of algebraic spaces whose source is quasi-compact whenever the
target is quasi-compact. -/
def quasiCompactSource {S : Scheme.{u}} : MorphismProperty (AlgebraicSpace S) :=
  fun {X Y} _ ↦ IsQuasiCompact Y → IsQuasiCompact X

/-- A morphism has the `quasiCompactSource` property if and only if quasi-compactness of the
target implies quasi-compactness of the source. -/
theorem quasiCompactSource_iff {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    quasiCompactSource f ↔ (IsQuasiCompact Y → IsQuasiCompact X) := sorry

/-- A morphism `f : X ⟶ Y` of algebraic spaces over `S` is quasi-compact if for every
quasi-compact algebraic space `Z` and morphism `Z ⟶ Y`, the fibre product `Z ×_Y X` is
quasi-compact. -/
@[mk_iff]
class QuasiCompact {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) : Prop where
  /-- The vertex of an `IsPullback` square for `f` is quasi-compact whenever the test
  object is quasi-compact. -/
  pullback_isQuasiCompact {Z P : AlgebraicSpace S} {g : Z ⟶ Y} {pZ : P ⟶ Z} {pX : P ⟶ X}
    [IsQuasiCompact Z] : IsPullback pZ pX g f → IsQuasiCompact P

namespace QuasiCompact

/-- The identity morphism of an algebraic space is quasi-compact. -/
instance id {S : Scheme.{u}} {X : AlgebraicSpace S} : QuasiCompact (𝟙 X) := sorry

/-- An isomorphism of algebraic spaces is quasi-compact. -/
instance of_isIso {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) [IsIso f] :
    QuasiCompact f := sorry

/-- A quasi-compact morphism pulls quasi-compact algebraic spaces back to quasi-compact
algebraic spaces along any `IsPullback` square. -/
theorem spec {S : Scheme.{u}} {X Y Z P : AlgebraicSpace S} {f : X ⟶ Y} {g : Z ⟶ Y}
    {pZ : P ⟶ Z} {pX : P ⟶ X} [QuasiCompact f] [IsQuasiCompact Z]
    (h : IsPullback pZ pX g f) : IsQuasiCompact P := sorry

/-- The source of a quasi-compact morphism is quasi-compact whenever the target is
quasi-compact. -/
theorem isQuasiCompact {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [QuasiCompact f] [IsQuasiCompact Y] : IsQuasiCompact X := sorry

end QuasiCompact

/-- A morphism of algebraic spaces is quasi-compact if and only if `quasiCompactSource`
holds after every base change. -/
theorem quasiCompact_iff_universally {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    QuasiCompact f ↔ universally quasiCompactSource f := sorry

/-- The chosen fibre product of a quasi-compact morphism with a quasi-compact algebraic
space is quasi-compact. -/
instance instIsQuasiCompact_pullback {S : Scheme.{u}} {X Y Z : AlgebraicSpace S}
    (f : X ⟶ Y) (g : Z ⟶ Y) [QuasiCompact f] [IsQuasiCompact Z] [HasPullback f g] :
    IsQuasiCompact (pullback f g) := sorry

/-- Quasi-compact morphisms of algebraic spaces are closed under composition. -/
instance quasiCompact_isStableUnderComposition {S : Scheme.{u}} :
    MorphismProperty.IsStableUnderComposition
      (@QuasiCompact S : MorphismProperty (AlgebraicSpace S)) := sorry

/-- The composition of quasi-compact morphisms of algebraic spaces is quasi-compact. -/
instance quasiCompact_comp {S : Scheme.{u}} {X Y Z : AlgebraicSpace S}
    (f : X ⟶ Y) (g : Y ⟶ Z) [QuasiCompact f] [QuasiCompact g] :
    QuasiCompact (f ≫ g) :=
  MorphismProperty.comp_mem (@QuasiCompact S) f g inferInstance inferInstance

end AlgebraicGeometry.AlgebraicSpace
