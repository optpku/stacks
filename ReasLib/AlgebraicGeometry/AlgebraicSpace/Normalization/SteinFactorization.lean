module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Normalization.UniversalProperty
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.UniversallyClosed.QuasiCompact
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Surjective
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.RelativeSpectrum.Factorization
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Normalization.BaseChange
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Pullback
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.QuasiCompact.BaseChange
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Separation.BaseChange
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.Flat

/-!
# Stein factorization through relative normalization

For a universally closed quasi-separated morphism of algebraic spaces, the
canonical map to the relative normalization is universally closed,
quasi-compact, quasi-separated and surjective, and its structure-sheaf map is
an isomorphism. The relative normalization is uniquely identified with the
relative spectrum of the pushed-forward structure sheaf, and the factorization
commutes with flat base change.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace Limits

universe u

namespace AlgebraicGeometry.AlgebraicSpace

namespace Hom

/-- The canonical map from the source into the relative normalization of a
universally closed quasi-separated morphism of algebraic spaces is universally
closed. -/
instance instUniversallyClosed_toNormalization
    {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [UniversallyClosed f] [QuasiSeparated f] :
    UniversallyClosed (toNormalization f) :=
  sorry

/-- The canonical map from the source into the relative normalization of a
universally closed quasi-separated morphism of algebraic spaces is
quasi-compact. -/
instance instQuasiCompact_toNormalization_of_universallyClosed
    {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [UniversallyClosed f] [QuasiSeparated f] :
    QuasiCompact (toNormalization f) :=
  sorry

/-- The canonical map from the source into the relative normalization of a
universally closed quasi-separated morphism of algebraic spaces is
quasi-separated. -/
instance instQuasiSeparated_toNormalization
    {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [UniversallyClosed f] [QuasiSeparated f] :
    QuasiSeparated (toNormalization f) :=
  sorry

/-- The canonical map from the source into the relative normalization of a
universally closed quasi-separated morphism of algebraic spaces is surjective. -/
instance instSurjective_toNormalization
    {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [UniversallyClosed f] [QuasiSeparated f] :
    Surjective (toNormalization f) :=
  sorry

/-- The structure-sheaf map of the canonical map into the relative
normalization of a universally closed quasi-separated morphism of algebraic
spaces is an isomorphism. -/
instance instIsIso_commRingStructureSheafMap_toNormalization
    {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [UniversallyClosed f] [QuasiSeparated f] :
    IsIso (commStructureSheafMap (toNormalization f)) :=
  sorry

/-- The relative normalization of a universally closed quasi-separated morphism
of algebraic spaces is uniquely isomorphic over the target to the relative
spectrum of the pushed-forward structure sheaf. -/
theorem existsUnique_iso_toPushforwardRelativeSpec
    {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [UniversallyClosed f] [QuasiSeparated f] :
    ∃! e : normalization f ≅ relativeSpec (pushforwardStructureQcAlgebra f),
      toNormalization f ≫ e.hom = toPushforwardRelativeSpec f ∧
        e.hom ≫ relativeSpecπ (pushforwardStructureQcAlgebra f) =
          fromNormalization f :=
  sorry

/-- After flat base change, the relative normalization of the pulled-back
morphism is uniquely isomorphic to the pullback of the relative normalization,
compatibly with the maps from the pulled-back source and the structure
morphisms to the new base. -/
theorem existsUnique_isIso_normalizationPullback_of_flat
    {S : Scheme.{u}} {X Y Z : AlgebraicSpace S} (f : X ⟶ Y) (g : Z ⟶ Y)
    [UniversallyClosed f] [QuasiSeparated f] [Flat g] :
    ∃! h : normalization (pullback.snd f g) ⟶
        pullback (fromNormalization f) g,
      toNormalization (pullback.snd f g) ≫ h =
          pullbackToNormalization f g ∧
        h ≫ pullback.snd (fromNormalization f) g =
          fromNormalization (pullback.snd f g) ∧
        IsIso h :=
  sorry

end Hom

end AlgebraicGeometry.AlgebraicSpace
