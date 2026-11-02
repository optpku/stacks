/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

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
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.UniversallyClosed.Cancellation
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.Separation.Cancellation
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Separation.Representable
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.RelativeSpectrum.Affine
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Normalization.UniversallyClosed

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
    UniversallyClosed (toNormalization f) := by
  haveI : Separated (fromNormalization f) := by
    apply (separated_presheaf_iff_separated
      (relativeSpecπ_relativelyRepresentable (integralClosureAlgebra f))).mp
    refine ⟨(relativeSpecπ_presheaf_affine (integralClosureAlgebra f)).rep, ?_⟩
    intro T R g fst snd h
    haveI : IsAffineHom snd.left :=
      (relativeSpecπ_presheaf_affine (integralClosureAlgebra f)).property g fst snd h
    change AlgebraicGeometry.IsSeparated snd.left
    infer_instance
  haveI : UniversallyClosed (toNormalization f ≫ fromNormalization f) := by
    rw [toNormalization_fromNormalization]
    infer_instance
  exact UniversallyClosed.of_comp (toNormalization f) (fromNormalization f)

/-- The canonical map from the source into the relative normalization of a
universally closed quasi-separated morphism of algebraic spaces is
quasi-compact. -/
instance instQuasiCompact_toNormalization_of_universallyClosed
    {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [UniversallyClosed f] [QuasiSeparated f] :
    QuasiCompact (toNormalization f) :=
  QuasiCompact.of_universallyClosed (toNormalization f)

/-- The canonical map from the source into the relative normalization of a
universally closed quasi-separated morphism of algebraic spaces is
quasi-separated. -/
instance instQuasiSeparated_toNormalization
    {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [UniversallyClosed f] [QuasiSeparated f] :
    QuasiSeparated (toNormalization f) := by
  haveI : QuasiSeparated (toNormalization f ≫ fromNormalization f) := by
    rw [toNormalization_fromNormalization]
    infer_instance
  exact QuasiSeparated.of_comp (toNormalization f) (fromNormalization f)

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
          fromNormalization f := by
  have hn := isNormalization_normalization f
  have hs := isNormalization_toPushforwardRelativeSpec f
  letI := hn.isIntegral
  letI := hs.isIntegral
  obtain ⟨h, hh, hu⟩ := hn.existsUnique_lift
    (toPushforwardRelativeSpec f) (relativeSpecπ (pushforwardStructureQcAlgebra f))
    hs.factor.symm
  obtain ⟨k, hk, _⟩ := hs.existsUnique_lift
    (toNormalization f) (fromNormalization f) hn.factor.symm
  have hhk : h ≫ k = 𝟙 _ := by
    obtain ⟨l, _, hl⟩ := hn.existsUnique_lift
      (toNormalization f) (fromNormalization f) hn.factor.symm
    apply (hl _ ?_).trans (hl _ ?_).symm
    · exact ⟨by rw [← Category.assoc, hh.1, hk.1],
        by rw [Category.assoc, hk.2, hh.2]⟩
    · exact ⟨by simp, by simp⟩
  have hkh : k ≫ h = 𝟙 _ := by
    obtain ⟨l, _, hl⟩ := hs.existsUnique_lift
      (toPushforwardRelativeSpec f) (relativeSpecπ (pushforwardStructureQcAlgebra f))
      hs.factor.symm
    apply (hl _ ?_).trans (hl _ ?_).symm
    · exact ⟨by rw [← Category.assoc, hk.1, hh.1],
        by rw [Category.assoc, hh.2, hk.2]⟩
    · exact ⟨by simp, by simp⟩
  refine ⟨⟨h, k, hhk, hkh⟩, hh, ?_⟩
  intro e he
  apply Iso.ext
  exact hu e.hom he

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
