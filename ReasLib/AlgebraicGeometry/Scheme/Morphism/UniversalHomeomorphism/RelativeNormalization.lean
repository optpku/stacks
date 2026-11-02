/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.RelativeGluing
public import Mathlib.CategoryTheory.Category.Factorisation
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Normalization
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.UniversalHomeomorphism.Seminormalization.Affine
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.UniversalHomeomorphism.WeakNormalization

/-!
# Relative weak normalization and seminormalization

This module defines the factorization categories for relative weak normalization and
seminormalization and records their initial objects and compatibility with restriction to open
subschemes.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.ObjectProperty
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Hom

/-- The property of a factorization whose second map is a universal homeomorphism. -/
abbrev relativeWeakNormalizationFactorizationProperty {X Y : Scheme.{u}} (f : Y ⟶ X) :
    ObjectProperty (CategoryTheory.Factorisation f) :=
  fun F ↦ UniversalHomeomorphism F.π

/-- A factorization has the relative weak-normalization property exactly when its second map is a
universal homeomorphism. -/
theorem relativeWeakNormalizationFactorizationProperty_iff
    {X Y : Scheme.{u}} (f : Y ⟶ X) (F : CategoryTheory.Factorisation f) :
    relativeWeakNormalizationFactorizationProperty f F ↔ UniversalHomeomorphism F.π :=
  Iff.rfl

/-- The category of factorizations whose second map is a universal homeomorphism. -/
abbrev RelativeWeakNormalizationFactorizations {X Y : Scheme.{u}} (f : Y ⟶ X) :
    Type (u + 1) :=
  (relativeWeakNormalizationFactorizationProperty f).FullSubcategory

/-- The second map of a relative weak-normalization factorization is a universal
homeomorphism. -/
theorem RelativeWeakNormalizationFactorizations.property
    {X Y : Scheme.{u}} {f : Y ⟶ X} (F : RelativeWeakNormalizationFactorizations f) :
    UniversalHomeomorphism F.1.π :=
  CategoryTheory.ObjectProperty.FullSubcategory.property F

/-- The property of a factorization whose second map is a universal homeomorphism inducing
isomorphisms on all residue fields. -/
abbrev relativeSeminormalizationFactorizationProperty {X Y : Scheme.{u}} (f : Y ⟶ X) :
    ObjectProperty (CategoryTheory.Factorisation f) :=
  fun F ↦
    UniversalHomeomorphism F.π ∧
      ∀ x : F.mid, IsIso (Scheme.Hom.residueFieldMap F.π x)

/-- A factorization has the relative seminormalization property exactly when its second map is a
universal homeomorphism inducing isomorphisms on all residue fields. -/
theorem relativeSeminormalizationFactorizationProperty_iff
    {X Y : Scheme.{u}} (f : Y ⟶ X) (F : CategoryTheory.Factorisation f) :
    relativeSeminormalizationFactorizationProperty f F ↔
      UniversalHomeomorphism F.π ∧
        ∀ x : F.mid, IsIso (Scheme.Hom.residueFieldMap F.π x) :=
  Iff.rfl

/-- The category of factorizations whose second map is a universal homeomorphism inducing
isomorphisms on all residue fields. -/
abbrev RelativeSeminormalizationFactorizations {X Y : Scheme.{u}} (f : Y ⟶ X) :
    Type (u + 1) :=
  (relativeSeminormalizationFactorizationProperty f).FullSubcategory

/-- The second map of a relative seminormalization factorization is a universal homeomorphism
inducing isomorphisms on all residue fields. -/
theorem RelativeSeminormalizationFactorizations.property
    {X Y : Scheme.{u}} {f : Y ⟶ X} (F : RelativeSeminormalizationFactorizations f) :
    UniversalHomeomorphism F.1.π ∧
      ∀ x : F.1.mid, IsIso (Scheme.Hom.residueFieldMap F.1.π x) :=
  CategoryTheory.ObjectProperty.FullSubcategory.property F

/-- A relative weak normalization is an initial factorization whose map to the target is a
universal homeomorphism. -/
abbrev RelativeWeakNormalization {X Y : Scheme.{u}} (f : Y ⟶ X) : Type (u + 1) :=
  { F : RelativeWeakNormalizationFactorizations f // Nonempty (IsInitial F) }

namespace RelativeWeakNormalization

/-- The underlying factorization of a relative weak normalization. -/
def toFactorisation {X Y : Scheme.{u}} {f : Y ⟶ X} (W : RelativeWeakNormalization f) :
    CategoryTheory.Factorisation f :=
  W.1.1

/-- The intermediate scheme in a relative weak-normalization factorization. -/
def obj {X Y : Scheme.{u}} {f : Y ⟶ X} (W : RelativeWeakNormalization f) : Scheme.{u} :=
  W.toFactorisation.mid

/-- The morphism from the source to a relative weak normalization. -/
def fromSource {X Y : Scheme.{u}} {f : Y ⟶ X} (W : RelativeWeakNormalization f) :
    Y ⟶ W.obj :=
  W.toFactorisation.ι

/-- The universal homeomorphism from a relative weak normalization to the target. -/
def toTarget {X Y : Scheme.{u}} {f : Y ⟶ X} (W : RelativeWeakNormalization f) :
    W.obj ⟶ X :=
  W.toFactorisation.π

/-- The original morphism is the composite through a relative weak normalization. -/
theorem fromSource_comp_toTarget {X Y : Scheme.{u}} {f : Y ⟶ X}
    (W : RelativeWeakNormalization f) : W.fromSource ≫ W.toTarget = f :=
  W.toFactorisation.ι_π

/-- The morphism from a relative weak normalization to the target is a universal
homeomorphism. -/
theorem isUniversalHomeomorphism_toTarget {X Y : Scheme.{u}} {f : Y ⟶ X}
    (W : RelativeWeakNormalization f) : UniversalHomeomorphism W.toTarget :=
  RelativeWeakNormalizationFactorizations.property W.1

/-- A relative weak normalization is initial among relative weak-normalization
factorizations. -/
theorem nonempty_isInitial {X Y : Scheme.{u}} {f : Y ⟶ X}
    (W : RelativeWeakNormalization f) : Nonempty (IsInitial W.1) :=
  W.2

end RelativeWeakNormalization

/-- A relative seminormalization is an initial factorization whose map to the target is a
universal homeomorphism inducing isomorphisms on all residue fields. -/
abbrev RelativeSeminormalization {X Y : Scheme.{u}} (f : Y ⟶ X) : Type (u + 1) :=
  { F : RelativeSeminormalizationFactorizations f // Nonempty (IsInitial F) }

namespace RelativeSeminormalization

/-- The underlying factorization of a relative seminormalization. -/
def toFactorisation {X Y : Scheme.{u}} {f : Y ⟶ X} (S : RelativeSeminormalization f) :
    CategoryTheory.Factorisation f :=
  S.1.1

/-- The intermediate scheme in a relative seminormalization factorization. -/
def obj {X Y : Scheme.{u}} {f : Y ⟶ X} (S : RelativeSeminormalization f) : Scheme.{u} :=
  S.toFactorisation.mid

/-- The morphism from the source to a relative seminormalization. -/
def fromSource {X Y : Scheme.{u}} {f : Y ⟶ X} (S : RelativeSeminormalization f) :
    Y ⟶ S.obj :=
  S.toFactorisation.ι

/-- The universal homeomorphism from a relative seminormalization to the target. -/
def toTarget {X Y : Scheme.{u}} {f : Y ⟶ X} (S : RelativeSeminormalization f) :
    S.obj ⟶ X :=
  S.toFactorisation.π

/-- The original morphism is the composite through a relative seminormalization. -/
theorem fromSource_comp_toTarget {X Y : Scheme.{u}} {f : Y ⟶ X}
    (S : RelativeSeminormalization f) : S.fromSource ≫ S.toTarget = f :=
  S.toFactorisation.ι_π

/-- The morphism from a relative seminormalization to the target is a universal homeomorphism
inducing isomorphisms on all residue fields. -/
theorem toTarget_property {X Y : Scheme.{u}} {f : Y ⟶ X}
    (S : RelativeSeminormalization f) :
    UniversalHomeomorphism S.toTarget ∧
      ∀ x : S.obj, IsIso (Scheme.Hom.residueFieldMap S.toTarget x) :=
  RelativeSeminormalizationFactorizations.property S.1

/-- A relative seminormalization is initial among relative seminormalization factorizations. -/
theorem nonempty_isInitial {X Y : Scheme.{u}} {f : Y ⟶ X}
    (S : RelativeSeminormalization f) : Nonempty (IsInitial S.1) :=
  S.2

end RelativeSeminormalization

/-- For a quasi-compact, quasi-separated, dominant morphism, the category of relative weak
normalization factorizations has an initial object. -/
instance instHasInitialRelativeWeakNormalizationFactorizations
    {X Y : Scheme.{u}} (f : Y ⟶ X) [QuasiCompact f] [QuasiSeparated f] [IsDominant f] :
    HasInitial (RelativeWeakNormalizationFactorizations f) := sorry

/-- For a quasi-compact, quasi-separated, dominant morphism, the category of relative
seminormalization factorizations has an initial object. -/
instance instHasInitialRelativeSeminormalizationFactorizations
    {X Y : Scheme.{u}} (f : Y ⟶ X) [QuasiCompact f] [QuasiSeparated f] [IsDominant f] :
    HasInitial (RelativeSeminormalizationFactorizations f) := sorry

/-- The relative weak-normalization factorization of a quasi-compact, quasi-separated, dominant
morphism commutes with restriction to an open subscheme of the target. -/
theorem relativeWeakNormalization_openRestrict_exists
    {X Y : Scheme.{u}} (f : Y ⟶ X) [QuasiCompact f] [QuasiSeparated f] [IsDominant f]
    (U : X.Opens) :
    ∃ (WU : RelativeWeakNormalizationFactorizations (f ∣_ U))
        (toGlobal : WU.1.mid ⟶ (⊥_ (RelativeWeakNormalizationFactorizations f)).1.mid),
      IsPullback toGlobal WU.1.π
          (⊥_ (RelativeWeakNormalizationFactorizations f)).1.π U.ι ∧
        WU.1.ι ≫ toGlobal =
          (f ⁻¹ᵁ U).ι ≫ (⊥_ (RelativeWeakNormalizationFactorizations f)).1.ι ∧
        Nonempty (IsInitial WU) := sorry

/-- The relative seminormalization factorization of a quasi-compact, quasi-separated, dominant
morphism commutes with restriction to an open subscheme of the target. -/
theorem relativeSeminormalization_openRestrict_exists
    {X Y : Scheme.{u}} (f : Y ⟶ X) [QuasiCompact f] [QuasiSeparated f] [IsDominant f]
    (U : X.Opens) :
    ∃ (SU : RelativeSeminormalizationFactorizations (f ∣_ U))
        (toGlobal : SU.1.mid ⟶ (⊥_ (RelativeSeminormalizationFactorizations f)).1.mid),
      IsPullback toGlobal SU.1.π
          (⊥_ (RelativeSeminormalizationFactorizations f)).1.π U.ι ∧
        SU.1.ι ≫ toGlobal =
          (f ⁻¹ᵁ U).ι ≫ (⊥_ (RelativeSeminormalizationFactorizations f)).1.ι ∧
        Nonempty (IsInitial SU) := sorry

end AlgebraicGeometry.Scheme.Hom
