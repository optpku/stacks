/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Category.CommAlgCat.Basic
public import Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.CategoryTheory.Limits.Shapes.Terminal
public import Mathlib.CategoryTheory.MorphismProperty.Comma
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.UniversalHomeomorphism
public import ReasLib.AlgebraicGeometry.Scheme.Seminormal
public import ReasLib.RingTheory.Seminormal

/-!
# Absolute weak normalization and seminormalization

This module defines categories of commutative algebras and schemes whose structure morphisms are
universal homeomorphisms, with or without residue-field isomorphisms, and records their
normalization objects and universal properties.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.ObjectProperty

universe u

namespace AlgebraicGeometry

/-- The property of an `A`-algebra whose affine spectrum map to `Spec A` is a universal
homeomorphism. -/
@[stacks 0EUR]
abbrev absoluteWeakNormalizationAlgebraProperty (A : Type u) [CommRing A] :
    ObjectProperty (CommAlgCat.{u} A) :=
  fun B : CommAlgCat.{u} A ↦
    UniversalHomeomorphism (Spec.map (CommRingCat.ofHom (algebraMap A B)))

/-- An `A`-algebra has the absolute-weak-normalization property exactly when its affine spectrum
map to `Spec A` is a universal homeomorphism. -/
theorem absoluteWeakNormalizationAlgebraProperty_iff
    (A : Type u) [CommRing A] (B : CommAlgCat.{u} A) :
    absoluteWeakNormalizationAlgebraProperty A B ↔
      UniversalHomeomorphism (Spec.map (CommRingCat.ofHom (algebraMap A B))) := sorry

/-- The category of `A`-algebras whose affine spectrum maps are universal homeomorphisms. -/
@[stacks 0EUR]
abbrev AbsoluteWeakNormalizationAlgebras (A : Type u) [CommRing A] : Type (u + 1) :=
  (absoluteWeakNormalizationAlgebraProperty A).FullSubcategory

/-- Every object in the absolute-weak-normalization algebra category has a universally
homeomorphic affine spectrum map. -/
theorem AbsoluteWeakNormalizationAlgebras.property
    (A : Type u) [CommRing A] (B : AbsoluteWeakNormalizationAlgebras A) :
    UniversalHomeomorphism (Spec.map (CommRingCat.ofHom (algebraMap A (B.1 : Type u)))) := sorry

/-- The property of an `A`-algebra whose affine spectrum map to `Spec A` is a universal
homeomorphism and induces isomorphisms on all residue fields. -/
@[stacks 0EUR]
abbrev seminormalizationAlgebraProperty (A : Type u) [CommRing A] :
    ObjectProperty (CommAlgCat.{u} A) :=
  fun B : CommAlgCat.{u} A ↦
    let f : Spec (CommRingCat.of B) ⟶ Spec (CommRingCat.of A) :=
      Spec.map (CommRingCat.ofHom (algebraMap A B))
    UniversalHomeomorphism f ∧ ∀ x : Spec (CommRingCat.of B), IsIso (f.residueFieldMap x)

/-- An `A`-algebra has the seminormalization property exactly when its affine spectrum map is a
universal homeomorphism inducing isomorphisms on all residue fields. -/
theorem seminormalizationAlgebraProperty_iff
    (A : Type u) [CommRing A] (B : CommAlgCat.{u} A) :
    seminormalizationAlgebraProperty A B ↔
      (let f : Spec (CommRingCat.of B) ⟶ Spec (CommRingCat.of A) :=
        Spec.map (CommRingCat.ofHom (algebraMap A B))
      UniversalHomeomorphism f ∧ ∀ x : Spec (CommRingCat.of B), IsIso (f.residueFieldMap x)) := sorry

/-- The category of `A`-algebras whose affine spectrum maps are universal homeomorphisms and
induce isomorphisms on all residue fields. -/
@[stacks 0EUR]
abbrev SeminormalizationAlgebras (A : Type u) [CommRing A] : Type (u + 1) :=
  (seminormalizationAlgebraProperty A).FullSubcategory

/-- Every object in the seminormalization algebra category has a universally homeomorphic affine
spectrum map inducing isomorphisms on all residue fields. -/
theorem SeminormalizationAlgebras.property
    (A : Type u) [CommRing A] (B : SeminormalizationAlgebras A) :
    (let f : Spec (CommRingCat.of (B.1 : Type u)) ⟶ Spec (CommRingCat.of A) :=
      Spec.map (CommRingCat.ofHom (algebraMap A (B.1 : Type u)))
    UniversalHomeomorphism f ∧
      ∀ x : Spec (CommRingCat.of (B.1 : Type u)), IsIso (f.residueFieldMap x)) := sorry

/-- The category of `A`-algebras inducing universal homeomorphisms on affine spectra has a
terminal object. -/
@[stacks 0EUR, instance]
instance instHasTerminalAbsoluteWeakNormalizationAlgebras
    (A : Type u) [CommRing A] :
    HasTerminal (AbsoluteWeakNormalizationAlgebras A) := sorry

/-- The map from an algebra to the terminal absolute weak normalization is an isomorphism exactly
when the algebra is absolutely weakly normal. -/
@[stacks 0EUR]
theorem isIso_to_absoluteWeakNormalization_iff_absolutelyWeaklyNormalRing
    (A : Type u) [CommRing A] (B : AbsoluteWeakNormalizationAlgebras A) :
    IsIso (terminal.from B : B ⟶ ⊤_ (AbsoluteWeakNormalizationAlgebras A)) ↔
      AbsolutelyWeaklyNormalRing (B.1 : Type u) := sorry

/-- The category of `A`-algebras inducing universal homeomorphisms and residue-field isomorphisms
on affine spectra has a terminal object. -/
@[stacks 0EUR, instance]
instance instHasTerminalSeminormalizationAlgebras
    (A : Type u) [CommRing A] :
    HasTerminal (SeminormalizationAlgebras A) := sorry

/-- The map from an algebra to the terminal seminormalization is an isomorphism exactly when the
algebra is seminormal. -/
@[stacks 0EUR]
theorem isIso_to_seminormalization_iff_seminormalRing
    (A : Type u) [CommRing A] (B : SeminormalizationAlgebras A) :
    IsIso (terminal.from B : B ⟶ ⊤_ (SeminormalizationAlgebras A)) ↔
      SeminormalRing (B.1 : Type u) := sorry

/-- Every ring homomorphism induces a unique compatible homomorphism between the terminal
absolute weak normalizations. -/
@[stacks 0EUR]
theorem existsUnique_absoluteWeakNormalizationMap
    {A A' : Type u} [CommRing A] [CommRing A'] (φ : A →+* A') :
    ∃! φawn : ((⊤_ (AbsoluteWeakNormalizationAlgebras A)).1 : Type u) →+*
        ((⊤_ (AbsoluteWeakNormalizationAlgebras A')).1 : Type u),
      φawn.comp (algebraMap A ((⊤_ (AbsoluteWeakNormalizationAlgebras A)).1 : Type u)) =
        (algebraMap A' ((⊤_ (AbsoluteWeakNormalizationAlgebras A')).1 : Type u)).comp φ := sorry

/-- Every ring homomorphism induces a unique compatible homomorphism between the terminal
seminormalizations. -/
@[stacks 0EUR]
theorem existsUnique_seminormalizationMap
    {A A' : Type u} [CommRing A] [CommRing A'] (φ : A →+* A') :
    ∃! φsn : ((⊤_ (SeminormalizationAlgebras A)).1 : Type u) →+*
        ((⊤_ (SeminormalizationAlgebras A')).1 : Type u),
      φsn.comp (algebraMap A ((⊤_ (SeminormalizationAlgebras A)).1 : Type u)) =
        (algebraMap A' ((⊤_ (SeminormalizationAlgebras A')).1 : Type u)).comp φ := sorry

end AlgebraicGeometry

namespace AlgebraicGeometry.Scheme

/-- The category of universal homeomorphisms to a scheme. -/
@[stacks 0EUS]
abbrev AbsoluteWeakNormalizationOver (X : Scheme.{u}) : Type (u + 1) :=
  (CategoryTheory.MorphismProperty.overObj
    (@UniversalHomeomorphism : MorphismProperty Scheme.{u}) (X := X)).FullSubcategory

/-- The structure morphism of an object in the absolute weak normalization category is a
universal homeomorphism. -/
theorem AbsoluteWeakNormalizationOver.property
    (X : Scheme.{u}) (Y : AbsoluteWeakNormalizationOver X) :
    UniversalHomeomorphism Y.1.hom := sorry

/-- The property of a scheme over `X` whose structure morphism is a universal homeomorphism and
induces isomorphisms on all residue fields. -/
@[stacks 0EUS]
abbrev seminormalizationOverProperty (X : Scheme.{u}) : ObjectProperty (Over X) :=
  fun Y : Over X ↦
    UniversalHomeomorphism Y.hom ∧
      ∀ y : Y.left, IsIso (Scheme.Hom.residueFieldMap Y.hom y)

/-- A scheme over `X` has the seminormalization property exactly when its structure morphism is a
universal homeomorphism inducing isomorphisms on all residue fields. -/
theorem seminormalizationOverProperty_iff (X : Scheme.{u}) (Y : Over X) :
    seminormalizationOverProperty X Y ↔
      UniversalHomeomorphism Y.hom ∧
        ∀ y : Y.left, IsIso (Scheme.Hom.residueFieldMap Y.hom y) := sorry

/-- The category of universal homeomorphisms to a scheme that induce isomorphisms on all residue
fields. -/
@[stacks 0EUS]
abbrev SeminormalizationOver (X : Scheme.{u}) : Type (u + 1) :=
  (seminormalizationOverProperty X).FullSubcategory

/-- The structure morphism of an object in the seminormalization category is a universal
homeomorphism inducing isomorphisms on all residue fields. -/
theorem SeminormalizationOver.property
    (X : Scheme.{u}) (Y : SeminormalizationOver X) :
    UniversalHomeomorphism Y.1.hom ∧
      ∀ y : Y.1.left, IsIso (Scheme.Hom.residueFieldMap Y.1.hom y) := sorry

/-- The category of universal homeomorphisms to a scheme has an initial object. -/
@[stacks 0EUS, instance]
instance instHasInitialAbsoluteWeakNormalizationOver (X : Scheme.{u}) :
    HasInitial (AbsoluteWeakNormalizationOver X) := sorry

/-- The canonical morphism from the absolute weak normalization to an object is an isomorphism
exactly when the source scheme of that object is absolutely weakly normal. -/
@[stacks 0EUS]
theorem isIso_initialTo_iff_absolutelyWeaklyNormal
    (X : Scheme.{u}) (Y : AbsoluteWeakNormalizationOver X) :
    IsIso (initial.to Y : (⊥_ (AbsoluteWeakNormalizationOver X)) ⟶ Y) ↔
      AbsolutelyWeaklyNormal Y.1.left := sorry

/-- The category of universal homeomorphisms to a scheme that induce residue-field isomorphisms
has an initial object. -/
@[stacks 0EUS, instance]
instance instHasInitialSeminormalizationOver (X : Scheme.{u}) :
    HasInitial (SeminormalizationOver X) := sorry

/-- The canonical morphism from the seminormalization to an object is an isomorphism exactly when
the source scheme of that object is seminormal. -/
@[stacks 0EUS]
theorem isIso_initialTo_iff_seminormal
    (X : Scheme.{u}) (Y : SeminormalizationOver X) :
    IsIso (initial.to Y : (⊥_ (SeminormalizationOver X)) ⟶ Y) ↔
      Seminormal Y.1.left := sorry

/-- Every scheme morphism induces a unique compatible morphism between the corresponding
absolute weak normalizations. -/
@[stacks 0EUS]
theorem existsUnique_absoluteWeakNormalizationMap
    {X X' : Scheme.{u}} (h : X' ⟶ X) :
    ∃! hawn : (⊥_ (AbsoluteWeakNormalizationOver X')).1.left ⟶
        (⊥_ (AbsoluteWeakNormalizationOver X)).1.left,
      hawn ≫ (⊥_ (AbsoluteWeakNormalizationOver X)).1.hom =
        (⊥_ (AbsoluteWeakNormalizationOver X')).1.hom ≫ h := sorry

/-- Every scheme morphism induces a unique compatible morphism between the corresponding
seminormalizations. -/
@[stacks 0EUS]
theorem existsUnique_seminormalizationMap
    {X X' : Scheme.{u}} (h : X' ⟶ X) :
    ∃! hsn : (⊥_ (SeminormalizationOver X')).1.left ⟶
        (⊥_ (SeminormalizationOver X)).1.left,
      hsn ≫ (⊥_ (SeminormalizationOver X)).1.hom =
        (⊥_ (SeminormalizationOver X')).1.hom ≫ h := sorry

/-- A scheme is seminormal exactly when its canonical seminormalization morphism is an
isomorphism. -/
@[stacks 0H3G]
theorem seminormal_iff_isIso_seminormalizationMap (X : Scheme.{u}) :
    Seminormal X ↔ IsIso ((⊥_ (SeminormalizationOver X)).1.hom) := sorry

/-- A scheme is seminormal exactly when every universal homeomorphism to it from a reduced
scheme that induces isomorphisms on residue fields is an isomorphism. -/
@[stacks 0H3G]
theorem seminormal_iff_universalHomeomorphism_isIso
    (X : Scheme.{u}) :
    Seminormal X ↔
      ∀ {Y : Scheme.{u}} (π : Y ⟶ X), UniversalHomeomorphism π →
        (∀ y : Y, IsIso (π.residueFieldMap y)) → IsReduced Y → IsIso π := sorry

/-- A scheme is absolutely weakly normal exactly when its canonical absolute weak normalization
morphism is an isomorphism. -/
@[stacks 0H3H]
theorem absolutelyWeaklyNormal_iff_isIso_absoluteWeakNormalizationMap (X : Scheme.{u}) :
    AbsolutelyWeaklyNormal X ↔ IsIso ((⊥_ (AbsoluteWeakNormalizationOver X)).1.hom) := sorry

/-- A scheme is absolutely weakly normal exactly when every universal homeomorphism to it from a
reduced scheme is an isomorphism. -/
@[stacks 0H3H]
theorem absolutelyWeaklyNormal_iff_universalHomeomorphism_isIso_of_isReduced
    (X : Scheme.{u}) :
    AbsolutelyWeaklyNormal X ↔
      ∀ {Y : Scheme.{u}} (π : Y ⟶ X), UniversalHomeomorphism π → IsReduced Y → IsIso π := sorry

end AlgebraicGeometry.Scheme
