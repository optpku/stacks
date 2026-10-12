/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap67.Definition_67_48_3_Normalization
public import stacks_project.Chap67.Lemma_67_48_5_Normalization
public import stacks_project.Chap76.Lemma_76_36_1_Instances
public import stacks_project.Chap76.Lemma_76_36_1_Pullback
import StacksCheckRecall

/-!
# Stein factorization for universally closed quasi-separated morphisms

A universally closed quasi-separated morphism of algebraic spaces factors
through the relative normalization of the target in the source. The first
factor is universally closed, quasi-compact, quasi-separated and surjective,
the second factor is integral, the first factor pushes the structure sheaf
isomorphically onto the intermediate structure sheaf, and the intermediate
space is the relative spectrum of the pushed-forward structure sheaf.
Formation of this factorization commutes with flat base change.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace Limits

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/- Lemma 76.36.1 (1): the morphism to the relative normalization is universally
closed. -/
@[stacks 0A19] #check
  (Hom.instUniversallyClosed_toNormalization :
    ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
      [UniversallyClosed f] [QuasiSeparated f],
      UniversallyClosed (Hom.toNormalization f))

/- Lemma 76.36.1 (2): the morphism to the relative normalization is
quasi-compact. -/
@[stacks 0A19] #check
  (Hom.instQuasiCompact_toNormalization_of_universallyClosed :
    ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
      [UniversallyClosed f] [QuasiSeparated f],
      QuasiCompact (Hom.toNormalization f))

/- Lemma 76.36.1 (3): the morphism to the relative normalization is
quasi-separated. -/
@[stacks 0A19] #check
  (Hom.instQuasiSeparated_toNormalization :
    ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
      [UniversallyClosed f] [QuasiSeparated f],
      QuasiSeparated (Hom.toNormalization f))

/- Lemma 76.36.1 (4): the morphism to the relative normalization is
surjective. -/
@[stacks 0A19] #check
  (Hom.instSurjective_toNormalization :
    ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
      [UniversallyClosed f] [QuasiSeparated f],
      Surjective (Hom.toNormalization f))

/- Lemma 76.36.1 (5): the structure morphism from the relative normalization is
integral. -/
@[stacks 0A19] #check
  (Hom.instIsIntegralHom_fromNormalization :
    ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
      [QuasiCompact f] [QuasiSeparated f],
      IsIntegralHom (Hom.fromNormalization f))

/- Lemma 76.36.1 (6): the structure-sheaf map of the morphism to the relative
normalization is an isomorphism. -/
@[stacks 0A19] #check
  (Hom.instIsIso_commRingStructureSheafMap_toNormalization :
    ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
      [UniversallyClosed f] [QuasiSeparated f],
      IsIso (commRingStructureSheafMap (Hom.toNormalization f)))

/- Lemma 76.36.1 (7): the relative normalization is uniquely isomorphic over the
target to Spec_Y of the pushed-forward structure sheaf. -/
@[stacks 0A19] #check
  (Hom.existsUnique_iso_toPushforwardRelativeSpec :
    ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
      [UniversallyClosed f] [QuasiSeparated f],
      ∃! e : Hom.normalization f ≅ relativeSpec (pushforwardStructureQcAlgebra f),
        Hom.toNormalization f ≫ e.hom = Hom.toPushforwardRelativeSpec f ∧
          e.hom ≫ relativeSpecπ (pushforwardStructureQcAlgebra f) =
            Hom.fromNormalization f)

/- Lemma 76.36.1 (8): the intermediate space is the normalization of the target
in the source. -/
@[stacks 0A19] #check AlgebraicGeometry.AlgebraicSpace.Hom.normalization

/- Lemma 76.36.1 (9): the constructed factorization is a relative-normalization
factorization. -/
@[stacks 0A19] #check
  (Hom.isNormalization_normalization :
    ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
      [QuasiCompact f] [QuasiSeparated f],
      IsNormalization f (Hom.toNormalization f) (Hom.fromNormalization f))

/- Lemma 76.36.1 (10): the canonical maps through the relative normalization factor
the original morphism. -/
@[stacks 0A19] #check
  (Hom.toNormalization_fromNormalization :
    ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
      [QuasiCompact f] [QuasiSeparated f],
      Hom.toNormalization f ≫ Hom.fromNormalization f = f)

/- Lemma 76.36.1 (11): formation of the factorization commutes with flat base change. -/
@[stacks 0A19] #check
  (Hom.existsUnique_isIso_normalizationPullback_of_flat :
    ∀ {S : Scheme.{u}} {X Y Z : AlgebraicSpace S} (f : X ⟶ Y) (g : Z ⟶ Y)
      [UniversallyClosed f] [QuasiSeparated f] [Flat g],
      ∃! h : Hom.normalization (pullback.snd f g) ⟶
          pullback (Hom.fromNormalization f) g,
        Hom.toNormalization (pullback.snd f g) ≫ h =
            pullbackToNormalization f g ∧
          h ≫ pullback.snd (Hom.fromNormalization f) g =
            Hom.fromNormalization (pullback.snd f g) ∧
          IsIso h)

end AlgebraicGeometry.AlgebraicSpace
