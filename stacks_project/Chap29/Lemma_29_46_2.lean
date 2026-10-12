/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
import ReasLib.AlgebraicGeometry.Scheme.Morphism.Affine.FilteredColimit

open CategoryTheory CategoryTheory.Limits CommRingCat

universe u v

/- Lemma 29.46.2 (1): universal homeomorphisms of affine schemes are preserved by filtered
colimits of commutative algebras over a fixed base ring. -/
@[stacks 0CN8] #check
  (AlgebraicGeometry.UniversalHomeomorphism.specMap_of_filteredColimit :
    ∀ {J : Type v} [SmallCategory J] [IsFiltered J]
      {A : Type u} [CommRing A]
      (F : J ⥤ CommAlgCat.{u} A) [HasColimit F],
      (∀ j,
        let stageMap : AlgebraicGeometry.Spec (of (F.obj j)) ⟶
            AlgebraicGeometry.Spec (of A) :=
          AlgebraicGeometry.Spec.map (ofHom (algebraMap A (F.obj j)))
        AlgebraicGeometry.UniversalHomeomorphism stageMap) →
        let finalMap : AlgebraicGeometry.Spec (of (colimit F : CommAlgCat.{u} A)) ⟶
            AlgebraicGeometry.Spec (of A) :=
          AlgebraicGeometry.Spec.map
            (ofHom (algebraMap A (colimit F : CommAlgCat.{u} A)))
        AlgebraicGeometry.UniversalHomeomorphism finalMap)

/- Lemma 29.46.2 (2): universal homeomorphisms inducing residue-field isomorphisms are
preserved by filtered colimits of commutative algebras over a fixed base ring. -/
@[stacks 0CN8] #check
  (AlgebraicGeometry.UniversalHomeomorphism.specMap_of_filteredColimit_and_residueFieldMap_isIso :
    ∀ {J : Type v} [SmallCategory J] [IsFiltered J]
      {A : Type u} [CommRing A]
      (F : J ⥤ CommAlgCat.{u} A) [HasColimit F],
      (∀ j,
        let stageMap : AlgebraicGeometry.Spec (of (F.obj j)) ⟶
            AlgebraicGeometry.Spec (of A) :=
          AlgebraicGeometry.Spec.map (ofHom (algebraMap A (F.obj j)))
        AlgebraicGeometry.UniversalHomeomorphism stageMap ∧
          ∀ x : AlgebraicGeometry.Spec (of (F.obj j)),
            IsIso (stageMap.residueFieldMap x)) →
        let finalMap : AlgebraicGeometry.Spec (of (colimit F : CommAlgCat.{u} A)) ⟶
            AlgebraicGeometry.Spec (of A) :=
          AlgebraicGeometry.Spec.map
            (ofHom (algebraMap A (colimit F : CommAlgCat.{u} A)))
        AlgebraicGeometry.UniversalHomeomorphism finalMap ∧
          ∀ x : AlgebraicGeometry.Spec (of (colimit F : CommAlgCat.{u} A)),
            IsIso (finalMap.residueFieldMap x))

/- Lemma 29.46.2 (3): universally closed affine morphisms are preserved by filtered colimits
of commutative algebras over a fixed base ring. -/
@[stacks 0CN8] #check
  (AlgebraicGeometry.UniversallyClosed.specMap_of_filteredColimit :
    ∀ {J : Type v} [SmallCategory J] [IsFiltered J]
      {A : Type u} [CommRing A]
      (F : J ⥤ CommAlgCat.{u} A) [HasColimit F],
      (∀ j,
        let stageMap : AlgebraicGeometry.Spec (of (F.obj j)) ⟶
            AlgebraicGeometry.Spec (of A) :=
          AlgebraicGeometry.Spec.map (ofHom (algebraMap A (F.obj j)))
        AlgebraicGeometry.UniversallyClosed stageMap) →
        let finalMap : AlgebraicGeometry.Spec (of (colimit F : CommAlgCat.{u} A)) ⟶
            AlgebraicGeometry.Spec (of A) :=
          AlgebraicGeometry.Spec.map
            (ofHom (algebraMap A (colimit F : CommAlgCat.{u} A)))
        AlgebraicGeometry.UniversallyClosed finalMap)

/- Lemma 29.46.2 (4): universally closed and universally injective affine morphisms are
preserved by filtered colimits of commutative algebras over a fixed base ring. -/
@[stacks 0CN8] #check
  (AlgebraicGeometry.UniversallyClosed.specMap_of_filteredColimit_and_universallyInjective :
    ∀ {J : Type v} [SmallCategory J] [IsFiltered J]
      {A : Type u} [CommRing A]
      (F : J ⥤ CommAlgCat.{u} A) [HasColimit F],
      (∀ j,
        let stageMap : AlgebraicGeometry.Spec (of (F.obj j)) ⟶
            AlgebraicGeometry.Spec (of A) :=
          AlgebraicGeometry.Spec.map (ofHom (algebraMap A (F.obj j)))
        AlgebraicGeometry.UniversallyClosed stageMap ∧
          AlgebraicGeometry.UniversallyInjective stageMap) →
        let finalMap : AlgebraicGeometry.Spec (of (colimit F : CommAlgCat.{u} A)) ⟶
            AlgebraicGeometry.Spec (of A) :=
          AlgebraicGeometry.Spec.map
            (ofHom (algebraMap A (colimit F : CommAlgCat.{u} A)))
        AlgebraicGeometry.UniversallyClosed finalMap ∧
          AlgebraicGeometry.UniversallyInjective finalMap)
