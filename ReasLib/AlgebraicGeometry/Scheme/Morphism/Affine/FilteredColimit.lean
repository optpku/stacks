module

public import Mathlib.Algebra.Category.CommAlgCat.Basic
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.UniversalHomeomorphism.Properties

/-!
# Affine spectrum morphisms from filtered colimits

This module records inheritance properties of affine spectrum morphisms under filtered
colimits of commutative algebras over a fixed base ring.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CommRingCat

universe u v

namespace AlgebraicGeometry

namespace UniversalHomeomorphism

variable {J : Type v} [SmallCategory J] [IsFiltered J]
variable {A : Type u} [CommRing A]

/-- The spectrum morphism of a filtered colimit of commutative algebras is a universal
homeomorphism when every spectrum morphism in the diagram is a universal homeomorphism. -/
theorem specMap_of_filteredColimit
    (F : J ⥤ CommAlgCat.{u} A) [HasColimit F]
    (hF : ∀ j,
      let stageMap : Spec (of (F.obj j)) ⟶ Spec (of A) :=
        Spec.map (ofHom (algebraMap A (F.obj j)))
      UniversalHomeomorphism stageMap) :
    let finalMap : Spec (of (colimit F : CommAlgCat.{u} A)) ⟶ Spec (of A) :=
      Spec.map (ofHom (algebraMap A (colimit F : CommAlgCat.{u} A)))
    UniversalHomeomorphism finalMap := sorry

/-- The spectrum morphism of a filtered colimit is a universal homeomorphism inducing
isomorphisms on residue fields when every spectrum morphism in the diagram has both
properties. -/
theorem specMap_of_filteredColimit_and_residueFieldMap_isIso
    (F : J ⥤ CommAlgCat.{u} A) [HasColimit F]
    (hF : ∀ j,
      let stageMap : Spec (of (F.obj j)) ⟶ Spec (of A) :=
        Spec.map (ofHom (algebraMap A (F.obj j)))
      UniversalHomeomorphism stageMap ∧
        ∀ x : Spec (of (F.obj j)), IsIso (stageMap.residueFieldMap x)) :
    let finalMap : Spec (of (colimit F : CommAlgCat.{u} A)) ⟶ Spec (of A) :=
      Spec.map (ofHom (algebraMap A (colimit F : CommAlgCat.{u} A)))
    UniversalHomeomorphism finalMap ∧
      ∀ x : Spec (of (colimit F : CommAlgCat.{u} A)), IsIso (finalMap.residueFieldMap x) := sorry

end UniversalHomeomorphism

namespace UniversallyClosed

variable {J : Type v} [SmallCategory J] [IsFiltered J]
variable {A : Type u} [CommRing A]

/-- The spectrum morphism of a filtered colimit of commutative algebras is universally closed
when every spectrum morphism in the diagram is universally closed. -/
theorem specMap_of_filteredColimit
    (F : J ⥤ CommAlgCat.{u} A) [HasColimit F]
    (hF : ∀ j,
      let stageMap : Spec (of (F.obj j)) ⟶ Spec (of A) :=
        Spec.map (ofHom (algebraMap A (F.obj j)))
      UniversallyClosed stageMap) :
    let finalMap : Spec (of (colimit F : CommAlgCat.{u} A)) ⟶ Spec (of A) :=
      Spec.map (ofHom (algebraMap A (colimit F : CommAlgCat.{u} A)))
    UniversallyClosed finalMap := sorry

/-- The spectrum morphism of a filtered colimit is universally closed and universally
injective when every spectrum morphism in the diagram has both properties. -/
theorem specMap_of_filteredColimit_and_universallyInjective
    (F : J ⥤ CommAlgCat.{u} A) [HasColimit F]
    (hF : ∀ j,
      let stageMap : Spec (of (F.obj j)) ⟶ Spec (of A) :=
        Spec.map (ofHom (algebraMap A (F.obj j)))
      UniversallyClosed stageMap ∧ UniversallyInjective stageMap) :
    let finalMap : Spec (of (colimit F : CommAlgCat.{u} A)) ⟶ Spec (of A) :=
      Spec.map (ofHom (algebraMap A (colimit F : CommAlgCat.{u} A)))
    UniversallyClosed finalMap ∧ UniversallyInjective finalMap := sorry

end UniversallyClosed

end AlgebraicGeometry
