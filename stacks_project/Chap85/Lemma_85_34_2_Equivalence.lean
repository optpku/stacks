/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap85.Lemma_85_34_2_Pullback

/-!
# Descent equivalence for quasi-coherent modules along an fppf hypercovering

If `a : U ⟶ X` is an fppf hypercovering, the unit of `a^* ⊣ a_*` is an isomorphism
on quasi-coherent modules on `X_spaces,étale`, and the counit is an isomorphism on
`QCoh(𝒪_U)`. These assemble to the unit and counit isomorphisms of the QCoh-level
equivalence.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.ObjectProperty
open Functor
open scoped Simplicial

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Simplicial

variable {S : Scheme.{u}} {X : AlgebraicSpace S}
variable {U : SimplicialObject (AlgebraicSpace S)}
variable (a : U ⟶ (const SimplexCategoryᵒᵖ).obj X)

/-- The unit of `a^* ⊣ a_*` is an isomorphism on a quasi-coherent module on
`X_spaces,étale`. -/
theorem unit_app_isIso (ha : IsFppfHypercovering a)
    (F : (spacesQuasiCoherentModuleProperty X).FullSubcategory) :
    IsIso ((moduleAdjunction a).unit.app F.obj) :=
  sorry

/-- The counit of `a^* ⊣ a_*` is an isomorphism on a quasi-coherent module on
`U_spaces,étale`. -/
theorem counit_app_isIso (ha : IsFppfHypercovering a) (G : QCoh U) :
    IsIso ((moduleAdjunction a).counit.app G.obj) :=
  sorry

/-- Naturality of the unit components of QCoh descent. -/
theorem qcohUnitIso_naturality (ha : IsFppfHypercovering a)
    {F G : (spacesQuasiCoherentModuleProperty X).FullSubcategory} (f : F ⟶ G) :
    (𝟭 ((spacesQuasiCoherentModuleProperty X).FullSubcategory)).map f ≫
        ((spacesQuasiCoherentModuleProperty X).isoMk
          (@asIso _ _ _ _ ((moduleAdjunction a).unit.app G.obj)
            (unit_app_isIso a ha G))).hom =
      ((spacesQuasiCoherentModuleProperty X).isoMk
          (@asIso _ _ _ _ ((moduleAdjunction a).unit.app F.obj)
            (unit_app_isIso a ha F))).hom ≫
        (QCoh.pullback a ⋙ QCoh.pushforward a ha).map f :=
  sorry

/-- The unit isomorphism `𝟭 ≅ a^* ⋙ a_*` of fppf hypercovering descent on
quasi-coherent modules. -/
def qcohUnitIso (ha : IsFppfHypercovering a) :
    𝟭 ((spacesQuasiCoherentModuleProperty X).FullSubcategory) ≅
      QCoh.pullback a ⋙ QCoh.pushforward a ha :=
  NatIso.ofComponents
    (fun F ↦
      (spacesQuasiCoherentModuleProperty X).isoMk
        (@asIso _ _ _ _ ((moduleAdjunction a).unit.app F.obj)
          (unit_app_isIso a ha F)))
    (fun f ↦ qcohUnitIso_naturality a ha f)

/-- The component of `qcohUnitIso` at `F` is the adjunction unit on the underlying
module sheaf. -/
theorem qcohUnitIso_hom_app_hom (ha : IsFppfHypercovering a)
    (F : (spacesQuasiCoherentModuleProperty X).FullSubcategory) :
    ((qcohUnitIso a ha).hom.app F).hom = (moduleAdjunction a).unit.app F.obj :=
  sorry

/-- Naturality of the counit components of QCoh descent. -/
theorem qcohCounitIso_naturality (ha : IsFppfHypercovering a)
    {F G : QCoh U} (f : F ⟶ G) :
    (QCoh.pushforward a ha ⋙ QCoh.pullback a).map f ≫
        ((quasiCoherentModuleProperty U).isoMk
          (@asIso _ _ _ _ ((moduleAdjunction a).counit.app G.obj)
            (counit_app_isIso a ha G))).hom =
      ((quasiCoherentModuleProperty U).isoMk
          (@asIso _ _ _ _ ((moduleAdjunction a).counit.app F.obj)
            (counit_app_isIso a ha F))).hom ≫
        (𝟭 (QCoh U)).map f :=
  sorry

/-- The counit isomorphism `a_* ⋙ a^* ≅ 𝟭` on quasi-coherent modules on
`U_spaces,étale`. -/
def qcohCounitIso (ha : IsFppfHypercovering a) :
    QCoh.pushforward a ha ⋙ QCoh.pullback a ≅ 𝟭 (QCoh U) :=
  NatIso.ofComponents
    (fun G ↦
      (quasiCoherentModuleProperty U).isoMk
        (@asIso _ _ _ _ ((moduleAdjunction a).counit.app G.obj)
          (counit_app_isIso a ha G)))
    (fun f ↦ qcohCounitIso_naturality a ha f)

/-- The component of `qcohCounitIso` at `G` is the adjunction counit on the underlying
module sheaf. -/
theorem qcohCounitIso_hom_app_hom (ha : IsFppfHypercovering a) (G : QCoh U) :
    ((qcohCounitIso a ha).hom.app G).hom = (moduleAdjunction a).counit.app G.obj :=
  sorry

/-- If `a` is an fppf hypercovering of `X`, then `a^*` implements an equivalence
between quasi-coherent modules on `X_spaces,étale` and quasi-coherent modules on
`U_spaces,étale`, with quasi-inverse `a_*`. -/
def qcohDescent (ha : IsFppfHypercovering a) :
    (spacesQuasiCoherentModuleProperty X).FullSubcategory ≌ QCoh U :=
  CategoryTheory.Equivalence.mk (QCoh.pullback a) (QCoh.pushforward a ha)
    (qcohUnitIso a ha) (qcohCounitIso a ha)

/-- The forward functor of `qcohDescent` is `a^*` on quasi-coherent modules. -/
theorem qcohDescent_functor (ha : IsFppfHypercovering a) :
    (qcohDescent a ha).functor = QCoh.pullback a :=
  sorry

/-- The inverse functor of `qcohDescent` is `a_*` on quasi-coherent modules. -/
theorem qcohDescent_inverse (ha : IsFppfHypercovering a) :
    (qcohDescent a ha).inverse = QCoh.pushforward a ha :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Simplicial

end
