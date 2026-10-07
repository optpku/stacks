module

public import stacks_project.Chap66.Lemma_66_16_4_Etale
public import stacks_project.Chap66.«66_26_1_1_Restrict»
public import stacks_project.Chap66.Lemma_66_29_2_Pullback
public import stacks_project.Chap70.Lemma_70_5_6_GlobalSections

/-!
# Pullback comparisons for quasi-coherent modules on algebraic spaces

Canonical identifications of quasi-coherent pullback along equal morphisms,
composites, and identities, together with reindexing of equivariance maps.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits
open CategoryTheory.ObjectProperty
open AlgebraicSpace Sheaf.InternalModule

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidAlgebraicSpace

variable {S : Scheme.{u}}

/-- Equal morphisms of algebraic spaces induce canonically isomorphic pullback
functors on quasi-coherent modules. -/
def pullbackEqIso {X Y : AlgebraicSpace S} {f g : X ⟶ Y} (h : f = g) :
    AlgebraicSpace.QCoh.pullback f ≅ AlgebraicSpace.QCoh.pullback g :=
  eqToIso (congrArg AlgebraicSpace.QCoh.pullback h)

/-- Successive pullbacks of quasi-coherent modules identify with pullback along
the composite. -/
def pullbackCompIso {X Y Z : AlgebraicSpace S} (f : X ⟶ Y) (g : Y ⟶ Z) :
    AlgebraicSpace.QCoh.pullback (f ≫ g) ≅
      AlgebraicSpace.QCoh.pullback g ⋙ AlgebraicSpace.QCoh.pullback f :=
  NatIso.ofComponents
    (fun F ↦
      (AlgebraicSpace.quasiCoherentModuleProperty X).isoMk
        ((AlgebraicSpace.Modules.pullbackComp f g).symm.app F.obj))
    sorry

/-- Restriction of modules along an identity morphism is canonically the identity. -/
def restrictFunctorId (X : AlgebraicSpace S) :
    AlgebraicSpace.Modules.restrictFunctor (𝟙 X) ≅ 𝟭 X.Modules :=
  NatIso.ofComponents
    (fun M ↦
      { hom :=
          homOfUnderlying (structureSheaf X)
            (InducedCategory.homMk
              { app := fun _ ↦ 𝟙 _
                naturality := fun _ _ _ ↦ sorry })
            sorry sorry
        inv :=
          homOfUnderlying (structureSheaf X)
            (InducedCategory.homMk
              { app := fun _ ↦ 𝟙 _
                naturality := fun _ _ _ ↦ sorry })
            sorry sorry
        hom_inv_id := sorry
        inv_hom_id := sorry })
    sorry

/-- Pullback of modules along an identity morphism is canonically the identity. -/
def modulesPullbackId (X : AlgebraicSpace S) :
    AlgebraicSpace.Modules.pullback (𝟙 X) ≅ 𝟭 X.Modules :=
  (AlgebraicSpace.Modules.restrictFunctorIsoPullback (𝟙 X)).symm ≪≫ restrictFunctorId X

/-- `modulesPullbackId` is étale restriction along the identity, compared with
module pullback. -/
theorem modulesPullbackId_eq (X : AlgebraicSpace S) :
    modulesPullbackId X =
      (AlgebraicSpace.Modules.restrictFunctorIsoPullback (𝟙 X)).symm ≪≫
        restrictFunctorId X := sorry

/-- Pullback of quasi-coherent modules along an identity morphism is canonically
isomorphic to the identity functor. -/
def pullbackIdIso (X : AlgebraicSpace S) :
    AlgebraicSpace.QCoh.pullback (𝟙 X) ≅ 𝟭 (AlgebraicSpace.QCoh X) :=
  NatIso.ofComponents
    (fun F ↦
      (AlgebraicSpace.quasiCoherentModuleProperty X).isoMk
        ((modulesPullbackId X).app F.obj))
    sorry

/-- Pull an equivariance map back along a morphism into the arrow space,
including the canonical composition comparisons. -/
def reindexAction {X Y Z : AlgebraicSpace S} (target source : X ⟶ Y) (h : Z ⟶ X)
    (F : AlgebraicSpace.QCoh Y)
    (action : (AlgebraicSpace.QCoh.pullback target).obj F ⟶
      (AlgebraicSpace.QCoh.pullback source).obj F) :
    (AlgebraicSpace.QCoh.pullback (h ≫ target)).obj F ⟶
      (AlgebraicSpace.QCoh.pullback (h ≫ source)).obj F :=
  (pullbackCompIso h target).hom.app F ≫
    (AlgebraicSpace.QCoh.pullback h).map action ≫
      (pullbackCompIso h source).inv.app F

/-- `pullbackEqIso` is functoriality of quasi-coherent pullback on equal morphisms. -/
theorem pullbackEqIso_eq {X Y : AlgebraicSpace S} {f g : X ⟶ Y} (h : f = g) :
    pullbackEqIso h = eqToIso (congrArg AlgebraicSpace.QCoh.pullback h) := sorry

/-- The forward component of `pullbackCompIso` is the lifted module-level composition
comparison. -/
theorem pullbackCompIso_hom_app {X Y Z : AlgebraicSpace S} (f : X ⟶ Y) (g : Y ⟶ Z)
    (F : AlgebraicSpace.QCoh Z) :
    ((pullbackCompIso f g).hom.app F).hom =
      (AlgebraicSpace.Modules.pullbackComp f g).symm.hom.app F.obj := sorry

/-- The forward component of `pullbackIdIso` is the lifted module-level identity
comparison. -/
theorem pullbackIdIso_hom_app (X : AlgebraicSpace S) (F : AlgebraicSpace.QCoh X) :
    ((pullbackIdIso X).hom.app F).hom =
      (modulesPullbackId X).hom.app F.obj := sorry

/-- `reindexAction` is pullback of the equivariance map, compared by `pullbackCompIso`. -/
theorem reindexAction_eq {X Y Z : AlgebraicSpace S} (target source : X ⟶ Y)
    (h : Z ⟶ X) (F : AlgebraicSpace.QCoh Y)
    (action : (AlgebraicSpace.QCoh.pullback target).obj F ⟶
      (AlgebraicSpace.QCoh.pullback source).obj F) :
    reindexAction target source h F action =
      (pullbackCompIso h target).hom.app F ≫
        (AlgebraicSpace.QCoh.pullback h).map action ≫
          (pullbackCompIso h source).inv.app F := sorry

end AlgebraicGeometry.GroupoidAlgebraicSpace
