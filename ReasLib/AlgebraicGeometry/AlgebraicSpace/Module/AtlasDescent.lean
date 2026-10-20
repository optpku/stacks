module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.AtlasGroupoid
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Quasicoherent.Pullback
public import ReasLib.AlgebraicGeometry.GroupoidScheme.Module.Quasicoherent

/-! # Quasi-coherent descent along an étale atlas -/

@[expose] public section

open CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.QCoh

variable {S : Scheme.{u}}

/-- Pullback along an étale atlas has the canonical invertible action from target pullback
to source pullback, induced by the equality of the two atlas composites. -/
def actionIso {X : AlgebraicSpace S} {U : Over S} (φ : ofOver U ⟶ X) [Etale φ]
    (F : QCoh X) :
    (Scheme.QCoh.pullback (atlasGroupoid φ).t.left).obj
      ((restrictToScheme U).obj ((pullback φ).obj F)) ≅
      (Scheme.QCoh.pullback (atlasGroupoid φ).s.left).obj
        ((restrictToScheme U).obj ((pullback φ).obj F)) :=
  ((restrictPullbackIso (atlasGroupoid φ).t).app ((pullback φ).obj F)).symm ≪≫
    (restrictToScheme (atlasGroupoid φ).R).mapIso
      (((pullbackCompIso φ (ofOverMap (atlasGroupoid φ).t)).app F) ≪≫
        eqToIso (congrArg (fun f ↦ (pullback f).obj F) (atlasGroupoid_comp_eq φ)) ≪≫
          ((pullbackCompIso φ (ofOverMap (atlasGroupoid φ).s)).app F).symm) ≪≫
      (restrictPullbackIso (atlasGroupoid φ).s).app ((pullback φ).obj F)

/-- The canonical target-to-source action on the pullback of a quasi-coherent module to
an étale atlas. -/
def action {X : AlgebraicSpace S} {U : Over S} (φ : ofOver U ⟶ X) [Etale φ]
    (F : QCoh X) :
    (Scheme.QCoh.pullback (atlasGroupoid φ).t.left).obj
      ((restrictToScheme U).obj ((pullback φ).obj F)) ⟶
      (Scheme.QCoh.pullback (atlasGroupoid φ).s.left).obj
        ((restrictToScheme U).obj ((pullback φ).obj F)) :=
  (actionIso φ F).hom

/-- The canonical atlas action is invertible. -/
instance action_isIso {X : AlgebraicSpace S} {U : Over S} (φ : ofOver U ⟶ X) [Etale φ]
    (F : QCoh X) : IsIso (action φ F) :=
  inferInstanceAs (IsIso (actionIso φ F).hom)

/-- The canonical isomorphism `α` satisfies the cocycle condition of
`GroupoidScheme.Cocycle`. -/
theorem action_cocycle {X : AlgebraicSpace S} {U : Over S} (φ : ofOver U ⟶ X) [Etale φ]
    (F : QCoh X) :
    GroupoidScheme.Cocycle (atlasGroupoid φ)
      ((restrictToScheme U).obj ((pullback φ).obj F)) (action φ F) :=
  sorry

/-- The canonical isomorphism `α` satisfies the unit condition of `GroupoidScheme.Unit`. -/
theorem action_unit {X : AlgebraicSpace S} {U : Over S} (φ : ofOver U ⟶ X) [Etale φ]
    (F : QCoh X) :
    GroupoidScheme.Unit (atlasGroupoid φ)
      ((restrictToScheme U).obj ((pullback φ).obj F)) (action φ F) :=
  sorry

/-- Pullback and scheme restriction send every module morphism to a morphism compatible
with the canonical atlas actions. -/
theorem toGroupoid_map_compatibility {X : AlgebraicSpace S} {U : Over S}
    (φ : ofOver U ⟶ X) [Etale φ] {F G : QCoh X} (f : F ⟶ G) :
    (Scheme.QCoh.pullback (atlasGroupoid φ).t.left).map
        ((restrictToScheme U).map ((pullback φ).map f)) ≫ action φ G =
      action φ F ≫ (Scheme.QCoh.pullback (atlasGroupoid φ).s.left).map
        ((restrictToScheme U).map ((pullback φ).map f)) :=
  sorry

/-- The functor sending a quasi-coherent `𝒪_X`-module `F` to the equivariant module
`(φ* F, α)` on the atlas groupoid. -/
def toGroupoid {X : AlgebraicSpace S} {U : Over S} (φ : ofOver U ⟶ X) [Etale φ] :
    QCoh X ⥤ (atlasGroupoid φ).QCoh where
  obj F :=
    GroupoidScheme.QCoh.of ((restrictToScheme U).obj ((pullback φ).obj F)) (action φ F)
      (action_cocycle φ F) (action_unit φ F)
  map {F G} f :=
    GroupoidScheme.System.Hom.of
      ((restrictToScheme U).map ((pullback φ).map f))
      (toGroupoid_map_compatibility φ f)
  map_id F := by
    apply GroupoidScheme.System.Hom.ext
    change (restrictToScheme U).map ((pullback φ).map (𝟙 F)) = 𝟙 _
    exact CategoryTheory.Functor.map_id (pullback φ ⋙ restrictToScheme U) F
  map_comp f g := by
    apply GroupoidScheme.System.Hom.ext
    change (restrictToScheme U).map ((pullback φ).map (f ≫ g)) =
      (restrictToScheme U).map ((pullback φ).map f) ≫
        (restrictToScheme U).map ((pullback φ).map g)
    exact CategoryTheory.Functor.map_comp (pullback φ ⋙ restrictToScheme U) f g

/-- The underlying quasi-coherent module of `toGroupoid φ` is `φ* F`, viewed on the
underlying scheme of `U`. -/
theorem toGroupoid_obj {X : AlgebraicSpace S} {U : Over S} (φ : ofOver U ⟶ X) [Etale φ]
    (F : QCoh X) :
    GroupoidScheme.QCoh.obj ((toGroupoid φ).obj F) =
      (restrictToScheme U).obj ((pullback φ).obj F) :=
  rfl

/-- The equivariance map of `toGroupoid φ` is the canonical isomorphism `α`. -/
theorem toGroupoid_action {X : AlgebraicSpace S} {U : Over S} (φ : ofOver U ⟶ X) [Etale φ]
    (F : QCoh X) :
    GroupoidScheme.QCoh.action ((toGroupoid φ).obj F) = action φ F :=
  rfl

/-- Pullback with its canonical action is an equivalence from quasi-coherent modules on
an algebraic space to quasi-coherent modules on the kernel-pair groupoid of a surjective
étale scheme atlas. -/
instance toGroupoid_isEquivalence {X : AlgebraicSpace S} {U : Over S}
    (φ : ofOver U ⟶ X) [Etale φ]
    [Presheaf.IsLocallySurjective (Scheme.etaleTopology.over S) φ] :
    (toGroupoid φ).IsEquivalence := sorry

end AlgebraicGeometry.AlgebraicSpace.QCoh
