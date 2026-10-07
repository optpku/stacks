module

public import ReasLib.AlgebraicGeometry.GroupoidScheme.Module.Quasicoherent
public import ReasLib.CategoryTheory.Sites.Topos.ModuleAdjunction
public import stacks_project.Chap66.«66_26_0_1_Pushforward»
public import stacks_project.Chap66.Lemma_66_26_3_Glueing
public import stacks_project.Chap66.Lemma_66_29_2_Pullback
public import stacks_project.Chap66.Proposition_66_32_1_Comparison
public import stacks_project.Chap66.Proposition_66_32_1_Groupoid

/-!
# Quasi-coherent modules along an étale presentation

Pullback along an étale atlas `φ : U ⟶ X` sends a quasi-coherent `𝒪_X`-module `F` to
`φ* F` on `U`, equipped with the canonical isomorphism `α : t* φ* F ⟶ s* φ* F` obtained
from `φ ∘ t = φ ∘ s` and functoriality of pullback. This is the functor from
`QCoh X` to quasi-coherent modules on the atlas groupoid.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open CategoryTheory.ObjectProperty
open CategoryTheory.Sheaf.InternalModule

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.QCoh

variable {S : Scheme.{u}}

/-- Successive pullbacks of quasi-coherent modules along étale morphisms identify with
pullback along the composite, by lifting `SmallEtaleModuleGlueing.modulesPullbackComp`. -/
def pullbackCompIso {X Y Z : AlgebraicSpace S} (g : Y ⟶ Z) [Etale g] (f : X ⟶ Y) [Etale f] :
    pullback g ⋙ pullback f ≅ pullback (f ≫ g) :=
  NatIso.ofComponents
    (fun F ↦
      (quasiCoherentModuleProperty X).isoMk
        ((SmallEtaleModuleGlueing.modulesPullbackComp f g).app F.obj))
    sorry

/-- The forward component of `pullbackCompIso` is the lifted module-level composition
comparison. -/
theorem pullbackCompIso_hom_app {X Y Z : AlgebraicSpace S} (g : Y ⟶ Z) [Etale g]
    (f : X ⟶ Y) [Etale f] (F : QCoh Z) :
    ((pullbackCompIso g f).hom.app F).hom =
      (SmallEtaleModuleGlueing.modulesPullbackComp f g).hom.app F.obj :=
  sorry

/-- The two kernel-pair projections of an étale atlas equalize `φ`. -/
theorem atlasGroupoid_comp_eq {X : AlgebraicSpace S} {U : Over S} (φ : ofOver U ⟶ X)
    [Etale φ] :
    ofOverMap (atlasGroupoid φ).t ≫ φ = ofOverMap (atlasGroupoid φ).s ≫ φ :=
  sorry

/-- An étale morphism of schemes over `S` induces an étale morphism of algebraic spaces, so
the kernel-pair projections of an atlas are étale as algebraic-space morphisms. -/
instance etale_ofOverMap_atlasGroupoid_t {X : AlgebraicSpace S} {U : Over S}
    {φ : ofOver U ⟶ X} [Etale φ] : Etale (ofOverMap (atlasGroupoid φ).t) :=
  etale_ofOverMap_of_etale (atlasGroupoid φ).t

/-- The source projection of an étale atlas is étale as a morphism of algebraic spaces. -/
instance etale_ofOverMap_atlasGroupoid_s {X : AlgebraicSpace S} {U : Over S}
    {φ : ofOver U ⟶ X} [Etale φ] : Etale (ofOverMap (atlasGroupoid φ).s) :=
  etale_ofOverMap_of_etale (atlasGroupoid φ).s

/-- Underlying sections of the two pushforward-restriction composites agree. -/
theorem modulesRestrictPushforward_underlying_eq {U V : Over S} (h : V ⟶ U)
    [AlgebraicGeometry.Etale h.left] (N : (ofOver V).Modules)
    (W : (TopologicalSpace.Opens U.left)ᵒᵖ) :
    ((ToInternal.underlying U.left.ringCatSheaf).obj
          ((Modules.pushforward (ofOverMap h) ⋙ Modules.restrictToScheme U).obj N)).obj.obj W =
      ((ToInternal.underlying U.left.ringCatSheaf).obj
          ((Modules.restrictToScheme V ⋙ Scheme.Modules.pushforward h.left).obj N)).obj.obj W :=
  sorry

/-- Restriction to the underlying scheme intertwines module pushforward along `ofOverMap h`
with scheme-level module pushforward along `h.left`. The comparison is transport of the
identity on underlying sections. -/
def modulesRestrictPushforwardIso {U V : Over S} (h : V ⟶ U)
    [AlgebraicGeometry.Etale h.left] :
    Modules.pushforward (ofOverMap h) ⋙ Modules.restrictToScheme U ≅
      Modules.restrictToScheme V ⋙ Scheme.Modules.pushforward h.left :=
  NatIso.ofComponents
    (fun N ↦
      { hom :=
          homOfUnderlying U.left.ringCatSheaf
            ⟨{ app := fun W ↦ eqToHom (modulesRestrictPushforward_underlying_eq h N W)
               naturality := fun _ _ _ ↦ sorry }⟩
            sorry sorry
        inv :=
          homOfUnderlying U.left.ringCatSheaf
            ⟨{ app := fun W ↦ eqToHom (modulesRestrictPushforward_underlying_eq h N W).symm
               naturality := fun _ _ _ ↦ sorry }⟩
            sorry sorry
        hom_inv_id := sorry
        inv_hom_id := sorry })
    sorry

/-- The two pushforward-restriction composites become the identity after composing the
comparison with its inverse. -/
theorem modulesRestrictPushforwardIso_hom_inv_id {U V : Over S} (h : V ⟶ U)
    [AlgebraicGeometry.Etale h.left] :
    (modulesRestrictPushforwardIso h).hom ≫ (modulesRestrictPushforwardIso h).inv = 𝟙 _ :=
  sorry

/-- Underlying sections of the two pullback-restriction composites agree. -/
theorem modulesRestrictPullback_underlying_eq {U V : Over S} (h : V ⟶ U)
    [AlgebraicGeometry.Etale h.left] (F : (ofOver U).Modules)
    (W : (TopologicalSpace.Opens V.left)ᵒᵖ) :
    ((ToInternal.underlying V.left.ringCatSheaf).obj
          ((Modules.pullback (ofOverMap h) ⋙ Modules.restrictToScheme V).obj F)).obj.obj W =
      ((ToInternal.underlying V.left.ringCatSheaf).obj
          ((Modules.restrictToScheme U ⋙ Scheme.Modules.pullback h.left).obj F)).obj.obj W :=
  sorry

/-- Restriction of modules to the underlying scheme, after pullback along `ofOverMap h`,
identifies with restriction followed by scheme-level module pullback. -/
def modulesRestrictPullbackIso {U V : Over S} (h : V ⟶ U)
    [AlgebraicGeometry.Etale h.left] :
    Modules.pullback (ofOverMap h) ⋙ Modules.restrictToScheme V ≅
      Modules.restrictToScheme U ⋙ Scheme.Modules.pullback h.left :=
  NatIso.ofComponents
    (fun F ↦
      { hom :=
          homOfUnderlying V.left.ringCatSheaf
            ⟨{ app := fun W ↦ eqToHom (modulesRestrictPullback_underlying_eq h F W)
               naturality := fun _ _ _ ↦ sorry }⟩
            sorry sorry
        inv :=
          homOfUnderlying V.left.ringCatSheaf
            ⟨{ app := fun W ↦ eqToHom (modulesRestrictPullback_underlying_eq h F W).symm
               naturality := fun _ _ _ ↦ sorry }⟩
            sorry sorry
        hom_inv_id := sorry
        inv_hom_id := sorry })
    sorry

/-- Pullback along an étale morphism of schemes over `S`, then restriction to the underlying
scheme, identifies with restriction followed by scheme-level pullback. -/
def restrictPullbackIso {U V : Over S} (h : V ⟶ U)
    [AlgebraicGeometry.Etale h.left] :
    pullback (ofOverMap h) ⋙ restrictToScheme V ≅
      restrictToScheme U ⋙ Scheme.QCoh.pullback h.left :=
  NatIso.ofComponents
    (fun F ↦
      (Scheme.quasiCoherentModuleProperty V.left).isoMk
        ((modulesRestrictPullbackIso h).app F.obj))
    sorry

/-- The forward component of `restrictPullbackIso` is the lifted module-level comparison. -/
theorem restrictPullbackIso_hom_app {U V : Over S} (h : V ⟶ U)
    [AlgebraicGeometry.Etale h.left] (F : QCoh (ofOver U)) :
    ((restrictPullbackIso h).hom.app F).hom =
      (modulesRestrictPullbackIso h).hom.app F.obj :=
  sorry

/-- Functoriality of pullback along `t ≫ φ` for an étale atlas. -/
def atlasTargetPullbackCompIso {X : AlgebraicSpace S} {U : Over S} (φ : ofOver U ⟶ X)
    [Etale φ] :
    pullback φ ⋙ pullback (ofOverMap (atlasGroupoid φ).t) ≅
      pullback (ofOverMap (atlasGroupoid φ).t ≫ φ) :=
  @pullbackCompIso S (ofOver (atlasGroupoid φ).R) (ofOver U) X φ inferInstance
    (ofOverMap (atlasGroupoid φ).t) etale_ofOverMap_atlasGroupoid_t

/-- Functoriality of pullback along `s ≫ φ` for an étale atlas. -/
def atlasSourcePullbackCompIso {X : AlgebraicSpace S} {U : Over S} (φ : ofOver U ⟶ X)
    [Etale φ] :
    pullback φ ⋙ pullback (ofOverMap (atlasGroupoid φ).s) ≅
      pullback (ofOverMap (atlasGroupoid φ).s ≫ φ) :=
  @pullbackCompIso S (ofOver (atlasGroupoid φ).R) (ofOver U) X φ inferInstance
    (ofOverMap (atlasGroupoid φ).s) etale_ofOverMap_atlasGroupoid_s

/-- `atlasTargetPullbackCompIso φ` is an isomorphism of pullback functors. -/
theorem atlasTargetPullbackCompIso_inv_hom_id {X : AlgebraicSpace S} {U : Over S}
    (φ : ofOver U ⟶ X) [Etale φ] :
    (atlasTargetPullbackCompIso φ).inv ≫ (atlasTargetPullbackCompIso φ).hom = 𝟙 _ := sorry

/-- `atlasSourcePullbackCompIso φ` is an isomorphism of pullback functors. -/
theorem atlasSourcePullbackCompIso_inv_hom_id {X : AlgebraicSpace S} {U : Over S}
    (φ : ofOver U ⟶ X) [Etale φ] :
    (atlasSourcePullbackCompIso φ).inv ≫ (atlasSourcePullbackCompIso φ).hom = 𝟙 _ := sorry

/-- The algebraic-space level comparison `t* φ* F ⟶ s* φ* F` before restriction to schemes. -/
def actionAux {X : AlgebraicSpace S} {U : Over S} (φ : ofOver U ⟶ X) [Etale φ] (F : QCoh X) :
    (pullback (ofOverMap (atlasGroupoid φ).t)).obj ((pullback φ).obj F) ⟶
      (pullback (ofOverMap (atlasGroupoid φ).s)).obj ((pullback φ).obj F) :=
  (atlasTargetPullbackCompIso φ).hom.app F ≫
    eqToHom (congrArg (fun f ↦ (pullback f).obj F) (atlasGroupoid_comp_eq φ)) ≫
      (atlasSourcePullbackCompIso φ).inv.app F

/-- `actionAux` is the composite of the two atlas pullback-composition comparisons along
`t ≫ φ = s ≫ φ`. -/
theorem actionAux_spec {X : AlgebraicSpace S} {U : Over S} (φ : ofOver U ⟶ X) [Etale φ]
    (F : QCoh X) :
    actionAux φ F =
      (atlasTargetPullbackCompIso φ).hom.app F ≫
        eqToHom (congrArg (fun f ↦ (pullback f).obj F) (atlasGroupoid_comp_eq φ)) ≫
          (atlasSourcePullbackCompIso φ).inv.app F := sorry

/-- The canonical isomorphism `α : t* φ* F ⟶ s* φ* F` of an étale atlas, obtained from
`φ ∘ t = φ ∘ s` and functoriality of pullback. -/
def action {X : AlgebraicSpace S} {U : Over S} (φ : ofOver U ⟶ X) [Etale φ] (F : QCoh X) :
    (Scheme.QCoh.pullback (atlasGroupoid φ).t.left).obj
      ((restrictToScheme U).obj ((pullback φ).obj F)) ⟶
      (Scheme.QCoh.pullback (atlasGroupoid φ).s.left).obj
        ((restrictToScheme U).obj ((pullback φ).obj F)) :=
  (restrictPullbackIso (atlasGroupoid φ).t).inv.app ((pullback φ).obj F) ≫
    (restrictToScheme (atlasGroupoid φ).R).map (actionAux φ F) ≫
      (restrictPullbackIso (atlasGroupoid φ).s).hom.app ((pullback φ).obj F)

/-- `action φ F` is the transport of the algebraic-space comparison `actionAux` through
`restrictPullbackIso`. -/
theorem action_spec {X : AlgebraicSpace S} {U : Over S} (φ : ofOver U ⟶ X) [Etale φ]
    (F : QCoh X) :
    action φ F =
      (restrictPullbackIso (atlasGroupoid φ).t).inv.app ((pullback φ).obj F) ≫
        (restrictToScheme (atlasGroupoid φ).R).map (actionAux φ F) ≫
          (restrictPullbackIso (atlasGroupoid φ).s).hom.app ((pullback φ).obj F) := sorry

/-- The canonical isomorphism `α` of an étale atlas is an isomorphism. -/
instance action_isIso {X : AlgebraicSpace S} {U : Over S} (φ : ofOver U ⟶ X) [Etale φ]
    (F : QCoh X) : IsIso (action φ F) :=
  sorry

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

/-- The functor sending a quasi-coherent `𝒪_X`-module `F` to the equivariant module
`(φ* F, α)` on the atlas groupoid. -/
def toGroupoid {X : AlgebraicSpace S} {U : Over S} (φ : ofOver U ⟶ X) [Etale φ] :
    QCoh X ⥤ (atlasGroupoid φ).QCoh where
  obj F :=
    GroupoidScheme.QCoh.of ((restrictToScheme U).obj ((pullback φ).obj F)) (action φ F)
      (action_cocycle φ F) (action_unit φ F)
  map {F G} f :=
    GroupoidScheme.System.Hom.of
      ((restrictToScheme U).map ((pullback φ).map f)) sorry
  map_id := sorry
  map_comp := sorry

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
  sorry

end AlgebraicGeometry.AlgebraicSpace.QCoh
