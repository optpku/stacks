module

public import Mathlib.CategoryTheory.HomCongr
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Pasting
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.HomFunctor

/-!
# Restriction of base-changed module morphisms

Morphisms of algebraic spaces over a fixed base induce restriction of module
morphisms on every test scheme, compatibly with identities and composition.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open CategoryTheory.Limits Opposite

noncomputable section

universe u v w

namespace AlgebraicGeometry.AlgebraicSpace.Modules

variable {S : Scheme.{u}} {X B : AlgebraicSpace S}

/-- The canonical map `X'_T ⟶ X_T` induced by `φ : X' ⟶ X`. -/
def restrictSpaceMap (f : X ⟶ B) {X' : AlgebraicSpace S} (φ : X' ⟶ X)
    (σ : SchemeOver B) :
    baseChangeSpace (φ ≫ f) σ.hom ⟶ baseChangeSpace f σ.hom :=
  Limits.pullback.lift
    (baseChangeProj (φ ≫ f) σ.hom ≫ φ)
    (Limits.pullback.snd (φ ≫ f) σ.hom)
    ((Category.assoc (baseChangeProj (φ ≫ f) σ.hom) φ f).trans
      (Limits.pullback.condition :
        Limits.pullback.fst (φ ≫ f) σ.hom ≫ (φ ≫ f) =
          Limits.pullback.snd (φ ≫ f) σ.hom ≫ σ.hom))

/-- `restrictSpaceMap` is the second projection of `X' ×_X X_T` after pasting. -/
theorem restrictSpaceMap_eq_pasting (f : X ⟶ B) {X' : AlgebraicSpace S}
    (φ : X' ⟶ X) (σ : SchemeOver B) :
    restrictSpaceMap f φ σ =
      (pullbackRightPullbackFstIso f σ.hom φ).symm.hom ≫
        Limits.pullback.snd φ (baseChangeProj f σ.hom) :=
  sorry

/-- `restrictSpaceMap` commutes with the projections to `X`. -/
theorem restrictSpaceMap_comp_proj (f : X ⟶ B) {X' : AlgebraicSpace S} (φ : X' ⟶ X)
    (σ : SchemeOver B) :
    restrictSpaceMap f φ σ ≫ baseChangeProj f σ.hom =
      baseChangeProj (φ ≫ f) σ.hom ≫ φ :=
  Limits.pullback.lift_fst
    (baseChangeProj (φ ≫ f) σ.hom ≫ φ)
    (Limits.pullback.snd (φ ≫ f) σ.hom)
    ((Category.assoc (baseChangeProj (φ ≫ f) σ.hom) φ f).trans
      (Limits.pullback.condition :
        Limits.pullback.fst (φ ≫ f) σ.hom ≫ (φ ≫ f) =
          Limits.pullback.snd (φ ≫ f) σ.hom ≫ σ.hom))

/-- Identification of `(φ^* F)_T` with the pullback of `F_T` along `X'_T ⟶ X_T`. -/
def restrictModuleIso (f : X ⟶ B) {X' : AlgebraicSpace S} (φ : X' ⟶ X)
    (σ : SchemeOver B) (F : X.Modules) :
    baseChangeModule (φ ≫ f) σ.hom ((pullback φ).obj F) ≅
      (pullback (restrictSpaceMap f φ σ)).obj (baseChangeModule f σ.hom F) :=
  (pullbackCompIso (baseChangeProj (φ ≫ f) σ.hom) φ).app F ≪≫
    (pullbackCongr (restrictSpaceMap_comp_proj f φ σ).symm).app F ≪≫
    (pullbackCompIso (restrictSpaceMap f φ σ) (baseChangeProj f σ.hom)).symm.app F

/-- Restriction of an `𝒪_{X_T}`-module map along a morphism `φ : X' ⟶ X` over `B`. -/
def restrictHomAlong (f : X ⟶ B) (F G : X.Modules) {X' : AlgebraicSpace S}
    (φ : X' ⟶ X) (σ : SchemeOver B)
    (u : baseChangeModule f σ.hom F ⟶ baseChangeModule f σ.hom G) :
    baseChangeModule (φ ≫ f) σ.hom ((pullback φ).obj F) ⟶
      baseChangeModule (φ ≫ f) σ.hom ((pullback φ).obj G) :=
  (restrictModuleIso f φ σ F).hom ≫
    (pullback (restrictSpaceMap f φ σ)).map u ≫ (restrictModuleIso f φ σ G).inv

/-- After the pasting identification, `restrictHomAlong` is pullback along
`restrictSpaceMap`. -/
theorem restrictHomAlong_spec (f : X ⟶ B) (F G : X.Modules)
    {X' : AlgebraicSpace S} (φ : X' ⟶ X) (σ : SchemeOver B)
    (u : baseChangeModule f σ.hom F ⟶ baseChangeModule f σ.hom G) :
    restrictHomAlong f F G φ σ u =
      (restrictModuleIso f φ σ F).hom ≫
        (pullback (restrictSpaceMap f φ σ)).map u ≫
          (restrictModuleIso f φ σ G).inv :=
  sorry

/-- Transport of a base-changed Hom along an equality of structure morphisms over `B`. -/
def homCast {X' : AlgebraicSpace S} {α β : X' ⟶ B} (h : α = β) (σ : SchemeOver B)
    (F G : X'.Modules)
    (u : baseChangeModule α σ.hom F ⟶ baseChangeModule α σ.hom G) :
    baseChangeModule β σ.hom F ⟶ baseChangeModule β σ.hom G :=
  cast (congrArg (fun γ ↦
      (baseChangeModule γ σ.hom F ⟶ baseChangeModule γ σ.hom G)) h) u


/-- Restriction along `𝟙 X` recovers the original map after the identity
identifications of structure morphisms and module pullbacks. -/
theorem restrictHomAlong_id (f : X ⟶ B) (F G : X.Modules) (σ : SchemeOver B)
    (u : baseChangeModule f σ.hom F ⟶ baseChangeModule f σ.hom G) :
    ∃ (eF : (pullback (𝟙 X)).obj F ≅ F) (eG : (pullback (𝟙 X)).obj G ≅ G),
      CategoryTheory.Iso.homCongr
          ((pullback (baseChangeProj f σ.hom)).mapIso eF)
          ((pullback (baseChangeProj f σ.hom)).mapIso eG)
          (homCast (Category.id_comp f) σ ((pullback (𝟙 X)).obj F)
            ((pullback (𝟙 X)).obj G) (restrictHomAlong f F G (𝟙 X) σ u)) =
        u :=
  sorry

/-- Restriction along a composite `X'' ⟶ X' ⟶ X` is the composite restriction. -/
theorem restrictHomAlong_comp (f : X ⟶ B) (F G : X.Modules)
    {X' X'' : AlgebraicSpace S} (φ : X' ⟶ X) (ψ : X'' ⟶ X') (σ : SchemeOver B)
    (u : baseChangeModule f σ.hom F ⟶ baseChangeModule f σ.hom G) :
    restrictHomAlong f F G (ψ ≫ φ) σ u =
      CategoryTheory.Iso.homCongr
        ((pullback (baseChangeProj ((ψ ≫ φ) ≫ f) σ.hom)).mapIso
          ((pullbackCompIso ψ φ).app F))
        ((pullback (baseChangeProj ((ψ ≫ φ) ≫ f) σ.hom)).mapIso
          ((pullbackCompIso ψ φ).app G))
        (homCast (Category.assoc ψ φ f).symm σ
          ((pullback ψ).obj ((pullback φ).obj F))
          ((pullback ψ).obj ((pullback φ).obj G))
          (restrictHomAlong (φ ≫ f) ((pullback φ).obj F) ((pullback φ).obj G) ψ σ
            (restrictHomAlong f F G φ σ u))) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Modules
