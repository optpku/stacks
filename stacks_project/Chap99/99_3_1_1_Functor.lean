module

public import stacks_project.Chap70.Lemma_70_5_6_GlobalSections
public import stacks_project.Chap70.Lemma_70_7_2_FinitePresentation
public import stacks_project.Chap77.«77_7_1_1_IsomorphismFunctor»

/-!
# The Hom functor of quasi-coherent modules on an algebraic space

This module constructs the contravariant functor on schemes over `B` sending a
test scheme `T` to the type of `𝒪_{X_T}`-module maps `F_T ⟶ G_T`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open CategoryTheory.Limits Opposite

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Modules

variable {S : Scheme.{u}} {X B : AlgebraicSpace S}

/-- The canonical map `X_{T'} ⟶ X_T` induced by a morphism of schemes over `B`. -/
def baseChangeSpaceMap (f : X ⟶ B) {σ τ : SchemeOver B} (h : τ ⟶ σ) :
    baseChangeSpace f τ.hom ⟶ baseChangeSpace f σ.hom :=
  Limits.pullback.map f τ.hom f σ.hom (𝟙 X) ((ofOverFunctor S).map h.left) (𝟙 B)
    ((Category.comp_id f).trans (Category.id_comp f).symm)
    ((Category.comp_id τ.hom).trans (CostructuredArrow.w h).symm)

/-- The map `baseChangeSpaceMap f h` commutes with the projections to `X`. -/
theorem baseChangeSpaceMap_fst (f : X ⟶ B) {σ τ : SchemeOver B} (h : τ ⟶ σ) :
    baseChangeSpaceMap f h ≫ baseChangeProj f σ.hom = baseChangeProj f τ.hom :=
  sorry

/-- The map `baseChangeSpaceMap f h` commutes with the projections to the varying base. -/
theorem baseChangeSpaceMap_snd (f : X ⟶ B) {σ τ : SchemeOver B} (h : τ ⟶ σ) :
    baseChangeSpaceMap f h ≫ Limits.pullback.snd f σ.hom =
      Limits.pullback.snd f τ.hom ≫ (ofOverFunctor S).map h.left :=
  sorry

/-- The comparison identifying `F_{T'}` with the pullback of `F_T` along `X_{T'} ⟶ X_T`. -/
def baseChangeModuleCompIso (f : X ⟶ B) (F : X.Modules) {σ τ : SchemeOver B} (h : τ ⟶ σ) :
    baseChangeModule f τ.hom F ≅
      (pullback (baseChangeSpaceMap f h)).obj (baseChangeModule f σ.hom F) :=
  (pullbackCongr
      ((Limits.pullback.lift_fst (Limits.pullback.fst f τ.hom ≫ 𝟙 X)
          (Limits.pullback.snd f τ.hom ≫ (ofOverFunctor S).map h.left)
          (((Category.assoc (Limits.pullback.fst f τ.hom) (𝟙 X) f).trans
              (congrArg (fun k ↦ Limits.pullback.fst f τ.hom ≫ k)
                (Category.id_comp f))).trans
            ((Limits.pullback.condition :
                Limits.pullback.fst f τ.hom ≫ f =
                  Limits.pullback.snd f τ.hom ≫ τ.hom).trans
              ((congrArg (fun k ↦ Limits.pullback.snd f τ.hom ≫ k)
                  (CostructuredArrow.w h).symm).trans
                (Category.assoc (Limits.pullback.snd f τ.hom)
                  ((ofOverFunctor S).map h.left) σ.hom).symm)))).trans
        (Category.comp_id _)).symm).app F ≪≫
    (pullbackComp (baseChangeSpaceMap f h) (baseChangeProj f σ.hom)).symm.app F

/-- Restriction of an `𝒪_{X_T}`-module map along `X_{T'} ⟶ X_T`. -/
def baseChangeHom (f : X ⟶ B) (F G : X.Modules) {σ τ : SchemeOver B} (h : τ ⟶ σ)
    (u : baseChangeModule f σ.hom F ⟶ baseChangeModule f σ.hom G) :
    baseChangeModule f τ.hom F ⟶ baseChangeModule f τ.hom G :=
  (baseChangeModuleCompIso f F h).hom ≫
    (pullback (baseChangeSpaceMap f h)).map u ≫ (baseChangeModuleCompIso f G h).inv

/-- Restriction of Hom-sets along the identity morphism of a scheme over `B` is the identity. -/
theorem baseChangeHom_id (f : X ⟶ B) (F G : X.Modules) {σ : SchemeOver B}
    (u : baseChangeModule f σ.hom F ⟶ baseChangeModule f σ.hom G) :
    baseChangeHom f F G (𝟙 σ) u = u :=
  sorry

/-- Restriction of Hom-sets along a composite morphism of schemes over `B` is the composite
restriction. -/
theorem baseChangeHom_comp (f : X ⟶ B) (F G : X.Modules) {σ τ ρ : SchemeOver B}
    (h : τ ⟶ σ) (k : ρ ⟶ τ)
    (u : baseChangeModule f σ.hom F ⟶ baseChangeModule f σ.hom G) :
    baseChangeHom f F G (k ≫ h) u = baseChangeHom f F G k (baseChangeHom f F G h u) :=
  sorry

namespace HomFunctor

/-- The contravariant Hom functor on schemes over `B`, sending `T` to the type of
`𝒪_{X_T}`-module morphisms `F_T ⟶ G_T`. -/
def functor (f : X ⟶ B) (F G : X.Modules) [F.IsQuasicoherent] [G.IsQuasicoherent] :
    (SchemeOver B)ᵒᵖ ⥤ Type (u + 1) where
  obj σ := baseChangeModule f σ.unop.hom F ⟶ baseChangeModule f σ.unop.hom G
  map h := TypeCat.ofHom (baseChangeHom f F G h.unop)
  map_id := sorry
  map_comp := sorry

/-- The value of the Hom functor at a scheme over `B` is the Hom-type of the base-changed
modules. -/
theorem functor_obj (f : X ⟶ B) (F G : X.Modules) [F.IsQuasicoherent] [G.IsQuasicoherent]
    (σ : SchemeOver B) :
    (functor f F G).obj (op σ) =
      (baseChangeModule f σ.hom F ⟶ baseChangeModule f σ.hom G) :=
  sorry

/-- The Hom functor acts on a morphism of schemes over `B` by restriction of module maps. -/
theorem functor_map (f : X ⟶ B) (F G : X.Modules) [F.IsQuasicoherent] [G.IsQuasicoherent]
    {σ τ : SchemeOver B} (h : τ ⟶ σ) :
    (functor f F G).map h.op = TypeCat.ofHom (baseChangeHom f F G h) :=
  sorry

end HomFunctor

end AlgebraicGeometry.AlgebraicSpace.Modules
