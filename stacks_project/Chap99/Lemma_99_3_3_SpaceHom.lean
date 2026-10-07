module

public import stacks_project.Chap99.«99_3_1_1»

/-!
# Space-level Hom pairs of quasi-coherent modules

This module extends the scheme-level Hom functor of Situation 99.3.1 to an
algebraic space `T` over `S`, via a morphism `h : T ⟶ B` and an
`𝒪_{X_T}`-module map `F_T ⟶ G_T` on the chosen pullback `X ×_{B,h} T`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open CategoryTheory.Limits Opposite

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Modules

variable {S : Scheme.{u}} {X B : AlgebraicSpace S}

/-- The pullback `F_T` of a module `F` along the projection `X ×_{B,h} T ⟶ X`. -/
abbrev spaceBaseChangeModule {T : AlgebraicSpace S} (f : X ⟶ B) (h : T ⟶ B)
    (F : X.Modules) : (Limits.pullback f h).Modules :=
  (pullback (Limits.pullback.fst f h)).obj F

/-- `spaceBaseChangeModule f h F` is module pullback of `F` along `X ×_{B,h} T ⟶ X`. -/
theorem spaceBaseChangeModule_eq {T : AlgebraicSpace S} (f : X ⟶ B) (h : T ⟶ B)
    (F : X.Modules) :
    spaceBaseChangeModule f h F = (pullback (Limits.pullback.fst f h)).obj F :=
  sorry

/-- The canonical map `X_{T'} ⟶ X_T` induced by a morphism `a : T' ⟶ T` over `B`. -/
def spaceBaseChangeMap {T T' : AlgebraicSpace S} (f : X ⟶ B) (h : T ⟶ B)
    (a : T' ⟶ T) : Limits.pullback f (a ≫ h) ⟶ Limits.pullback f h :=
  Limits.pullback.map f (a ≫ h) f h (𝟙 X) a (𝟙 B)
    ((Category.comp_id f).trans (Category.id_comp f).symm)
    (Category.comp_id (a ≫ h))

/-- The map `spaceBaseChangeMap f h a` commutes with the projections to `X`. -/
theorem spaceBaseChangeMap_fst {T T' : AlgebraicSpace S} (f : X ⟶ B) (h : T ⟶ B)
    (a : T' ⟶ T) :
    spaceBaseChangeMap f h a ≫ Limits.pullback.fst f h =
      Limits.pullback.fst f (a ≫ h) :=
  sorry

/-- The map `spaceBaseChangeMap f h a` commutes with the projections to the varying
base. -/
theorem spaceBaseChangeMap_snd {T T' : AlgebraicSpace S} (f : X ⟶ B) (h : T ⟶ B)
    (a : T' ⟶ T) :
    spaceBaseChangeMap f h a ≫ Limits.pullback.snd f h =
      Limits.pullback.snd f (a ≫ h) ≫ a :=
  sorry

/-- The comparison identifying `F_{T'}` with the pullback of `F_T` along
`X_{T'} ⟶ X_T`. -/
def spaceBaseChangeModuleIso {T T' : AlgebraicSpace S} (f : X ⟶ B) (h : T ⟶ B)
    (a : T' ⟶ T) (F : X.Modules) :
    spaceBaseChangeModule f (a ≫ h) F ≅
      (pullback (spaceBaseChangeMap f h a)).obj (spaceBaseChangeModule f h F) :=
  (pullbackCongr
      ((Limits.pullback.lift_fst (Limits.pullback.fst f (a ≫ h) ≫ 𝟙 X)
          (Limits.pullback.snd f (a ≫ h) ≫ a)
          (((Category.assoc (Limits.pullback.fst f (a ≫ h)) (𝟙 X) f).trans
              (congrArg (fun k ↦ Limits.pullback.fst f (a ≫ h) ≫ k)
                (Category.id_comp f))).trans
            ((Limits.pullback.condition :
                Limits.pullback.fst f (a ≫ h) ≫ f =
                  Limits.pullback.snd f (a ≫ h) ≫ (a ≫ h)).trans
              (Category.assoc (Limits.pullback.snd f (a ≫ h)) a h).symm))).trans
        (Category.comp_id _)).symm).app F ≪≫
    (pullbackComp (spaceBaseChangeMap f h a) (Limits.pullback.fst f h)).symm.app F

/-- Restriction of an `𝒪_{X_T}`-module map along `X_{T'} ⟶ X_T`. -/
def spaceBaseChangeHom {T T' : AlgebraicSpace S} (f : X ⟶ B) (F G : X.Modules)
    (h : T ⟶ B) (a : T' ⟶ T)
    (u : spaceBaseChangeModule f h F ⟶ spaceBaseChangeModule f h G) :
    spaceBaseChangeModule f (a ≫ h) F ⟶ spaceBaseChangeModule f (a ≫ h) G :=
  (spaceBaseChangeModuleIso f h a F).hom ≫
    (pullback (spaceBaseChangeMap f h a)).map u ≫
      (spaceBaseChangeModuleIso f h a G).inv

/-- A pair `(h, u)` consisting of a morphism `h : T ⟶ B` and an
`𝒪_{X_T}`-module map `u : F_T ⟶ G_T` on `X_T = X ×_{B,h} T`. -/
structure SpaceHom (f : X ⟶ B) (F G : X.Modules) (T : AlgebraicSpace S) :
    Type (u + 1) where
  /-- The morphism `h : T ⟶ B`. -/
  hom : T ⟶ B
  /-- The `𝒪_{X_T}`-module map `F_T ⟶ G_T`. -/
  map : spaceBaseChangeModule f hom F ⟶ spaceBaseChangeModule f hom G

namespace SpaceHom

/-- Package a morphism `h : T ⟶ B` and an `𝒪_{X_T}`-module map as a space-level
Hom pair. -/
def of {T : AlgebraicSpace S} {f : X ⟶ B} {F G : X.Modules} (h : T ⟶ B)
    (u : spaceBaseChangeModule f h F ⟶ spaceBaseChangeModule f h G) :
    SpaceHom f F G T where
  hom := h
  map := u

/-- A space-level Hom pair is a morphism `h : T ⟶ B` together with an
`𝒪_{X_T}`-module map on the pullbacks of `F` and `G` to `X ×_{B,h} T`. -/
theorem spec {T : AlgebraicSpace S} {f : X ⟶ B} {F G : X.Modules}
    (p : SpaceHom f F G T) :
    spaceBaseChangeModule f p.hom F =
        (pullback (Limits.pullback.fst f p.hom)).obj F ∧
      spaceBaseChangeModule f p.hom G =
        (pullback (Limits.pullback.fst f p.hom)).obj G :=
  sorry

/-- Pull back a pair `(h, u)` along `a : T' ⟶ T`, sending it to `(h ∘ a, a^* u)`. -/
def pullback {T T' : AlgebraicSpace S} {f : X ⟶ B} {F G : X.Modules}
    (p : SpaceHom f F G T) (a : T' ⟶ T) : SpaceHom f F G T' :=
  of (a ≫ p.hom) (spaceBaseChangeHom f F G p.hom a p.map)

/-- The morphism of a pulled-back pair is the composite `a ≫ p.hom`. -/
theorem pullback_hom {T T' : AlgebraicSpace S} {f : X ⟶ B} {F G : X.Modules}
    (p : SpaceHom f F G T) (a : T' ⟶ T) :
    (p.pullback a).hom = a ≫ p.hom :=
  sorry

/-- Convert a Hom-functor section over a scheme `σ` over `B` into a space-level
pair with structural morphism `σ.hom`. -/
def ofScheme {f : X ⟶ B} {F G : X.Modules} [F.IsQuasicoherent] [G.IsQuasicoherent]
    {σ : SchemeOver B} (u : (homFunctor f F G).obj (op σ)) :
    SpaceHom f F G (ofOver σ.left) :=
  of σ.hom u

/-- Recover a Hom-functor section from a space-level pair over `ofOver σ.left`
whose structural morphism is `σ.hom`. -/
def toScheme {f : X ⟶ B} {F G : X.Modules} [F.IsQuasicoherent] [G.IsQuasicoherent]
    {σ : SchemeOver B} (p : SpaceHom f F G (ofOver σ.left))
    (hp : p.hom = σ.hom) : (homFunctor f F G).obj (op σ) :=
  cast (congrArg
      (fun h ↦ (spaceBaseChangeModule f h F ⟶ spaceBaseChangeModule f h G)) hp)
    p.map

end SpaceHom

end AlgebraicGeometry.AlgebraicSpace.Modules
