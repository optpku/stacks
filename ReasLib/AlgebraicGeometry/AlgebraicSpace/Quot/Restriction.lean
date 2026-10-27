/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Quot.FinitePresentation
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.InverseImage
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Flat

/-!
# Flat restriction of quotient points

Quotient representatives and their kernel classes restrict along flat morphisms of total
spaces, and transport along isomorphisms of their source modules.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open CategoryTheory.Limits Opposite

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Quot

variable {S : Scheme.{u}} {X B : AlgebraicSpace S}

/-- The canonical map `X'_T ⟶ X_T` induced by `φ : X' ⟶ X`. -/
def restrictSpaceMap (f : X ⟶ B) {X' : AlgebraicSpace S} (φ : X' ⟶ X)
    (σ : SchemeOver B) : fiber (φ ≫ f) σ ⟶ fiber f σ :=
  pullback.lift (pullback.fst (φ ≫ f) σ.hom ≫ φ) (pullback.snd (φ ≫ f) σ.hom)
    ((Category.assoc (pullback.fst (φ ≫ f) σ.hom) φ f).trans
      (pullback.condition :
        pullback.fst (φ ≫ f) σ.hom ≫ φ ≫ f =
          pullback.snd (φ ≫ f) σ.hom ≫ σ.hom))

/-- `restrictSpaceMap` commutes with the projections to `X`. -/
theorem restrictSpaceMap_comp_proj (f : X ⟶ B) {X' : AlgebraicSpace S} (φ : X' ⟶ X)
    (σ : SchemeOver B) :
    restrictSpaceMap f φ σ ≫ pullback.fst f σ.hom =
      pullback.fst (φ ≫ f) σ.hom ≫ φ :=
  pullback.lift_fst (pullback.fst (φ ≫ f) σ.hom ≫ φ) (pullback.snd (φ ≫ f) σ.hom)
    ((Category.assoc (pullback.fst (φ ≫ f) σ.hom) φ f).trans
      (pullback.condition :
        pullback.fst (φ ≫ f) σ.hom ≫ φ ≫ f =
          pullback.snd (φ ≫ f) σ.hom ≫ σ.hom))

/-- Identification of `(φ^* F)_T` with the pullback of `F_T` along `X'_T ⟶ X_T`. -/
def restrictFiberFIso (f : X ⟶ B) {X' : AlgebraicSpace S} (φ : X' ⟶ X)
    (σ : SchemeOver B) (F : X.Modules) :
    fiberF (φ ≫ f) ((Modules.pullback φ).obj F) σ ≅
      (Modules.pullback (restrictSpaceMap f φ σ)).obj (fiberF f F σ) :=
  (Modules.pullbackCompIso (pullback.fst (φ ≫ f) σ.hom) φ).app F ≪≫
    eqToIso (congrArg (fun ψ ↦ (Modules.pullback ψ).obj F)
      (restrictSpaceMap_comp_proj f φ σ).symm) ≪≫
    (Modules.pullbackCompIso (restrictSpaceMap f φ σ)
      (pullback.fst f σ.hom)).symm.app F

namespace Point

/-- Transporting the source of a quotient along a module isomorphism preserves
surjectivity of its quotient morphism. -/
theorem congrModule_properties {X' : AlgebraicSpace S} {α : X' ⟶ B}
    {F G : X'.Modules} {σ : SchemeOver B} (e : F ≅ G) (Q : Point α F σ) :
    Epi ((Modules.pullback (pullback.fst α σ.hom)).map e.inv ≫ Q.map) := sorry

/-- Source-transport a quotient point along an isomorphism of the ambient module
`F_T`. -/
def congrModule {X' : AlgebraicSpace S} {α : X' ⟶ B} {F G : X'.Modules}
    {σ : SchemeOver B} (e : F ≅ G) (Q : Point α F σ) : Point α G σ where
  module := Q.module
  map := (Modules.pullback (pullback.fst α σ.hom)).map e.inv ≫ Q.map
  map_epi := congrModule_properties e Q
  isQuasicoherent := Q.isQuasicoherent
  isFlat := Q.isFlat

/-- Transport a quotient point along an equality of structure morphisms over `B`
and an isomorphism of source modules. -/
def congr {X' : AlgebraicSpace S} {α β : X' ⟶ B} (h : α = β) {F G : X'.Modules}
    (e : F ≅ G) {σ : SchemeOver B} (Q : Point α F σ) : Point β G σ :=
  eqToHom (congrArg (fun γ ↦ Point γ G σ) h) (Q.congrModule e)

/-- Flat restriction of a quotient preserves surjectivity, quasi-coherence and
flatness over the test scheme. -/
theorem restrictAlong_properties {f : X ⟶ B} {F : X.Modules} {σ : SchemeOver B}
    {X' : AlgebraicSpace S} (Q : Point f F σ) (φ : X' ⟶ X) (hflat : Flat φ) :
    Epi ((restrictFiberFIso f φ σ F).hom ≫
      (Modules.pullback (restrictSpaceMap f φ σ)).map Q.map) ∧
    ((Modules.pullback (restrictSpaceMap f φ σ)).obj Q.module).IsQuasicoherent ∧
    Modules.flatOver ((Modules.pullback (restrictSpaceMap f φ σ)).obj Q.module)
      (pullback.snd (φ ≫ f) σ.hom) := sorry

/-- Restriction of a quotient point of `F_T` along `φ : X' ⟶ X`. -/
def restrictAlong {f : X ⟶ B} {F : X.Modules} {σ : SchemeOver B}
    {X' : AlgebraicSpace S} (Q : Point f F σ) (φ : X' ⟶ X) (hflat : Flat φ) :
    Point (φ ≫ f) ((Modules.pullback φ).obj F) σ where
  module := (Modules.pullback (restrictSpaceMap f φ σ)).obj Q.module
  map := (restrictFiberFIso f φ σ F).hom ≫
    (Modules.pullback (restrictSpaceMap f φ σ)).map Q.map
  map_epi := (restrictAlong_properties Q φ hflat).1
  isQuasicoherent := (restrictAlong_properties Q φ hflat).2.1
  isFlat := (restrictAlong_properties Q φ hflat).2.2

/-- The module of a restricted quotient point is the module pullback along
`restrictSpaceMap`. -/
theorem restrictAlong_module {f : X ⟶ B} {F : X.Modules} {σ : SchemeOver B}
    {X' : AlgebraicSpace S} (Q : Point f F σ) (φ : X' ⟶ X) (hflat : Flat φ) :
    (Q.restrictAlong φ hflat).module =
      (Modules.pullback (restrictSpaceMap f φ σ)).obj Q.module :=
  rfl

/-- The restricted quotient map is the pullback of `Q.map` after
`restrictFiberFIso`. -/
theorem restrictAlong_map {f : X ⟶ B} {F : X.Modules} {σ : SchemeOver B}
    {X' : AlgebraicSpace S} (Q : Point f F σ) (φ : X' ⟶ X) (hflat : Flat φ) :
    (Q.restrictAlong φ hflat).map =
      (restrictFiberFIso f φ σ F).hom ≫
        (Modules.pullback (restrictSpaceMap f φ σ)).map Q.map :=
  rfl

end Point

/-- Restriction of quotient points along `φ : X' ⟶ X` preserves kernel
identification. -/
theorem restrictAlong_rel (f : X ⟶ B) (F : X.Modules) {X' : AlgebraicSpace S}
    (φ : X' ⟶ X) (hflat : Flat φ) (σ : SchemeOver B) :
    ∀ (Q₁ Q₂ : Point f F σ),
      (quotientSetoid f F σ).r Q₁ Q₂ →
        (quotientSetoid (φ ≫ f) ((Modules.pullback φ).obj F) σ).r
          (Q₁.restrictAlong φ hflat) (Q₂.restrictAlong φ hflat) :=
  sorry

/-- Restriction of kernel-identified quotients of `F_T` along `φ : X' ⟶ X`. -/
def restrictAlong (f : X ⟶ B) (F : X.Modules) [F.IsQuasicoherent]
    {X' : AlgebraicSpace S} (φ : X' ⟶ X) (hflat : Flat φ) (σ : SchemeOver B) :
    (functor f F).obj (op σ) →
      (functor (φ ≫ f) ((Modules.pullback φ).obj F)).obj (op σ) :=
  _root_.Quotient.map (fun Q : Point f F σ ↦ Q.restrictAlong φ hflat)
    (restrictAlong_rel f F φ hflat σ)

/-- Restriction of kernel-identified quotients evaluates on a representative by
`Point.restrictAlong`. -/
theorem restrictAlong_apply (f : X ⟶ B) (F : X.Modules) [F.IsQuasicoherent]
    {X' : AlgebraicSpace S} (φ : X' ⟶ X) (hflat : Flat φ) (σ : SchemeOver B)
    (Q : Point f F σ) :
    restrictAlong f F φ hflat σ (Quotient.mk (quotientSetoid f F σ) Q) =
      Quotient.mk (quotientSetoid (φ ≫ f) ((Modules.pullback φ).obj F) σ)
        (Q.restrictAlong φ hflat) :=
  rfl

namespace FpPoint

/-- Source-transport a finitely presented quotient point along an isomorphism of
the ambient module `F_T`. -/
def congrModule {X' : AlgebraicSpace S} {α : X' ⟶ B} {F G : X'.Modules}
    {σ : SchemeOver B} (e : F ≅ G) (Q : FpPoint α F σ) : FpPoint α G σ where
  point := Q.point.congrModule e
  isFinitePresentation := Q.isFinitePresentation

/-- Transport a finitely presented quotient point along an equality of structure
morphisms over `B` and an isomorphism of source modules. -/
def congr {X' : AlgebraicSpace S} {α β : X' ⟶ B} (h : α = β) {F G : X'.Modules}
    (e : F ≅ G) {σ : SchemeOver B} (Q : FpPoint α F σ) : FpPoint β G σ :=
  eqToHom (congrArg (fun γ ↦ FpPoint γ G σ) h) (Q.congrModule e)

/-- The pullback of a finitely presented quotient target along a flat restriction
is finitely presented. -/
theorem restrictAlong_finitePresentation {f : X ⟶ B} {F : X.Modules}
    {σ : SchemeOver B} {X' : AlgebraicSpace S} (Q : FpPoint f F σ)
    (φ : X' ⟶ X) (hflat : Flat φ) :
    ((Modules.pullback (restrictSpaceMap f φ σ)).obj Q.point.module).IsFinitePresentation := sorry

/-- Restriction of a finitely presented quotient point of `F_T` along
`φ : X' ⟶ X`. -/
def restrictAlong {f : X ⟶ B} {F : X.Modules} {σ : SchemeOver B}
    {X' : AlgebraicSpace S} (Q : FpPoint f F σ) (φ : X' ⟶ X) (hflat : Flat φ) :
    FpPoint (φ ≫ f) ((Modules.pullback φ).obj F) σ where
  point := Q.point.restrictAlong φ hflat
  isFinitePresentation := restrictAlong_finitePresentation Q φ hflat

/-- The underlying point of a restricted `FpPoint` is the restricted point. -/
theorem restrictAlong_point {f : X ⟶ B} {F : X.Modules} {σ : SchemeOver B}
    {X' : AlgebraicSpace S} (Q : FpPoint f F σ) (φ : X' ⟶ X) (hflat : Flat φ) :
    (Q.restrictAlong φ hflat).point = Q.point.restrictAlong φ hflat :=
  rfl

end FpPoint

/-- Restriction of finitely presented quotient points along `φ : X' ⟶ X`
preserves kernel identification. -/
theorem fpRestrictAlong_rel (f : X ⟶ B) (F : X.Modules) {X' : AlgebraicSpace S}
    (φ : X' ⟶ X) (hflat : Flat φ) (σ : SchemeOver B) :
    ∀ (Q₁ Q₂ : FpPoint f F σ),
      (fpSetoid f F σ).r Q₁ Q₂ →
        (fpSetoid (φ ≫ f) ((Modules.pullback φ).obj F) σ).r
          (Q₁.restrictAlong φ hflat) (Q₂.restrictAlong φ hflat) :=
  sorry

/-- Restriction of kernel-identified finitely presented quotients of `F_T` along
`φ : X' ⟶ X`. -/
def fpRestrictAlong (f : X ⟶ B) (F : X.Modules) [F.IsQuasicoherent]
    {X' : AlgebraicSpace S} (φ : X' ⟶ X) (hflat : Flat φ) (σ : SchemeOver B) :
    (fpFunctor f F).obj (op σ) →
      (fpFunctor (φ ≫ f) ((Modules.pullback φ).obj F)).obj (op σ) :=
  _root_.Quotient.map (fun Q : FpPoint f F σ ↦ Q.restrictAlong φ hflat)
    (fpRestrictAlong_rel f F φ hflat σ)

/-- Restriction of finitely presented quotient classes evaluates on a
representative by `FpPoint.restrictAlong`. -/
theorem fpRestrictAlong_apply (f : X ⟶ B) (F : X.Modules) [F.IsQuasicoherent]
    {X' : AlgebraicSpace S} (φ : X' ⟶ X) (hflat : Flat φ) (σ : SchemeOver B)
    (Q : FpPoint f F σ) :
    fpRestrictAlong f F φ hflat σ (Quotient.mk (fpSetoid f F σ) Q) =
      Quotient.mk (fpSetoid (φ ≫ f) ((Modules.pullback φ).obj F) σ)
        (Q.restrictAlong φ hflat) :=
  rfl

/-- Transport of kernel-identified quotients along an equality of structure
morphisms over `B` preserves kernel identification. -/
theorem functorCongr_rel {X' : AlgebraicSpace S} {α β : X' ⟶ B} (h : α = β)
    {F G : X'.Modules} (e : F ≅ G) (σ : SchemeOver B) :
    ∀ (Q₁ Q₂ : Point α F σ),
      (quotientSetoid α F σ).r Q₁ Q₂ →
        (quotientSetoid β G σ).r (Point.congr h e Q₁) (Point.congr h e Q₂) :=
  sorry

/-- Transport of kernel-identified quotients along an equality of structure
morphisms over `B` and an isomorphism of source modules. -/
def functorCongr {X' : AlgebraicSpace S} {α β : X' ⟶ B} (h : α = β)
    {F G : X'.Modules} [F.IsQuasicoherent] [G.IsQuasicoherent] (e : F ≅ G)
    (σ : SchemeOver B) :
    (functor α F).obj (op σ) → (functor β G).obj (op σ) :=
  _root_.Quotient.map (fun Q : Point α F σ ↦ Point.congr h e Q)
    (functorCongr_rel h e σ)

/-- Transport of finitely presented quotient classes along an equality of
structure morphisms over `B` preserves kernel identification. -/
theorem fpFunctorCongr_rel {X' : AlgebraicSpace S} {α β : X' ⟶ B} (h : α = β)
    {F G : X'.Modules} (e : F ≅ G) (σ : SchemeOver B) :
    ∀ (Q₁ Q₂ : FpPoint α F σ),
      (fpSetoid α F σ).r Q₁ Q₂ →
        (fpSetoid β G σ).r (FpPoint.congr h e Q₁) (FpPoint.congr h e Q₂) :=
  sorry

/-- Transport of finitely presented quotient classes along an equality of
structure morphisms over `B` and an isomorphism of source modules. -/
def fpFunctorCongr {X' : AlgebraicSpace S} {α β : X' ⟶ B} (h : α = β)
    {F G : X'.Modules} [F.IsQuasicoherent] [G.IsQuasicoherent] (e : F ≅ G)
    (σ : SchemeOver B) :
    (fpFunctor α F).obj (op σ) → (fpFunctor β G).obj (op σ) :=
  _root_.Quotient.map (fun Q : FpPoint α F σ ↦ FpPoint.congr h e Q)
    (fpFunctorCongr_rel h e σ)

end AlgebraicGeometry.AlgebraicSpace.Quot
