/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Quot.Functor

/-!
# The functor of finitely presented quotients

This module constructs the contravariant subfunctor `Q^{fp}_{F/X/B}` of
`Q_{F/X/B}` consisting of those kernel-identified quasi-coherent quotients
that are of finite presentation as modules on `X_T`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open CategoryTheory.Limits Opposite

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Quot

variable {S : Scheme.{u}} {X B : AlgebraicSpace S}

/-- A finitely presented quasi-coherent quotient of `F_T` that is flat over `T`. -/
structure FpPoint (f : X ⟶ B) (F : X.Modules) (σ : SchemeOver B) where
  /-- The underlying quotient representative before kernel identification. -/
  point : Point f F σ
  /-- The target is of finite presentation. -/
  isFinitePresentation : point.module.IsFinitePresentation

namespace FpPoint

/-- Construct an `FpPoint` from an epimorphism `F_T ⟶ Q` with `Q` quasi-coherent
of finite presentation and flat over `T`. -/
def ofEpi (f : X ⟶ B) (F : X.Modules) (σ : SchemeOver B)
    (module : (fiber f σ).Modules) (map : fiberF f F σ ⟶ module)
    (map_epi : Epi map) (isQuasicoherent : module.IsQuasicoherent)
    (isFlat : Modules.flatOver module (pullback.snd f σ.hom))
    (isFinitePresentation : module.IsFinitePresentation) : FpPoint f F σ where
  point := Point.ofEpi f F σ module map map_epi isQuasicoherent isFlat
  isFinitePresentation := isFinitePresentation

/-- Convert a quotient point whose target is of finite presentation into an
`FpPoint`. -/
def ofPoint {f : X ⟶ B} {F : X.Modules} {σ : SchemeOver B}
    (Q : Point f F σ) (isFinitePresentation : Q.module.IsFinitePresentation) :
    FpPoint f F σ where
  point := Q
  isFinitePresentation := isFinitePresentation

/-- The underlying `Q_{F/X/B}`-point of a finitely presented quotient point. -/
abbrev toPoint {f : X ⟶ B} {F : X.Modules} {σ : SchemeOver B}
    (Q : FpPoint f F σ) : Point f F σ :=
  Q.point

/-- An `FpPoint` is an epimorphism `F_T ⟶ Q` with `Q` quasi-coherent of finite
presentation and flat over `T`. -/
theorem spec {f : X ⟶ B} {F : X.Modules} {σ : SchemeOver B} (Q : FpPoint f F σ) :
    Epi Q.point.map ∧ Q.point.module.IsQuasicoherent ∧
      Q.point.module.IsFinitePresentation ∧
      Modules.flatOver Q.point.module (pullback.snd f σ.hom) := sorry

/-- Pull back a finitely presented quotient point along a morphism of schemes
over `B`. -/
def pullback {f : X ⟶ B} {F : X.Modules} {σ τ : SchemeOver B}
    (Q : FpPoint f F σ) (h : τ ⟶ σ) : FpPoint f F τ where
  point := Q.point.pullback h
  isFinitePresentation := sorry

/-- The module of a pulled-back `FpPoint` is the module pullback along
`fiberMap`. -/
theorem pullback_module {f : X ⟶ B} {F : X.Modules} {σ τ : SchemeOver B}
    (Q : FpPoint f F σ) (h : τ ⟶ σ) :
    (Q.pullback h).point.module =
      (Modules.pullback (fiberMap f h)).obj Q.point.module := sorry

end FpPoint

/-- Kernel identification is an equivalence relation on finitely presented
quotient points. -/
theorem fpSetoid_isEquivalence (f : X ⟶ B) (F : X.Modules) (σ : SchemeOver B) :
    Equivalence (fun Q₁ Q₂ : FpPoint f F σ ↦ Rel Q₁.point Q₂.point) := sorry

/-- The setoid of finitely presented quotient points modulo kernel equality. -/
def fpSetoid (f : X ⟶ B) (F : X.Modules) (σ : SchemeOver B) :
    Setoid (FpPoint f F σ) where
  r Q₁ Q₂ := Rel Q₁.point Q₂.point
  iseqv := fpSetoid_isEquivalence f F σ

/-- Pullback preserves the relation of the finitely presented quotient setoid. -/
theorem fpSetoid_rel_pullback (f : X ⟶ B) (F : X.Modules)
    {σ τ : SchemeOver B} (h : τ ⟶ σ) :
    ∀ (Q₁ Q₂ : FpPoint f F σ),
      (fpSetoid f F σ).r Q₁ Q₂ →
        (fpSetoid f F τ).r (Q₁.pullback h) (Q₂.pullback h) := sorry

/-- Pullback along the identity induces the identity on kernel-identified
finitely presented quotient classes. -/
theorem fp_map_id (f : X ⟶ B) (F : X.Modules) (σ : (SchemeOver B)ᵒᵖ) :
    TypeCat.ofHom
      (_root_.Quotient.map (fun Q : FpPoint f F σ.unop ↦ Q.pullback (𝟙 σ).unop)
        (fpSetoid_rel_pullback f F (𝟙 σ).unop)) =
      𝟙 (_root_.Quotient (fpSetoid f F σ.unop)) := sorry

/-- Pullback along a composite induces the composite of the pullback maps on
finitely presented quotient classes. -/
theorem fp_map_comp (f : X ⟶ B) (F : X.Modules)
    {σ τ ρ : (SchemeOver B)ᵒᵖ} (h : σ ⟶ τ) (k : τ ⟶ ρ) :
    TypeCat.ofHom
      (_root_.Quotient.map (fun Q : FpPoint f F σ.unop ↦ Q.pullback (h ≫ k).unop)
        (fpSetoid_rel_pullback f F (h ≫ k).unop)) =
      TypeCat.ofHom
          (_root_.Quotient.map (fun Q : FpPoint f F σ.unop ↦ Q.pullback h.unop)
            (fpSetoid_rel_pullback f F h.unop)) ≫
        TypeCat.ofHom
          (_root_.Quotient.map (fun Q : FpPoint f F τ.unop ↦ Q.pullback k.unop)
            (fpSetoid_rel_pullback f F k.unop)) := sorry

/-- The contravariant functor `Q^{fp}_{F/X/B}` of finitely presented
quasi-coherent quotients of `F` along `f : X ⟶ B`, identified by kernels. -/
def fpFunctor (f : X ⟶ B) (F : X.Modules) [F.IsQuasicoherent] :
    (SchemeOver B)ᵒᵖ ⥤ Type (u + 1) where
  obj σ := _root_.Quotient (fpSetoid f F σ.unop)
  map {σ τ} (h : σ ⟶ τ) :=
    TypeCat.ofHom
      (_root_.Quotient.map (fun Q : FpPoint f F σ.unop ↦ Q.pullback h.unop)
        (fpSetoid_rel_pullback f F h.unop))
  map_id := fp_map_id f F
  map_comp := fp_map_comp f F

/-- The value of the finitely presented quotient functor is the setoid quotient
of `FpPoint`s by kernels. -/
theorem fpFunctor_obj (f : X ⟶ B) (F : X.Modules) [F.IsQuasicoherent]
    (σ : SchemeOver B) :
    (fpFunctor f F).obj (op σ) = _root_.Quotient (fpSetoid f F σ) := sorry

/-- The finitely presented quotient functor acts on a morphism by pullback of
`FpPoint`s. -/
theorem fpFunctor_map (f : X ⟶ B) (F : X.Modules) [F.IsQuasicoherent]
    {σ τ : (SchemeOver B)ᵒᵖ} (h : σ ⟶ τ) :
    (fpFunctor f F).map h =
      TypeCat.ofHom
        (_root_.Quotient.map (fun Q : FpPoint f F σ.unop ↦ Q.pullback h.unop)
          (fpSetoid_rel_pullback f F h.unop)) := sorry

/-- The forgetful map from finitely presented quotient points to quotient points
preserves kernel identification. -/
theorem fpToPoint_rel (f : X ⟶ B) (F : X.Modules) (σ : SchemeOver B) :
    ∀ (Q₁ Q₂ : FpPoint f F σ),
      (fpSetoid f F σ).r Q₁ Q₂ →
        (quotientSetoid f F σ).r Q₁.toPoint Q₂.toPoint := sorry

/-- The inclusion of `Q^{fp}_{F/X/B}` as a subfunctor of `Q_{F/X/B}`. -/
def fpι (f : X ⟶ B) (F : X.Modules) [F.IsQuasicoherent] :
    fpFunctor f F ⟶ functor f F where
  app σ :=
    TypeCat.ofHom
      (_root_.Quotient.map (fun Q : FpPoint f F σ.unop ↦ Q.toPoint)
        (fpToPoint_rel f F σ.unop))
  naturality := sorry

/-- The inclusion of finitely presented quotient classes is the setoid map
induced by `FpPoint.toPoint`. -/
theorem fpι_app (f : X ⟶ B) (F : X.Modules) [F.IsQuasicoherent]
    (σ : (SchemeOver B)ᵒᵖ) :
    (fpι f F).app σ =
      TypeCat.ofHom
        (_root_.Quotient.map (fun Q : FpPoint f F σ.unop ↦ Q.toPoint)
          (fpToPoint_rel f F σ.unop)) := sorry

/-- Each component of the forgetful inclusion of finitely presented quotient
classes into quotient classes is injective. -/
theorem fpι_app_injective (f : X ⟶ B) (F : X.Modules) [F.IsQuasicoherent]
    (σ : (SchemeOver B)ᵒᵖ) :
    Function.Injective ((fpι f F).app σ) := sorry

end AlgebraicGeometry.AlgebraicSpace.Quot
