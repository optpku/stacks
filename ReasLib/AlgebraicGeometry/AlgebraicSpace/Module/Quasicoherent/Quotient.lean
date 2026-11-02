/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Subobject.Limits
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Abelian
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.InverseImage
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.DirectImage

/-!
# Quasi-coherent quotients of a module on an algebraic space

A quasi-coherent quotient of a quasi-coherent module `F` on an algebraic space is an
epimorphism `F ⟶ Q` with `Q` quasi-coherent. Quotients are identified when they have
the same kernel.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open CategoryTheory.Limits

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.QCoh

variable {S : Scheme.{u}} {X : AlgebraicSpace S}

/-- A quasi-coherent quotient of a quasi-coherent `𝒪_X`-module `F`. -/
structure Quotient (F : X.Modules) [F.IsQuasicoherent] where
  /-- The target module sheaf of the quotient. -/
  module : X.Modules
  /-- The quotient morphism from `F`. -/
  map : F ⟶ module
  /-- The quotient morphism is an epimorphism. -/
  map_epi : Epi map
  /-- The target is quasi-coherent. -/
  isQuasicoherent : module.IsQuasicoherent

namespace Quotient

/-- Construct a quasi-coherent quotient from an epimorphism `F ⟶ Q` with `Q`
quasi-coherent. -/
def ofEpi (F : X.Modules) [F.IsQuasicoherent] (module : X.Modules) (map : F ⟶ module)
    (map_epi : Epi map) (isQuasicoherent : module.IsQuasicoherent) : Quotient F where
  module := module
  map := map
  map_epi := map_epi
  isQuasicoherent := isQuasicoherent

/-- A quasi-coherent quotient is an epimorphism onto a quasi-coherent module. -/
theorem spec {F : X.Modules} [F.IsQuasicoherent] (Q : Quotient F) :
    Epi Q.map ∧ Q.module.IsQuasicoherent :=
  ⟨Q.map_epi, Q.isQuasicoherent⟩

/-- Two quasi-coherent quotients of `F` are identified when they have the same kernel. -/
def Rel {F : X.Modules} [F.IsQuasicoherent] (Q₁ Q₂ : Quotient F) : Prop :=
  kernelSubobject Q₁.map = kernelSubobject Q₂.map

/-- Kernel equality is an equivalence relation on quasi-coherent quotients. -/
theorem rel_isEquivalence (F : X.Modules) [F.IsQuasicoherent] :
    Equivalence (fun Q₁ Q₂ : Quotient F ↦ Rel Q₁ Q₂) :=
  ⟨fun _ ↦ rfl, fun h ↦ h.symm, fun h₁ h₂ ↦ h₁.trans h₂⟩

/-- Kernel identification of quasi-coherent quotients is equivalent to an isomorphism of
targets over `F`. -/
theorem rel_iso_iff {F : X.Modules} [F.IsQuasicoherent] (Q₁ Q₂ : Quotient F) :
    Rel Q₁ Q₂ ↔ ∃ e : Q₁.module ≅ Q₂.module, Q₁.map ≫ e.hom = Q₂.map := by
  letI := Q₁.map_epi
  letI := Q₂.map_epi
  constructor
  · intro h
    change kernelSubobject Q₁.map = kernelSubobject Q₂.map at h
    have h₁₂ : kernel.ι Q₁.map ≫ Q₂.map = 0 := by
      apply (kernelSubobject_factors_iff Q₂.map _).mp
      rw [← h]
      exact kernelSubobject_factors Q₁.map _ (kernel.condition _)
    have h₂₁ : kernel.ι Q₂.map ≫ Q₁.map = 0 := by
      apply (kernelSubobject_factors_iff Q₁.map _).mp
      rw [h]
      exact kernelSubobject_factors Q₂.map _ (kernel.condition _)
    refine ⟨
      { hom := Abelian.epiDesc Q₁.map Q₂.map h₁₂
        inv := Abelian.epiDesc Q₂.map Q₁.map h₂₁
        hom_inv_id := ?_
        inv_hom_id := ?_ }, Abelian.comp_epiDesc _ _ _⟩
    · apply (cancel_epi Q₁.map).mp
      simp only [← Category.assoc, Abelian.comp_epiDesc, Category.comp_id]
    · apply (cancel_epi Q₂.map).mp
      simp only [← Category.assoc, Abelian.comp_epiDesc, Category.comp_id]
  · rintro ⟨e, he⟩
    change kernelSubobject Q₁.map = kernelSubobject Q₂.map
    rw [← he, kernelSubobject_comp_mono]

/-- Precompose a quasi-coherent quotient with an isomorphism of its source. -/
def precomposeIso {F F' : X.Modules} [F.IsQuasicoherent] [F'.IsQuasicoherent]
    (e : F ≅ F') (Q : Quotient F') : Quotient F where
  module := Q.module
  map := e.hom ≫ Q.map
  map_epi := by
    letI := Q.map_epi
    exact epi_comp _ _
  isQuasicoherent := Q.isQuasicoherent

/-- The target of `precomposeIso e Q` is the target of `Q`. -/
theorem precomposeIso_module {F F' : X.Modules} [F.IsQuasicoherent] [F'.IsQuasicoherent]
    (e : F ≅ F') (Q : Quotient F') :
    (precomposeIso e Q).module = Q.module := rfl

/-- The underlying map of `precomposeIso e Q` is `e.hom ≫ Q.map`. -/
theorem precomposeIso_map {F F' : X.Modules} [F.IsQuasicoherent] [F'.IsQuasicoherent]
    (e : F ≅ F') (Q : Quotient F') :
    (precomposeIso e Q).map = e.hom ≫ Q.map := rfl

/-- Pull back a quasi-coherent quotient along a morphism of algebraic spaces. -/
def pullback {F : X.Modules} [F.IsQuasicoherent] (Q : Quotient F)
    {Y : AlgebraicSpace S} (f : Y ⟶ X) :
    Quotient ((Modules.pullback f).obj F) where
  module := (Modules.pullback f).obj Q.module
  map := (Modules.pullback f).map Q.map
  map_epi := by
    letI := Q.map_epi
    exact (Modules.pullback f).map_epi Q.map
  isQuasicoherent := Modules.pullback_quasiCoherentModuleProperty f Q.isQuasicoherent

/-- The module of a pulled-back quotient is the module pullback of the original target. -/
theorem pullback_module {F : X.Modules} [F.IsQuasicoherent] (Q : Quotient F)
    {Y : AlgebraicSpace S} (f : Y ⟶ X) :
    (Q.pullback f).module = (Modules.pullback f).obj Q.module := rfl

/-- Pullback preserves kernel identification of quasi-coherent quotients. -/
theorem rel_pullback {F : X.Modules} [F.IsQuasicoherent] {Q₁ Q₂ : Quotient F}
    (hQ : Rel Q₁ Q₂) {Y : AlgebraicSpace S} (f : Y ⟶ X) :
    Rel (Q₁.pullback f) (Q₂.pullback f) := by
  obtain ⟨e, he⟩ := (rel_iso_iff Q₁ Q₂).mp hQ
  apply (rel_iso_iff _ _).mpr
  refine ⟨(Modules.pullback f).mapIso e, ?_⟩
  change (Modules.pullback f).map Q₁.map ≫ (Modules.pullback f).map e.hom =
    (Modules.pullback f).map Q₂.map
  rw [← Functor.map_comp, he]

end Quotient

/-- The setoid of quasi-coherent quotients of `F` modulo kernel equality. -/
def quotientSetoid (F : X.Modules) [F.IsQuasicoherent] : Setoid (Quotient F) where
  r := Quotient.Rel
  iseqv := Quotient.rel_isEquivalence F

/-- Kernel-identified quasi-coherent quotients of `F`. -/
def quotients (F : X.Modules) [F.IsQuasicoherent] :=
  _root_.Quotient (quotientSetoid F)

end AlgebraicGeometry.AlgebraicSpace.QCoh

