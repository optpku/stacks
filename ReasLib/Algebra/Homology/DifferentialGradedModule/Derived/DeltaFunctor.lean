/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Homology.DifferentialGradedModule.Abelian
public import ReasLib.Algebra.Homology.DifferentialGradedModule.Derived.Hom
public import ReasLib.Algebra.Homology.DifferentialGradedModule.Derived.FromModules
public import ReasLib.Algebra.Homology.DifferentialGradedModule.MappingCone.Triangle
public import ReasLib.CategoryTheory.Pretriangulated.DeltaFunctor.Definition
public import Mathlib.Tactic.CrossRefAttribute

/-!
# The Delta Functor to the Derived Category of a DG Algebra

An arbitrary short exact sequence of right differential graded modules is compared with the
mapping cone of its first map.  The cone-to-quotient comparison is a quasi-isomorphism, so its
inverse after localization gives the canonical connecting morphism.  The resulting construction
packages `DifferentialGradedModule.Derived.fromModules` as a reusable `DeltaFunctor`.
-/

@[expose] public section

noncomputable section

universe u v

open CategoryTheory CategoryTheory.Pretriangulated DifferentialGradedCategory
open scoped DifferentialGradedCategory DifferentialGradedModule

namespace DifferentialGradedModule.Derived.Delta

variable {R : Type u} [CommRing R]
variable {A : CochainDGAlgebra.{u, v} R}
variable (S : ShortComplex (DifferentialGradedModule.{u, v} A))

/-- The canonical map from the mapping cone of the first arrow of a short complex to its third
object.  In degree `n` it is projection to `S.X₂.X n` followed by `S.g`. -/
def coneProjection : mappingCone S.f ⟶ S.X₃ where
  hom n := (S.g.hom n).comp (LinearMap.fst R (S.X₂.X n) (S.X₁.X (n + 1)))
  comm_d n x := by
    rcases x with ⟨x, y⟩
    have h := congrArg (fun z ↦ z.hom (n + 1) y) S.zero
    change S.g.hom (n + 1) (S.f.hom (n + 1) y) = 0 at h
    change S.g.hom (n + 1) (S.X₂.d n x + S.f.hom (n + 1) y) =
      S.X₃.d n (S.g.hom n x)
    rw [map_add, h, add_zero, S.g.comm_d]
  comm_smul p i x a := by
    change S.g.hom (p + i) (S.X₂.smul p i x.1 a) =
      S.X₃.smul p i (S.g.hom p x.1) a
    exact S.g.comm_smul p i x.1 a

/-- The cone projection is degreewise the first coordinate followed by the second arrow of the
short complex. -/
@[simp]
theorem coneProjection_hom (n : ℤ) :
    (coneProjection S).hom n =
      (S.g.hom n).comp (LinearMap.fst R (S.X₂.X n) (S.X₁.X (n + 1))) := rfl

/-- The mapping-cone inclusion followed by the cone projection is the second arrow of the short
complex. -/
@[reassoc]
theorem inclusion_coneProjection :
    MappingCone.inclusion S.f ≫ coneProjection S = S.g := by
  apply DifferentialGradedModule.hom_ext
  intro n x
  change (S.g.hom n)
      (LinearMap.fst R (S.X₂.X n) (S.X₁.X (n + 1))
        (LinearMap.inl R (S.X₂.X n) (S.X₁.X (n + 1)) x)) = S.g.hom n x
  simp

/-- Cone projection is natural in morphisms of short complexes. -/
theorem coneProjection_naturality
    {T : ShortComplex (DifferentialGradedModule.{u, v} A)} (φ : S ⟶ T) :
    MappingCone.map φ.τ₁ φ.τ₂ φ.comm₁₂.symm ≫ coneProjection T =
      coneProjection S ≫ φ.τ₃ := by
  apply DifferentialGradedModule.hom_ext
  intro n x
  rcases x with ⟨x, y⟩
  change (T.g.hom n) (φ.τ₂.hom n x) = φ.τ₃.hom n (S.g.hom n x)
  have h := congrArg (fun z ↦ z.hom n x) φ.comm₂₃
  change (T.g.hom n) (φ.τ₂.hom n x) = φ.τ₃.hom n (S.g.hom n x) at h
  exact h

/-- For a short exact sequence, the cone projection is a quasi-isomorphism in the intrinsic DG
homotopy category. -/
theorem coneProjection_quasiIso (hS : S.ShortExact) :
    quasiIso A ((toK A).map (coneProjection S)) := sorry

/-- The canonical comparison between the mapping cone and the quotient term of a short exact
sequence after localization. -/
noncomputable def coneIso (hS : S.ShortExact) :
    (fromModules A).obj (mappingCone S.f) ≅ (fromModules A).obj S.X₃ :=
  Localization.isoOfHom (Q A) (quasiIso A) ((toK A).map (coneProjection S))
    (coneProjection_quasiIso S hS)

/-- The forward map of the localized cone comparison is the derived image of the cone
projection. -/
@[simp]
theorem coneIso_hom (hS : S.ShortExact) :
    (coneIso S hS).hom = (fromModules A).map (coneProjection S) := by
  simp [coneIso, fromModules_map]

/-- The connecting morphism of a short exact sequence of right DG modules.  It is the inverse of
the localized cone projection followed by the third map of the mapping-cone triangle. -/
@[stacks 09L0 "connecting morphism for a short exact sequence of DG modules"]
noncomputable def δ (hS : S.ShortExact) :
    (fromModules A).obj S.X₃ ⟶ ((fromModules A).obj S.X₁)⟦(1 : ℤ)⟧ :=
  (coneIso S hS).inv ≫
    (fromModules A).map (MappingCone.toShift S.f) ≫
      (toKShiftIso S.X₁ (1 : ℤ)).hom

/-- After precomposition with the cone comparison, the connecting morphism is the third map of
the localized mapping-cone triangle. -/
@[reassoc]
theorem coneIso_hom_δ (hS : S.ShortExact) :
    (coneIso S hS).hom ≫ δ S hS =
      (fromModules A).map (MappingCone.toShift S.f) ≫
        (toKShiftIso S.X₁ (1 : ℤ)).hom := by
  dsimp [δ]
  simp only [Iso.hom_inv_id_assoc]
  rfl

/-- The canonical triangle attached to a short exact sequence of right DG modules. -/
noncomputable def triangle (hS : S.ShortExact) : Triangle (Category A) :=
  Triangle.mk ((fromModules A).map S.f) ((fromModules A).map S.g) (δ S hS)

set_option backward.isDefEq.respectTransparency false in
/-- Lemma 22.23.1 (09L0): the canonical triangle attached to a short exact sequence of right DG
modules is distinguished in the derived category. -/
@[stacks 09L0 "short exact sequences give distinguished triangles in the DG derived category"]
theorem triangle_distinguished (hS : S.ShortExact) :
    triangle S hS ∈ distTriang (Category A) := by
  let T := (Q A).mapTriangle.obj (MappingCone.triangleK S.f)
  have hT : T ∈ distTriang (Category A) :=
    (Q A).map_distinguished _ (Homotopy.mappingCone_triangleK_distinguished A S.f)
  have e : T ≅ triangle S hS := by
    refine Triangle.isoMk _ _ (Iso.refl _) (Iso.refl _) (coneIso S hS) ?_ ?_ ?_
    · change (fromModules A).map S.f ≫ (𝟙 _) = (𝟙 _) ≫ (fromModules A).map S.f
      simp only [Category.comp_id, Category.id_comp]
    · change (fromModules A).map (MappingCone.inclusion S.f) ≫ (coneIso S hS).hom =
        (𝟙 _) ≫ (fromModules A).map S.g
      rw [coneIso_hom, ← Functor.map_comp, inclusion_coneProjection, Category.id_comp]
    · change ((Q A).map ((toK A).map (MappingCone.toShift S.f) ≫
          ((toK A).commShiftIso (1 : ℤ)).hom.app S.X₁) ≫
          ((Q A).commShiftIso (1 : ℤ)).hom.app ((toK A).obj S.X₁)) ≫ (𝟙 _)⟦(1 : ℤ)⟧' =
        (coneIso S hS).hom ≫ δ S hS
      erw [CategoryTheory.Functor.map_id, Category.comp_id, coneIso_hom_δ,
        toKShiftIso_hom, fromModules_map, Functor.map_comp]
      exact Category.assoc _ _ _
  exact isomorphic_distinguished _ hT _ e.symm

set_option backward.isDefEq.respectTransparency false in
/-- Connecting morphisms of short exact DG-module sequences are natural. -/
theorem δ_naturality
    {T : ShortComplex (DifferentialGradedModule.{u, v} A)}
    (hS : S.ShortExact) (hT : T.ShortExact) (φ : S ⟶ T) :
    CommSq ((fromModules A).map φ.τ₃) (δ S hS) (δ T hT)
      (((fromModules A).map φ.τ₁)⟦(1 : ℤ)⟧') := by
  let ψ := (Q A).mapTriangle.map
    (MappingCone.triangleMapK φ.τ₁ φ.τ₂ φ.comm₁₂.symm)
  have h := ψ.comm₃
  change ((Q A).map ((toK A).map (MappingCone.toShift S.f) ≫
      ((toK A).commShiftIso (1 : ℤ)).hom.app S.X₁) ≫
      ((Q A).commShiftIso (1 : ℤ)).hom.app ((toK A).obj S.X₁)) ≫
      (((fromModules A).map φ.τ₁)⟦(1 : ℤ)⟧') =
    (fromModules A).map (MappingCone.map φ.τ₁ φ.τ₂ φ.comm₁₂.symm) ≫
      (Q A).map ((toK A).map (MappingCone.toShift T.f) ≫
        ((toK A).commShiftIso (1 : ℤ)).hom.app T.X₁) ≫
      ((Q A).commShiftIso (1 : ℤ)).hom.app ((toK A).obj T.X₁) at h
  simp only [Functor.map_comp, Category.assoc] at h
  have hb : (fromModules A).map (MappingCone.map φ.τ₁ φ.τ₂ φ.comm₁₂.symm) ≫
      (fromModules A).map (MappingCone.toShift T.f) ≫
        (toKShiftIso T.X₁ (1 : ℤ)).hom =
      (fromModules A).map (MappingCone.toShift S.f) ≫
        (toKShiftIso S.X₁ (1 : ℤ)).hom ≫
          (((fromModules A).map φ.τ₁)⟦(1 : ℤ)⟧') := by
    simpa only [toKShiftIso_hom, fromModules_map, Functor.map_comp, Category.assoc] using h.symm
  refine ⟨?_⟩
  apply (cancel_epi (coneIso S hS).hom).1
  calc
    (coneIso S hS).hom ≫ (fromModules A).map φ.τ₃ ≫ δ T hT =
        (fromModules A).map (MappingCone.map φ.τ₁ φ.τ₂ φ.comm₁₂.symm) ≫
          (coneIso T hT).hom ≫ δ T hT := by
      rw [coneIso_hom, coneIso_hom, ← Functor.map_comp_assoc,
        ← Functor.map_comp_assoc, coneProjection_naturality]
    _ = (fromModules A).map (MappingCone.map φ.τ₁ φ.τ₂ φ.comm₁₂.symm) ≫
        (fromModules A).map (MappingCone.toShift T.f) ≫
          (toKShiftIso T.X₁ (1 : ℤ)).hom := by rw [coneIso_hom_δ]
    _ = (fromModules A).map (MappingCone.toShift S.f) ≫
        (toKShiftIso S.X₁ (1 : ℤ)).hom ≫
          (((fromModules A).map φ.τ₁)⟦(1 : ℤ)⟧') := hb
    _ = (coneIso S hS).hom ≫ δ S hS ≫
        (((fromModules A).map φ.τ₁)⟦(1 : ℤ)⟧') := by
      simpa only [Category.assoc] using
        (coneIso_hom_δ_assoc S hS (((fromModules A).map φ.τ₁)⟦(1 : ℤ)⟧')).symm

/-- Lemma 22.23.1 (09L0): the canonical functor from right DG modules to their derived category,
with the connecting morphisms induced by mapping cones. -/
@[stacks 09L0 "delta functor from DG modules to their derived category"]
noncomputable def functor (A : CochainDGAlgebra.{u, v} R) :
    DeltaFunctor (DifferentialGradedModule.{u, v} A) (Category A) where
  toFunctor := fromModules A
  additive := inferInstance
  δ := fun {_} hS ↦ δ _ hS
  map_distinguished := fun {_} hS ↦ triangle_distinguished _ hS
  δ_naturality := fun {_ _} hS hT φ ↦ δ_naturality _ hS hT φ

/-- The underlying functor of the canonical DG-module delta functor is `fromModules A`. -/
theorem functor_toFunctor (A : CochainDGAlgebra.{u, v} R) :
    (functor A).toFunctor = fromModules A := rfl

/-- The boundary map stored by the canonical DG-module delta functor is the mapping-cone
connecting morphism `δ`. -/
theorem functor_δ (A : CochainDGAlgebra.{u, v} R)
    {S : ShortComplex (DifferentialGradedModule.{u, v} A)} (hS : S.ShortExact) :
    (functor A).δ hS = δ S hS := rfl

end DifferentialGradedModule.Derived.Delta
