/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Differentials.Presheaf
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
public import ReasLib.Algebra.Category.ModuleCat.Presheaf.PrincipalParts
public import ReasLib.Algebra.Module.PrincipalParts.RingHom.FirstOrder

/-!
# The first principal-parts sequence for module presheaves

This file constructs the first principal-parts sequence for a morphism of commutative-ring
presheaves.  It is independent of a Grothendieck topology: the sheaf-level sequence is obtained
by applying module sheafification to this owner.
-/

@[expose] public section

open CategoryTheory
open PresheafOfModules.DifferentialsConstruction

noncomputable section

universe u v

namespace PresheafOfModules.PrincipalParts.FirstOrder

variable {C : Type u} [Category.{v} C]
variable {O₁ O₂ : Cᵒᵖ ⥤ CommRingCat.{max u v}}

/-- The cotangent tensor presheaf `Ω[O₂/O₁] ⊗[O₂] F`. -/
noncomputable abbrev cotangent (phi : O₁ ⟶ O₂)
    (F : PresheafOfModules (ringPresheaf O₂)) :
    PresheafOfModules (ringPresheaf O₂) :=
  PresheafOfModules.Monoidal.tensorObj (relativeDifferentials' phi) F

/-- The component of the canonical cotangent arrow into first principal parts. -/
noncomputable def cotangentToApp (phi : O₁ ⟶ O₂)
    (F : PresheafOfModules (ringPresheaf O₂)) (X : Cᵒᵖ) :
    (cotangent phi F).obj X ⟶ (PrincipalParts.presheaf phi F 1).obj X :=
  _root_.PrincipalParts.RingHom.FirstOrder.cotangentTo (phi.app X).hom (F.obj X)

private theorem cotangentToApp_d_tmul (phi : O₁ ⟶ O₂)
    (F : PresheafOfModules (ringPresheaf O₂)) (X : Cᵒᵖ) (s : O₂.obj X) (m : F.obj X) :
    (cotangentToApp phi F X).hom
        (CommRingCat.KaehlerDifferential.d s ⊗ₜ[O₂.obj X] m) =
      PrincipalParts.universalClass phi F 1 X (s • m) -
        s • PrincipalParts.universalClass phi F 1 X m := by
  letI : Algebra (O₁.obj X) (O₂.obj X) :=
    _root_.PrincipalParts.RingHom.algebra (phi.app X).hom
  letI : Module (O₁.obj X) (F.obj X) :=
    _root_.PrincipalParts.RingHom.sourceModule (phi.app X).hom (F.obj X)
  letI : IsScalarTower (O₁.obj X) (O₂.obj X) (F.obj X) :=
    IsScalarTower.of_compHom _ _ _
  exact _root_.PrincipalParts.FirstOrder.cotangentTo_D_tmul s m

set_option backward.isDefEq.respectTransparency false in
private theorem cotangent_app_hom_ext (phi : O₁ ⟶ O₂)
    (F : PresheafOfModules (ringPresheaf O₂)) (X : Cᵒᵖ)
    {N : ModuleCat (O₂.obj X)} {a b : (cotangent phi F).obj X ⟶ N}
    (h : ∀ (s : O₂.obj X) (m : F.obj X),
      a.hom (CommRingCat.KaehlerDifferential.d s ⊗ₜ[O₂.obj X] m) =
        b.hom (CommRingCat.KaehlerDifferential.d s ⊗ₜ[O₂.obj X] m)) : a = b := by
  letI : Algebra (O₁.obj X) (O₂.obj X) :=
    _root_.PrincipalParts.RingHom.algebra (phi.app X).hom
  apply ModuleCat.hom_ext
  apply TensorProduct.ext
  apply LinearMap.ext_on_range
    (_root_.KaehlerDifferential.span_range_derivation (R := O₁.obj X) (S := O₂.obj X))
  intro s
  exact LinearMap.ext (h s)

set_option backward.isDefEq.respectTransparency false in
/-- The cotangent components commute with restriction maps. -/
theorem cotangentToApp_naturality (phi : O₁ ⟶ O₂)
    (F : PresheafOfModules (ringPresheaf O₂)) {X Y : Cᵒᵖ} (f : X ⟶ Y) :
    (cotangent phi F).map f ≫
        (ModuleCat.restrictScalars (((ringPresheaf O₂).map f).hom)).map
          (cotangentToApp phi F Y) =
      cotangentToApp phi F X ≫ (PrincipalParts.presheaf phi F 1).map f := by
  apply cotangent_app_hom_ext phi F X
  intro s m
  change (cotangentToApp phi F Y).hom
      (((cotangent phi F).map f).hom
        (CommRingCat.KaehlerDifferential.d s ⊗ₜ[O₂.obj X] m)) =
    ((PrincipalParts.presheaf phi F 1).map f).hom
      ((cotangentToApp phi F X).hom
        (CommRingCat.KaehlerDifferential.d s ⊗ₜ[O₂.obj X] m))
  have ht : ((cotangent phi F).map f).hom
      (CommRingCat.KaehlerDifferential.d s ⊗ₜ[O₂.obj X] m) =
      CommRingCat.KaehlerDifferential.d (O₂.map f s) ⊗ₜ[O₂.obj Y] (F.map f).hom m := by
    have h := PresheafOfModules.Monoidal.tensorObj_map_tmul
      (M₁ := relativeDifferentials' phi) (M₂ := F) f
      (CommRingCat.KaehlerDifferential.d s) m
    change ((cotangent phi F).map f).hom
        (CommRingCat.KaehlerDifferential.d s ⊗ₜ[O₂.obj X] m) =
      ((relativeDifferentials' phi).map f).hom (CommRingCat.KaehlerDifferential.d s)
        ⊗ₜ[O₂.obj Y] (F.map f).hom m at h
    exact h.trans (congrArg
      (fun η : (relativeDifferentials' phi).obj Y ↦ η ⊗ₜ[O₂.obj Y] (F.map f).hom m)
      (relativeDifferentials'_map_d phi f s))
  rw [ht, cotangentToApp_d_tmul, cotangentToApp_d_tmul, map_sub]
  rw [(PrincipalParts.presheaf phi F 1).map_smul]
  change PrincipalParts.universalClass phi F 1 Y ((O₂.map f).hom s • (F.map f).hom m) -
      (O₂.map f).hom s • PrincipalParts.universalClass phi F 1 Y ((F.map f).hom m) =
    (PrincipalParts.restrictionMap phi F 1 f).hom
        (PrincipalParts.universalClass phi F 1 X (s • m)) -
      (O₂.map f).hom s • (PrincipalParts.restrictionMap phi F 1 f).hom
        (PrincipalParts.universalClass phi F 1 X m)
  rw [PrincipalParts.restrictionMap_universalClass phi F 1 f (s • m),
    PrincipalParts.restrictionMap_universalClass phi F 1 f m]
  exact congrArg
    (fun n ↦ PrincipalParts.universalClass phi F 1 Y n -
      (O₂.map f).hom s • PrincipalParts.universalClass phi F 1 Y ((F.map f).hom m))
    (F.map_smul f s m).symm

/-- The canonical cotangent arrow into the first principal-parts presheaf. -/
noncomputable def cotangentTo (phi : O₁ ⟶ O₂)
    (F : PresheafOfModules (ringPresheaf O₂)) :
    cotangent phi F ⟶ PrincipalParts.presheaf phi F 1 where
  app X := cotangentToApp phi F X
  naturality := cotangentToApp_naturality phi F

/-- The component of the canonical first-principal-parts projection. -/
noncomputable def projectionApp (phi : O₁ ⟶ O₂)
    (F : PresheafOfModules (ringPresheaf O₂)) (X : Cᵒᵖ) :
    (PrincipalParts.presheaf phi F 1).obj X ⟶ F.obj X :=
  _root_.PrincipalParts.RingHom.FirstOrder.projection (phi.app X).hom (F.obj X)

private theorem projectionApp_universalClass (phi : O₁ ⟶ O₂)
    (F : PresheafOfModules (ringPresheaf O₂)) (X : Cᵒᵖ) (m : F.obj X) :
    (projectionApp phi F X).hom (PrincipalParts.universalClass phi F 1 X m) = m := by
  letI : Algebra (O₁.obj X) (O₂.obj X) :=
    _root_.PrincipalParts.RingHom.algebra (phi.app X).hom
  letI : Module (O₁.obj X) (F.obj X) :=
    _root_.PrincipalParts.RingHom.sourceModule (phi.app X).hom (F.obj X)
  letI : IsScalarTower (O₁.obj X) (O₂.obj X) (F.obj X) :=
    IsScalarTower.of_compHom _ _ _
  exact _root_.PrincipalParts.FirstOrder.projection_apply_universalClass m

set_option backward.isDefEq.respectTransparency false in
private theorem principalParts_app_hom_ext (phi : O₁ ⟶ O₂)
    (F : PresheafOfModules (ringPresheaf O₂)) (k : ℕ) (X : Cᵒᵖ)
    {N : ModuleCat (O₂.obj X)} {a b : (PrincipalParts.presheaf phi F k).obj X ⟶ N}
    (h : ∀ m : F.obj X,
      a.hom (PrincipalParts.universalClass phi F k X m) =
        b.hom (PrincipalParts.universalClass phi F k X m)) : a = b := by
  letI : Algebra (O₁.obj X) (O₂.obj X) :=
    _root_.PrincipalParts.RingHom.algebra (phi.app X).hom
  letI : Module (O₁.obj X) (F.obj X) :=
    _root_.PrincipalParts.RingHom.sourceModule (phi.app X).hom (F.obj X)
  letI : IsScalarTower (O₁.obj X) (O₂.obj X) (F.obj X) :=
    IsScalarTower.of_compHom _ _ _
  letI : Module (O₁.obj X) N :=
    _root_.PrincipalParts.RingHom.sourceModule (phi.app X).hom N
  letI : IsScalarTower (O₁.obj X) (O₂.obj X) N := IsScalarTower.of_compHom _ _ _
  apply ModuleCat.hom_ext
  exact _root_.PrincipalParts.linearMap_ext
    (R := O₁.obj X) (S := O₂.obj X) (M := F.obj X) k h

/-- The projection components commute with restriction maps. -/
theorem projectionApp_naturality (phi : O₁ ⟶ O₂)
    (F : PresheafOfModules (ringPresheaf O₂)) {X Y : Cᵒᵖ} (f : X ⟶ Y) :
    (PrincipalParts.presheaf phi F 1).map f ≫
        (ModuleCat.restrictScalars (((ringPresheaf O₂).map f).hom)).map
          (projectionApp phi F Y) =
      projectionApp phi F X ≫ F.map f := by
  apply principalParts_app_hom_ext phi F 1 X
  intro m
  change (projectionApp phi F Y).hom
      ((PrincipalParts.restrictionMap phi F 1 f).hom
        (PrincipalParts.universalClass phi F 1 X m)) =
    (F.map f).hom
      ((projectionApp phi F X).hom (PrincipalParts.universalClass phi F 1 X m))
  rw [PrincipalParts.restrictionMap_universalClass,
    projectionApp_universalClass, projectionApp_universalClass]

/-- The canonical projection from first principal parts to the original module presheaf. -/
noncomputable def projection (phi : O₁ ⟶ O₂)
    (F : PresheafOfModules (ringPresheaf O₂)) :
    PrincipalParts.presheaf phi F 1 ⟶ F where
  app X := projectionApp phi F X
  naturality := projectionApp_naturality phi F

/-- The cotangent arrow followed by the first-principal-parts projection is zero. -/
theorem zero (phi : O₁ ⟶ O₂)
    (F : PresheafOfModules (ringPresheaf O₂)) :
    cotangentTo phi F ≫ projection phi F = 0 := by
  apply PresheafOfModules.hom_ext
  intro X
  apply cotangent_app_hom_ext phi F X
  intro s m
  change (projectionApp phi F X).hom
      ((cotangentToApp phi F X).hom
        (CommRingCat.KaehlerDifferential.d s ⊗ₜ[O₂.obj X] m)) = 0
  rw [cotangentToApp_d_tmul, map_sub, map_smul,
    projectionApp_universalClass, projectionApp_universalClass, sub_self]

/-- The first principal-parts short complex of a module presheaf. -/
@[stacks 09CN "presheaf first principal-parts sequence"]
noncomputable def sequence (phi : O₁ ⟶ O₂)
    (F : PresheafOfModules (ringPresheaf O₂)) :
    ShortComplex (PresheafOfModules (ringPresheaf O₂)) :=
  ShortComplex.mk (cotangentTo phi F) (projection phi F) (zero phi F)

section Functoriality

variable {F G H : PresheafOfModules (ringPresheaf O₂)}

/-- The morphism on cotangent tensor presheaves induced by a module-presheaf morphism. -/
noncomputable abbrev cotangentMap (phi : O₁ ⟶ O₂) (alpha : F ⟶ G) :
    cotangent phi F ⟶ cotangent phi G :=
  PresheafOfModules.Monoidal.tensorHom (𝟙 (relativeDifferentials' phi)) alpha

/-- Cotangent tensor functoriality preserves identity morphisms. -/
@[simp]
theorem cotangentMap_id (phi : O₁ ⟶ O₂) :
    cotangentMap phi (𝟙 F) = 𝟙 (cotangent phi F) := by
  exact MonoidalCategory.id_tensorHom_id (relativeDifferentials' phi) F

/-- Cotangent tensor functoriality preserves composition. -/
@[simp]
theorem cotangentMap_comp (phi : O₁ ⟶ O₂) (alpha : F ⟶ G) (beta : G ⟶ H) :
    cotangentMap phi (alpha ≫ beta) =
      cotangentMap phi alpha ≫ cotangentMap phi beta := by
  exact (MonoidalCategory.tensorHom_comp_tensorHom (𝟙 _) alpha (𝟙 _) beta).symm

/-- Tensoring with the relative-differentials presheaf defines an endofunctor on module
presheaves. -/
noncomputable def cotangentFunctor (phi : O₁ ⟶ O₂) :
    PresheafOfModules (ringPresheaf O₂) ⥤ PresheafOfModules (ringPresheaf O₂) where
  obj F := cotangent phi F
  map alpha := cotangentMap phi alpha
  map_id _ := cotangentMap_id phi
  map_comp alpha beta := cotangentMap_comp phi alpha beta

/-- Naturality of the cotangent arrow in the module-presheaf argument. -/
theorem cotangentTo_naturality (phi : O₁ ⟶ O₂) (alpha : F ⟶ G) :
    cotangentMap phi alpha ≫ cotangentTo phi G =
      cotangentTo phi F ≫ PrincipalParts.map phi F 1 alpha := by
  apply PresheafOfModules.hom_ext
  intro X
  exact _root_.PrincipalParts.RingHom.FirstOrder.cotangentTo_naturality
    (phi.app X).hom (alpha.app X)

/-- Naturality of the first-principal-parts projection in the module-presheaf argument. -/
theorem projection_naturality (phi : O₁ ⟶ O₂) (alpha : F ⟶ G) :
    PrincipalParts.map phi F 1 alpha ≫ projection phi G =
      projection phi F ≫ alpha := by
  apply PresheafOfModules.hom_ext
  intro X
  exact _root_.PrincipalParts.RingHom.FirstOrder.projection_naturality
    (phi.app X).hom (alpha.app X)

/-- The cotangent arrows form a natural transformation into first principal parts. -/
noncomputable def cotangentToNatTrans (phi : O₁ ⟶ O₂) :
    cotangentFunctor phi ⟶ PrincipalParts.functor phi 1 where
  app F := cotangentTo phi F
  naturality _ _ alpha := cotangentTo_naturality phi alpha

/-- The first-principal-parts projections form a natural transformation to the identity
functor. -/
noncomputable def projectionNatTrans (phi : O₁ ⟶ O₂) :
    PrincipalParts.functor phi 1 ⟶ 𝟭 (PresheafOfModules (ringPresheaf O₂)) where
  app F := projection phi F
  naturality _ _ alpha := projection_naturality phi alpha

/-- The morphism of first-principal-parts short complexes induced by a module-presheaf
morphism. -/
noncomputable def sequenceMap (phi : O₁ ⟶ O₂) (alpha : F ⟶ G) :
    sequence phi F ⟶ sequence phi G :=
  ShortComplex.Hom.mk (cotangentMap phi alpha) (PrincipalParts.map phi F 1 alpha) alpha
    (cotangentTo_naturality phi alpha) (projection_naturality phi alpha)

/-- The first-principal-parts sequence map preserves identity morphisms. -/
@[simp]
theorem sequenceMap_id (phi : O₁ ⟶ O₂) :
    sequenceMap phi (𝟙 F) = 𝟙 (sequence phi F) := by
  apply ShortComplex.hom_ext
  · change cotangentMap phi (𝟙 F) = 𝟙 (cotangent phi F)
    exact cotangentMap_id phi
  · change PrincipalParts.map phi F 1 (𝟙 F) = 𝟙 (PrincipalParts.presheaf phi F 1)
    exact PrincipalParts.map_id phi F 1
  · rfl

/-- The first-principal-parts sequence map preserves composition. -/
@[simp]
theorem sequenceMap_comp (phi : O₁ ⟶ O₂) (alpha : F ⟶ G) (beta : G ⟶ H) :
    sequenceMap phi (alpha ≫ beta) = sequenceMap phi alpha ≫ sequenceMap phi beta := by
  apply ShortComplex.hom_ext
  · change cotangentMap phi (alpha ≫ beta) = cotangentMap phi alpha ≫ cotangentMap phi beta
    exact cotangentMap_comp phi alpha beta
  · change PrincipalParts.map phi F 1 (alpha ≫ beta) =
      PrincipalParts.map phi F 1 alpha ≫ PrincipalParts.map phi G 1 beta
    exact PrincipalParts.map_comp phi F 1 alpha beta
  · rfl

/-- The first-principal-parts short complex is functorial in the module presheaf. -/
noncomputable def sequenceFunctor (phi : O₁ ⟶ O₂) :
    PresheafOfModules (ringPresheaf O₂) ⥤
      ShortComplex (PresheafOfModules (ringPresheaf O₂)) where
  obj F := sequence phi F
  map alpha := sequenceMap phi alpha
  map_id _ := sequenceMap_id phi
  map_comp alpha beta := sequenceMap_comp phi alpha beta

end Functoriality

/-- The first principal-parts sequence of module presheaves is short exact. -/
@[stacks 09CN "presheaf first-order short exactness"]
theorem shortExact (phi : O₁ ⟶ O₂)
    (F : PresheafOfModules (ringPresheaf O₂)) :
    (sequence phi F).ShortExact := by
  have hX (X : Cᵒᵖ) :
      ((sequence phi F).map (PresheafOfModules.evaluation (ringPresheaf O₂) X)).ShortExact :=
    _root_.PrincipalParts.RingHom.FirstOrder.shortExact (phi.app X).hom (F.obj X)
  refine { exact := ?_, mono_f := ?_, epi_g := ?_ }
  · apply ShortComplex.exact_of_f_is_kernel
    apply PresheafOfModules.evaluationJointlyReflectsLimits
    intro X
    exact (Limits.isLimitMapConeForkEquiv'
      (PresheafOfModules.evaluation (ringPresheaf O₂) X) (sequence phi F).zero).symm
        (hX X).fIsKernel
  · exact PresheafOfModules.mono_of_injective (fun {X} ↦ (hX X).moduleCat_injective_f)
  · exact PresheafOfModules.epi_of_surjective (fun {X} ↦ (hX X).moduleCat_surjective_g)

end PresheafOfModules.PrincipalParts.FirstOrder
