/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Limits.Shapes.Kernels
public import Mathlib.CategoryTheory.Sites.Abelian
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.LowerShriek.LocallyQuasiFinite.Cech.Separated
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.FiniteSupport.Separated

/-!
# Separated Čech cokernels and lower shriek

The cokernel of the signed separated Čech map is functorial in the sheaf and
compares canonically with the locally quasi-finite lower shriek.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Functor
open CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.Scheme.GeometricPoint
open Opposite
open TopologicalSpace

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Etale

variable {X Y : Scheme.{u}} (f : X ⟶ Y)
variable [LocallyQuasiFinite f] [LocallyOfFiniteType f]
variable [HasSheafify Y.smallEtaleTopology AddCommGrpCat.{u}]
variable [HasCoproducts.{u} (Sheaf Y.smallEtaleTopology AddCommGrpCat.{u})]
variable {ι : Type u} (𝒰 : ι → X.Opens)
variable [∀ i, IsSeparated ((𝒰 i).ι ≫ f)]

/-- Sheafification identifies a separated Čech summand with the corresponding
locally quasi-finite lower-shriek summand. -/
def etaleLowerShriekCechSummandIso
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) (n : ℕ)
    (σ : Fin (n + 1) → ι) :
    etaleLowerShriekCechSummand f 𝒰 F n σ ≅
      lowerShriekCechSummand f 𝒰 F n σ :=
  (asIso
      ((sheafificationAdjunction Y.smallEtaleTopology AddCommGrpCat.{u}).counit.app
        (etaleLowerShriekCechSummand f 𝒰 F n σ))).symm ≪≫
    (presheafToSheaf Y.smallEtaleTopology AddCommGrpCat.{u}).mapIso
      ((lowerShriekPresheafIso
          ((lowerShriekCechIntersection 𝒰 σ).ι ≫ f)).app
        ((etaleRestrictionSheaf (lowerShriekCechIntersection 𝒰 σ).ι
            AddCommGrpCat.{u}).obj F)).symm

/-- The coproduct of the separated-to-canonical summand identifications. -/
def etaleLowerShriekCechTermIso
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) (n : ℕ) :
    etaleLowerShriekCechTerm f 𝒰 F n ≅ lowerShriekCechTerm f 𝒰 F n :=
  Sigma.mapIso (etaleLowerShriekCechSummandIso f 𝒰 F n)

/-- The alternative compact-support direct image, as the cokernel of the
separated Čech penultimate map. -/
def lowerShriekCechCokernel
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) :
    Sheaf Y.smallEtaleTopology AddCommGrpCat.{u} :=
  cokernel (etaleLowerShriekCechPenultimate f 𝒰 F)

/-- The cokernel projection from the degree-zero separated Čech term. -/
abbrev lowerShriekCechCokernel_π
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) :
    etaleLowerShriekCechTerm f 𝒰 F 0 ⟶ lowerShriekCechCokernel f 𝒰 F :=
  cokernel.π (etaleLowerShriekCechPenultimate f 𝒰 F)

/-- The cokernel universal property of the alternative construction. -/
abbrev lowerShriekCechCokernel_desc
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u})
    {G : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u}}
    (k : etaleLowerShriekCechTerm f 𝒰 F 0 ⟶ G)
    (h : etaleLowerShriekCechPenultimate f 𝒰 F ≫ k = 0) :
    lowerShriekCechCokernel f 𝒰 F ⟶ G :=
  cokernel.desc (etaleLowerShriekCechPenultimate f 𝒰 F) k h

/-- The cokernel projection is the canonical map out of the degree-zero term. -/
theorem lowerShriekCechCokernel_π_eq
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) :
    lowerShriekCechCokernel_π f 𝒰 F =
      cokernel.π (etaleLowerShriekCechPenultimate f 𝒰 F) :=
  sorry

/-- A morphism of abelian étale sheaves acts on the alternative cokernel by
`cokernel.map`. -/
def lowerShriekCechCokernelMap
    {F G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}} (φ : F ⟶ G) :
    lowerShriekCechCokernel f 𝒰 F ⟶ lowerShriekCechCokernel f 𝒰 G :=
  cokernel.map (etaleLowerShriekCechPenultimate f 𝒰 F)
    (etaleLowerShriekCechPenultimate f 𝒰 G)
    (etaleLowerShriekCechTermMap f 𝒰 φ 1) (etaleLowerShriekCechTermMap f 𝒰 φ 0)
    (etaleLowerShriekCechPenultimate_naturality f 𝒰 φ)

/-- The map on separated Čech cokernels preserves identity morphisms. -/
theorem lowerShriekCechCokernelMap_id
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) :
    lowerShriekCechCokernelMap f 𝒰 (𝟙 F) = 𝟙 (lowerShriekCechCokernel f 𝒰 F) := sorry

/-- The map on separated Čech cokernels preserves composition. -/
theorem lowerShriekCechCokernelMap_comp
    {F G H : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}} (φ : F ⟶ G) (ψ : G ⟶ H) :
    lowerShriekCechCokernelMap f 𝒰 (φ ≫ ψ) =
      lowerShriekCechCokernelMap f 𝒰 φ ≫ lowerShriekCechCokernelMap f 𝒰 ψ := sorry

/-- The functor sending an abelian étale sheaf to the cokernel of the separated
Čech penultimate map. -/
def lowerShriekCechCokernelFunctor :
    Sheaf X.smallEtaleTopology AddCommGrpCat.{u} ⥤
      Sheaf Y.smallEtaleTopology AddCommGrpCat.{u} where
  obj := lowerShriekCechCokernel f 𝒰
  map := lowerShriekCechCokernelMap f 𝒰
  map_id := lowerShriekCechCokernelMap_id f 𝒰
  map_comp := lowerShriekCechCokernelMap_comp f 𝒰

/-- Evaluating the alternative functor recovers the objectwise cokernel. -/
theorem lowerShriekCechCokernelFunctor_obj
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) :
    (lowerShriekCechCokernelFunctor f 𝒰).obj F =
      lowerShriekCechCokernel f 𝒰 F :=
  sorry

/-- The alternative functor acts on morphisms by `lowerShriekCechCokernelMap`. -/
theorem lowerShriekCechCokernelFunctor_map
    {F G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}} (φ : F ⟶ G) :
    (lowerShriekCechCokernelFunctor f 𝒰).map φ =
      lowerShriekCechCokernelMap f 𝒰 φ :=
  sorry

/-- The transported augmentation annihilates the separated penultimate map. -/
theorem etaleLowerShriekCechPenultimate_comp_augmentation
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) :
    etaleLowerShriekCechPenultimate f 𝒰 F ≫
        (etaleLowerShriekCechTermIso f 𝒰 F 0).hom ≫
          lowerShriekCechAugmentation f 𝒰 F = 0 :=
  sorry

/-- Comparison from the alternative cokernel to the canonical `f_! F`, induced
by the Čech augmentation after identifying the separated and canonical terms. -/
def lowerShriekCechCokernelComparison
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) :
    lowerShriekCechCokernel f 𝒰 F ⟶ (lowerShriek f).obj F :=
  cokernel.desc (etaleLowerShriekCechPenultimate f 𝒰 F)
    ((etaleLowerShriekCechTermIso f 𝒰 F 0).hom ≫
      lowerShriekCechAugmentation f 𝒰 F)
    (etaleLowerShriekCechPenultimate_comp_augmentation f 𝒰 F)

/-- On an open covering, the comparison morphism is an isomorphism. -/
theorem lowerShriekCechCokernelComparison_isIso (h𝒰 : IsOpenCover 𝒰)
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) :
    IsIso (lowerShriekCechCokernelComparison f 𝒰 F) :=
  sorry

/-- For an open cover certified by `Fact`, the augmentation-induced cokernel
comparison is canonically invertible. -/
instance lowerShriekCechCokernelComparison_isIso_of_fact [Fact (IsOpenCover 𝒰)]
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) :
    IsIso (lowerShriekCechCokernelComparison f 𝒰 F) :=
  lowerShriekCechCokernelComparison_isIso f 𝒰 Fact.out F

/-- The augmentation-induced cokernel comparison is natural in the sheaf. -/
theorem lowerShriekCechCokernelComparison_naturality
    {F G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}} (φ : F ⟶ G) :
    lowerShriekCechCokernelMap f 𝒰 φ ≫ lowerShriekCechCokernelComparison f 𝒰 G =
      lowerShriekCechCokernelComparison f 𝒰 F ≫ (lowerShriek f).map φ := sorry

/-- On an open covering, the separated Čech cokernel functor is canonically
isomorphic to `lowerShriek` through its augmentation-induced comparison. -/
def lowerShriekCechCokernelIso (h𝒰 : IsOpenCover 𝒰) :
    lowerShriekCechCokernelFunctor f 𝒰 ≅ lowerShriek f :=
  NatIso.ofComponents
    (fun F ↦ @asIso _ _ _ _ (lowerShriekCechCokernelComparison f 𝒰 F)
      (lowerShriekCechCokernelComparison_isIso f 𝒰 h𝒰 F))
    (fun φ ↦ lowerShriekCechCokernelComparison_naturality f 𝒰 φ)

end AlgebraicGeometry.Scheme.Etale

end
