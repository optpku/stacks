/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.GroupoidsOver.Module.Quasicoherent.Tensor
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.InternalHom
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Tensor.Bilinear

/-!
# Internal Hom of quasi-coherent modules
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Functor
  CategoryTheory.Limits CategoryTheory.MonoidalCategory
  CategoryTheory.MonoidalClosed CategoryTheory.ObjectProperty Opposite
  SheafOfModules SheafOfModules.RingedSite
open scoped SheafOfModules.RingedSite TensorProduct

noncomputable section

universe u v w

namespace AlgebraicGeometry.GroupoidsOver

variable {S : Scheme.{u}}

namespace QCoh

/-- The internal Hom of two commutative associated modules, computed in the
universe-lifted module category as `InternalHom.obj`. -/
def associatedInternalHomLift {X : GroupoidsOver S} {τ : StandardTopology}
    (F G : commAssociatedModules X τ) : commAssociatedModulesLift X τ :=
  SheafOfModules.RingedSite.InternalHom.obj.{u + 1, u, u + 1}
    (commAssociatedStructureSheafLift X τ)
    ((commAssociatedModulesLiftFunctor X τ).obj F)
    ((commAssociatedModulesLiftFunctor X τ).obj G)

/-- `associatedInternalHomLift` is the canonical lifted internal Hom. -/
theorem associatedInternalHomLift_eq {X : GroupoidsOver S}
    {τ : StandardTopology} (F G : commAssociatedModules X τ) :
    associatedInternalHomLift F G =
      SheafOfModules.RingedSite.InternalHom.obj.{u + 1, u, u + 1}
        (commAssociatedStructureSheafLift X τ)
        ((commAssociatedModulesLiftFunctor X τ).obj F)
        ((commAssociatedModulesLiftFunctor X τ).obj G) :=
  rfl

/-- `associatedInternalHomLift` agrees with `(ihom _).obj _` on the lifted
commutative associated module category. -/
theorem associatedInternalHomLift_ihom {X : GroupoidsOver S}
    {τ : StandardTopology} (F G : commAssociatedModules X τ) :
    associatedInternalHomLift F G =
      (ihom ((commAssociatedModulesLiftFunctor X τ).obj F)).obj
        ((commAssociatedModulesLiftFunctor X τ).obj G) :=
  rfl

/-- Pointwise tensor of universe lifts as a bilinear map into the lift of the
module-category tensor. -/
noncomputable def moduleTensorLiftBilinear {X : GroupoidsOver S}
    {τ : StandardTopology} (M N : commAssociatedModules X τ) :
    SectionBilinearMap.{u + 1, u} (commAssociatedStructureSheafLift X τ)
      ((commAssociatedModulesLiftFunctor X τ).obj M)
      ((commAssociatedModulesLiftFunctor X τ).obj N)
      ((commAssociatedModulesLiftFunctor X τ).obj
        (moduleTensorAssociated M N)) where
  app U :=
    LinearMap.mk₂ ((commAssociatedStructureSheafLift X τ).obj.obj U)
      (fun x y ↦
        ULift.up
          (((associatedModuleTensorIso M N).hom.val.app U).hom
            ((moduleSheafificationUnitToVal.{u + 1, u, u, u}
                (commAssociatedStructureSheaf X τ)
                (PresheafOfModules.Monoidal.tensorObj M.val N.val)).app U
              (x.down ⊗ₜ y.down))))
      sorry sorry sorry sorry
  naturality := sorry

/-- Canonical comparison from the tensor product of universe lifts to the universe
lift of the module-category tensor. -/
noncomputable def moduleTensorLiftComparison {X : GroupoidsOver S}
    {τ : StandardTopology} (M N : commAssociatedModules X τ) :
    moduleTensorAssociatedLift
      ((commAssociatedModulesLiftFunctor X τ).obj M)
      ((commAssociatedModulesLiftFunctor X τ).obj N) ⟶
    (commAssociatedModulesLiftFunctor X τ).obj (moduleTensorAssociated M N) :=
  SectionBilinearMap.hom.{u + 1, u} (moduleTensorLiftBilinear M N)

/-- `moduleTensorLiftComparison` is the bilinear pairing of universe lifts of
pure tensors. -/
theorem moduleTensorLiftComparison_eq {X : GroupoidsOver S}
    {τ : StandardTopology} (M N : commAssociatedModules X τ) :
    moduleTensorLiftComparison M N =
      SectionBilinearMap.hom.{u + 1, u} (moduleTensorLiftBilinear M N) :=
  sorry

/-- Target (and, via currying, source) functoriality of the lifted internal Hom. -/
def associatedInternalHomLiftCongr {X : GroupoidsOver S} {τ : StandardTopology}
    {F₁ F₂ G₁ G₂ : commAssociatedModules X τ} (f : F₂ ⟶ F₁) (g : G₁ ⟶ G₂) :
    associatedInternalHomLift F₁ G₁ ⟶ associatedInternalHomLift F₂ G₂ :=
  let O := commAssociatedStructureSheafLift X τ
  let L := commAssociatedModulesLiftFunctor X τ
  (SheafOfModules.RingedSite.InternalHom.homEquiv O (L.obj F₂)
        (associatedInternalHomLift F₁ G₁) (L.obj G₂))
    (tensorHom (L.map f) (𝟙 (associatedInternalHomLift F₁ G₁)) ≫
      (SheafOfModules.RingedSite.InternalHom.homEquiv O (L.obj F₁)
            (associatedInternalHomLift F₁ G₁) (L.obj G₁)).symm
        (𝟙 (associatedInternalHomLift F₁ G₁)) ≫
      L.map g)

/-- `associatedInternalHomLiftCongr` is the currying of `tensorHom` against
evaluation, followed by the lifted target map. -/
theorem associatedInternalHomLiftCongr_eq {X : GroupoidsOver S}
    {τ : StandardTopology} {F₁ F₂ G₁ G₂ : commAssociatedModules X τ}
    (f : F₂ ⟶ F₁) (g : G₁ ⟶ G₂) :
    associatedInternalHomLiftCongr f g =
      (SheafOfModules.RingedSite.InternalHom.homEquiv
          (commAssociatedStructureSheafLift X τ)
          ((commAssociatedModulesLiftFunctor X τ).obj F₂)
          (associatedInternalHomLift F₁ G₁)
          ((commAssociatedModulesLiftFunctor X τ).obj G₂))
        (tensorHom ((commAssociatedModulesLiftFunctor X τ).map f)
            (𝟙 (associatedInternalHomLift F₁ G₁)) ≫
          (SheafOfModules.RingedSite.InternalHom.homEquiv
                (commAssociatedStructureSheafLift X τ)
                ((commAssociatedModulesLiftFunctor X τ).obj F₁)
                (associatedInternalHomLift F₁ G₁)
                ((commAssociatedModulesLiftFunctor X τ).obj G₁)).symm
            (𝟙 (associatedInternalHomLift F₁ G₁)) ≫
          (commAssociatedModulesLiftFunctor X τ).map g) :=
  sorry

/-- The comparison determined by an evaluation `F ⊗ H ⟶ G`: transport to `τ`,
lift universes, and curry into the actual sheaf of local morphisms. -/
def internalHomComparison {X : GroupoidsOver S} (τ : StandardTopology)
    (F G H : QCoh X) (ev : quasicoherentTensor F H ⟶ G) :
    (commAssociatedModulesLiftFunctor X τ).obj
      ((toCommAssociatedModules X τ).obj H) ⟶
    associatedInternalHomLift
      ((toCommAssociatedModules X τ).obj F)
      ((toCommAssociatedModules X τ).obj G) :=
  SheafOfModules.RingedSite.InternalHom.homEquiv.{u + 1, u}
      (commAssociatedStructureSheafLift X τ)
      ((commAssociatedModulesLiftFunctor X τ).obj
        ((toCommAssociatedModules X τ).obj F))
      ((commAssociatedModulesLiftFunctor X τ).obj
        ((toCommAssociatedModules X τ).obj H))
      ((commAssociatedModulesLiftFunctor X τ).obj
        ((toCommAssociatedModules X τ).obj G))
    (moduleTensorLiftComparison
        ((toCommAssociatedModules X τ).obj F)
        ((toCommAssociatedModules X τ).obj H) ≫
      (commAssociatedModulesLiftFunctor X τ).map
        (tensorComparison τ F H ≫ (toCommAssociatedModules X τ).map ev))

/-- `internalHomComparison` is the currying of the lifted tensor comparison
followed by evaluation. -/
theorem internalHomComparison_eq {X : GroupoidsOver S} (τ : StandardTopology)
    (F G H : QCoh X) (ev : quasicoherentTensor F H ⟶ G) :
    internalHomComparison τ F G H ev =
      SheafOfModules.RingedSite.InternalHom.homEquiv.{u + 1, u}
          (commAssociatedStructureSheafLift X τ)
          ((commAssociatedModulesLiftFunctor X τ).obj
            ((toCommAssociatedModules X τ).obj F))
          ((commAssociatedModulesLiftFunctor X τ).obj
            ((toCommAssociatedModules X τ).obj H))
          ((commAssociatedModulesLiftFunctor X τ).obj
            ((toCommAssociatedModules X τ).obj G))
        (moduleTensorLiftComparison
            ((toCommAssociatedModules X τ).obj F)
            ((toCommAssociatedModules X τ).obj H) ≫
          (commAssociatedModulesLiftFunctor X τ).map
            (tensorComparison τ F H ≫ (toCommAssociatedModules X τ).map ev)) :=
  rfl

/-- There is one quasi-coherent module with an evaluation
whose canonical comparison with the actual internal Hom is invertible in the
Zariski, étale and fppf module categories. The same object and evaluation are
used for all three topologies. -/
theorem internalHom {X : GroupoidsOver S} (F G : QCoh X)
    [SheafOfModules.IsFiniteLocallyFree F.obj] :
    ∃ (H : QCoh X) (ev : quasicoherentTensor F H ⟶ G),
      ∀ τ ∈ [StandardTopology.zariski, .etale, .fppf],
        IsIso (internalHomComparison τ F G H ev) :=
  sorry

end QCoh

end AlgebraicGeometry.GroupoidsOver
