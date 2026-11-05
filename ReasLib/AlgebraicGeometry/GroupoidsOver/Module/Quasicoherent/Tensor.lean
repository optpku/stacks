/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.GroupoidsOver.Module.CommFppf
public import ReasLib.Algebra.Category.ModuleCat.Presheaf.Tensor.Restriction

/-!
# Tensor products of quasi-coherent modules
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

/-- The common quasi-coherent tensor product, computed as the module-category
tensor on the commutative fppf presentation and transported back to `QCoh`. -/
def quasicoherentTensor {X : GroupoidsOver S} (F G : QCoh X) : QCoh X where
  obj :=
    (fromCommFppfModules X).obj
      (moduleTensorAssociated
        ((toCommFppfModules X).obj F.obj)
        ((toCommFppfModules X).obj G.obj))
  property := sorry

/-- The underlying fppf module of `quasicoherentTensor` is the transport of the
commutative fppf module tensor. -/
theorem quasicoherentTensor_obj {X : GroupoidsOver S} (F G : QCoh X) :
    (quasicoherentTensor F G).obj =
      (fromCommAssociatedModules X).obj
        (moduleTensorAssociated
          ((toCommAssociatedModules X .fppf).obj F)
          ((toCommAssociatedModules X .fppf).obj G)) :=
  rfl

/-- The common tensor has the same underlying module in the direct fppf
coefficient presentation; the two coefficient transports agree definitionally. -/
theorem quasicoherentTensor_obj_commFppf {X : GroupoidsOver S} (F G : QCoh X) :
    (quasicoherentTensor F G).obj =
      (fromCommFppfModules X).obj
        (moduleTensorAssociated
          ((toCommFppfModules X).obj F.obj)
          ((toCommFppfModules X).obj G.obj)) := rfl

/-- Identity-on-Γ tensor comparison on restricted commutative fppf presentations,
built from restriction-of-scalars tensor comparison and the sheafification unit
of the module monoidal structure, transported along
`associatedModuleTensorIso`. -/
def tensorComparison_restrict {X : GroupoidsOver S} (τ : StandardTopology)
    (F G : QCoh X) :
    moduleTensorAssociated
        ((restrictCommAssociatedModules X τ .fppf rfl).obj
          ((toCommAssociatedModules X StandardTopology.fppf).obj F))
        ((restrictCommAssociatedModules X τ .fppf rfl).obj
          ((toCommAssociatedModules X StandardTopology.fppf).obj G)) ⟶
      (restrictCommAssociatedModules X τ .fppf rfl).obj
        (moduleTensorAssociated
          ((toCommAssociatedModules X StandardTopology.fppf).obj F)
          ((toCommAssociatedModules X StandardTopology.fppf).obj G)) :=
  (associatedModuleTensorIso
      ((restrictCommAssociatedModules X τ .fppf rfl).obj
        ((toCommAssociatedModules X StandardTopology.fppf).obj F))
      ((restrictCommAssociatedModules X τ .fppf rfl).obj
        ((toCommAssociatedModules X StandardTopology.fppf).obj G))).inv ≫
    associatedMapToRestriction rfl
      (PresheafOfModules.Restriction.tensorComparison
        (commAssociatedCoefficient X τ StandardTopology.fppf)
        ((toCommAssociatedModules X StandardTopology.fppf).obj F).val
        ((toCommAssociatedModules X StandardTopology.fppf).obj G).val) ≫
    (restrictCommAssociatedModules X τ .fppf rfl).map
      (associatedModuleTensorIso
        ((toCommAssociatedModules X StandardTopology.fppf).obj F)
        ((toCommAssociatedModules X StandardTopology.fppf).obj G)).hom

/-- Canonical comparison in `commAssociatedModules X τ` from the tensor product
computed on the associated `τ`-site to the identity-on-Γ transport of the
common fppf tensor. -/
def tensorComparison {X : GroupoidsOver S} (τ : StandardTopology)
    (F G : QCoh X) :
    moduleTensorAssociated ((toCommAssociatedModules X τ).obj F)
      ((toCommAssociatedModules X τ).obj G) ⟶
      (toCommAssociatedModules X τ).obj (quasicoherentTensor F G) :=
  SheafOfModules.RingedSite.moduleTensorMap.{u + 1, u, u}
      (toCommAssociatedModules_restrictIso τ F).hom
      (toCommAssociatedModules_restrictIso τ G).hom ≫
    tensorComparison_restrict τ F G ≫
    (restrictCommAssociatedModules X τ .fppf rfl).map
      (toFromCommAssociatedModulesIso
        (moduleTensorAssociated
          ((toCommAssociatedModules X StandardTopology.fppf).obj F)
          ((toCommAssociatedModules X StandardTopology.fppf).obj G))).inv ≫
    (toCommAssociatedModules_restrictIso τ (quasicoherentTensor F G)).inv

/-- Tensor products computed in the associated Zariski module category agree
with the common quasi-coherent value. -/
instance tensorComparison_isIso_zariski {X : GroupoidsOver S} (F G : QCoh X) :
    IsIso (tensorComparison .zariski F G) :=
  sorry

/-- Tensor products computed in the associated étale module category agree with
the common quasi-coherent value. -/
instance tensorComparison_isIso_etale {X : GroupoidsOver S} (F G : QCoh X) :
    IsIso (tensorComparison .etale F G) :=
  sorry

/-- Tensor products computed in `Mod(𝒪_X)` agree with the common quasi-coherent
value. -/
instance tensorComparison_isIso_fppf {X : GroupoidsOver S} (F G : QCoh X) :
    IsIso (tensorComparison .fppf F G) :=
  sorry

end QCoh

end AlgebraicGeometry.GroupoidsOver
