/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.GroupoidsOver.Module.CommFppf
public import ReasLib.AlgebraicGeometry.AlgebraicStack.Basic
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.InternalHom
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Tensor.Bilinear

/-! # Tensor and internal Hom in the direct fppf coefficient presentation -/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Functor Opposite
  AlgebraicGeometry.GroupoidsOver CategoryTheory.MonoidalCategory
  SheafOfModules SheafOfModules.RingedSite
open scoped SheafOfModules.RingedSite TensorProduct

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidsOver.QCoh.Fppf

variable {S : Scheme.{u}} {X : GroupoidsOver S}

/-- Tensor product of two quasi-coherent modules, computed in the commutative
fppf presentation of `Mod(𝒪_𝒳)`. -/
abbrev moduleTensor [AlgebraicStack X] (F G : QCoh X) : commAssociatedModules X .fppf :=
  moduleTensorAssociated
    ((toCommFppfModules X).obj F.obj) ((toCommFppfModules X).obj G.obj)

/-- `moduleTensor` is the ringed-site tensor product of the transported modules. -/
theorem moduleTensor_eq [AlgebraicStack X] (F G : QCoh X) :
    moduleTensor F G =
      moduleTensorAssociated
        ((toCommFppfModules X).obj F.obj) ((toCommFppfModules X).obj G.obj) :=
  rfl

/-- Inverse coefficient transport of the ambient tensor of quasi-coherent
 modules is quasi-coherent. -/
theorem tensor_isQuasicoherent [AlgebraicStack X] (F G : QCoh X) :
    quasiCoherentModuleProperty X
      ((fromCommFppfModules X).obj (moduleTensor F G)) := sorry

/-- The tensor product of two quasi-coherent `𝒪_𝒳`-modules, computed in
`Mod(𝒪_𝒳)`, as an object of `QCoh(𝒪_𝒳)`. The underlying fppf module is the
transport of the commutative module tensor. -/
def tensor [AlgebraicStack X] (F G : QCoh X) : QCoh X where
  obj := (fromCommFppfModules X).obj (moduleTensor F G)
  property := tensor_isQuasicoherent F G

/-- The underlying fppf module of `tensor` is the transport of the commutative
fppf module tensor. -/
theorem tensor_obj [AlgebraicStack X] (F G : QCoh X) :
    (tensor F G).obj = (fromCommFppfModules X).obj (moduleTensor F G) :=
  rfl

/-- Canonical comparison in the commutative fppf presentation from the module
tensor to the identity-on-Γ transport of `tensor F G`. -/
def tensorComparison [AlgebraicStack X] (F G : QCoh X) :
    moduleTensor F G ⟶ (toCommFppfModules X).obj (tensor F G).obj :=
  (toFromCommFppfModulesIso (moduleTensor F G)).inv

/-- `tensorComparison` is the inverse of `toFromCommFppfModulesIso`. -/
theorem tensorComparison_eq [AlgebraicStack X] (F G : QCoh X) :
    tensorComparison F G = (toFromCommFppfModulesIso (moduleTensor F G)).inv :=
  rfl

/-- Tensor products computed in `Mod(𝒪_𝒳)` agree with the quasi-coherent tensor. -/
instance tensorComparison_isIso [AlgebraicStack X] (F G : QCoh X) :
    IsIso (tensorComparison F G) :=
  (toFromCommFppfModulesIso (moduleTensor F G)).isIso_inv

/-- The lifted pure-tensor pairing is additive and linear in each variable,
 and commutes with restriction to every object of the fppf site. -/
theorem moduleTensorLiftBilinear_laws [AlgebraicStack X]
    (M N : commAssociatedModules X .fppf) :
    let b := fun (U : X.totalᵒᵖ)
      (x : ((commAssociatedModulesLiftFunctor X .fppf).obj M).val.obj U)
      (y : ((commAssociatedModulesLiftFunctor X .fppf).obj N).val.obj U) ↦
    (ULift.up
      (((associatedModuleTensorIso M N).hom.val.app U).hom
        ((@moduleSheafificationUnitToVal.{u + 1, u, u, u}
            X.total inferInstance (X.associatedTopology .fppf)
            (associatedTopology_hasSheafCompose_commRing X .fppf)
            (associatedTopology_hasWeakSheafify X .fppf)
            (associatedTopology_wEqualsLocallyBijective X .fppf)
            (commAssociatedStructureSheaf X .fppf)
            (PresheafOfModules.Monoidal.tensorObj M.val N.val)).app U
          (x.down ⊗ₜ y.down))) :
      ((commAssociatedModulesLiftFunctor X .fppf).obj
        (moduleTensorAssociated M N)).val.obj U);
    (∀ U x x' y, b U (x + x') y = b U x y + b U x' y) ∧
    (∀ U (r : (commAssociatedStructureSheafLift X .fppf).obj.obj U) x y,
      b U (@SMul.smul ((commAssociatedStructureSheafLift X .fppf).obj.obj U)
        (commAssociatedModuleLiftObj M U)
        (ModuleCat.isModule (commAssociatedModuleLiftObj M U)).toSMul r x) y = @SMul.smul ((commAssociatedStructureSheafLift X .fppf).obj.obj U)
        (commAssociatedModuleLiftObj (moduleTensorAssociated M N) U)
        (ModuleCat.isModule (commAssociatedModuleLiftObj (moduleTensorAssociated M N) U)).toSMul r (b U x y)) ∧
    (∀ U x y y', b U x (y + y') = b U x y + b U x y') ∧
    (∀ U (r : (commAssociatedStructureSheafLift X .fppf).obj.obj U) x y,
      b U x (@SMul.smul ((commAssociatedStructureSheafLift X .fppf).obj.obj U)
        (commAssociatedModuleLiftObj N U)
        (ModuleCat.isModule (commAssociatedModuleLiftObj N U)).toSMul r y) = @SMul.smul ((commAssociatedStructureSheafLift X .fppf).obj.obj U)
        (commAssociatedModuleLiftObj (moduleTensorAssociated M N) U)
        (ModuleCat.isModule (commAssociatedModuleLiftObj (moduleTensorAssociated M N) U)).toSMul r (b U x y)) ∧
    (∀ {U V : X.totalᵒᵖ} (i : U ⟶ V) x y,
      ((commAssociatedModulesLiftFunctor X .fppf).obj
        (moduleTensorAssociated M N)).val.map i
          (b U x y) =
        b V (((commAssociatedModulesLiftFunctor X .fppf).obj M).val.map i x)
          (((commAssociatedModulesLiftFunctor X .fppf).obj N).val.map i y)) := sorry

/-- The lifted pure-tensor pairing as a restriction-compatible bilinear map
 into the lift of the module-category tensor. -/
noncomputable def moduleTensorLiftBilinear [AlgebraicStack X]
    (M N : commAssociatedModules X .fppf) :
    SheafOfModules.RingedSite.SectionBilinearMap.{u + 1, u}
      (commAssociatedStructureSheafLift X .fppf)
      ((commAssociatedModulesLiftFunctor X .fppf).obj M)
      ((commAssociatedModulesLiftFunctor X .fppf).obj N)
      ((commAssociatedModulesLiftFunctor X .fppf).obj
        (moduleTensorAssociated M N)) :=
  let b := fun (U : X.totalᵒᵖ)
      (x : ((commAssociatedModulesLiftFunctor X .fppf).obj M).val.obj U)
      (y : ((commAssociatedModulesLiftFunctor X .fppf).obj N).val.obj U) ↦
    (ULift.up
      (((associatedModuleTensorIso M N).hom.val.app U).hom
        ((@moduleSheafificationUnitToVal.{u + 1, u, u, u}
            X.total inferInstance (X.associatedTopology .fppf)
            (associatedTopology_hasSheafCompose_commRing X .fppf)
            (associatedTopology_hasWeakSheafify X .fppf)
            (associatedTopology_wEqualsLocallyBijective X .fppf)
            (commAssociatedStructureSheaf X .fppf)
            (PresheafOfModules.Monoidal.tensorObj M.val N.val)).app U
          (x.down ⊗ₜ y.down))) :
      ((commAssociatedModulesLiftFunctor X .fppf).obj
        (moduleTensorAssociated M N)).val.obj U);
  let laws := moduleTensorLiftBilinear_laws M N
  { app U := LinearMap.mk₂ ((commAssociatedStructureSheafLift X .fppf).obj.obj U)
      (b U) (laws.1 U) (laws.2.1 U) (laws.2.2.1 U) (laws.2.2.2.1 U)
    naturality := laws.2.2.2.2 }

/-- Comparison from the tensor of universe lifts to the lift of the module
tensor. -/
noncomputable def moduleTensorLiftComparison [AlgebraicStack X]
    (M N : commAssociatedModules X .fppf) :
    moduleTensorAssociatedLift
      ((commAssociatedModulesLiftFunctor X .fppf).obj M)
      ((commAssociatedModulesLiftFunctor X .fppf).obj N) ⟶
    (commAssociatedModulesLiftFunctor X .fppf).obj
      (moduleTensorAssociated M N) :=
  SheafOfModules.RingedSite.SectionBilinearMap.hom.{u + 1, u}
    (moduleTensorLiftBilinear M N)

/-- The comparison determined by an evaluation `F ⊗ H ⟶ G`: transport to the
commutative fppf presentation, lift universes, and curry into the actual sheaf
of local morphisms. -/
def internalHomComparison [AlgebraicStack X] (F G H : QCoh X)
    (ev : tensor F H ⟶ G) :
    (commAssociatedModulesLiftFunctor X .fppf).obj ((toCommFppfModules X).obj H.obj) ⟶
      SheafOfModules.RingedSite.InternalHom.obj.{u + 1, u, u + 1}
        (commAssociatedStructureSheafLift X .fppf)
        ((commAssociatedModulesLiftFunctor X .fppf).obj ((toCommFppfModules X).obj F.obj))
        ((commAssociatedModulesLiftFunctor X .fppf).obj ((toCommFppfModules X).obj G.obj)) :=
  SheafOfModules.RingedSite.InternalHom.homEquiv.{u + 1, u}
      (commAssociatedStructureSheafLift X .fppf)
      ((commAssociatedModulesLiftFunctor X .fppf).obj ((toCommFppfModules X).obj F.obj))
      ((commAssociatedModulesLiftFunctor X .fppf).obj ((toCommFppfModules X).obj H.obj))
      ((commAssociatedModulesLiftFunctor X .fppf).obj ((toCommFppfModules X).obj G.obj))
    (moduleTensorLiftComparison
        ((toCommFppfModules X).obj F.obj)
        ((toCommFppfModules X).obj H.obj) ≫
      (commAssociatedModulesLiftFunctor X .fppf).map
        (tensorComparison F H ≫ (toCommFppfModules X).map ev.hom))

/-- `internalHomComparison` is the currying of the lifted tensor comparison
followed by evaluation. -/
theorem internalHomComparison_eq [AlgebraicStack X] (F G H : QCoh X)
    (ev : tensor F H ⟶ G) :
    internalHomComparison F G H ev =
      SheafOfModules.RingedSite.InternalHom.homEquiv.{u + 1, u}
          (commAssociatedStructureSheafLift X .fppf)
          ((commAssociatedModulesLiftFunctor X .fppf).obj ((toCommFppfModules X).obj F.obj))
          ((commAssociatedModulesLiftFunctor X .fppf).obj ((toCommFppfModules X).obj H.obj))
          ((commAssociatedModulesLiftFunctor X .fppf).obj ((toCommFppfModules X).obj G.obj))
        (moduleTensorLiftComparison
            ((toCommFppfModules X).obj F.obj)
            ((toCommFppfModules X).obj H.obj) ≫
          (commAssociatedModulesLiftFunctor X .fppf).map
            (tensorComparison F H ≫ (toCommFppfModules X).map ev.hom)) :=
  rfl

/-- If `F` is finite locally free, there is a quasi-coherent internal Hom from
`F` to `G` in `Mod(𝒪_𝒳)`, witnessed by an evaluation whose currying is an
isomorphism on the universe-lifted commutative fppf site. -/
theorem internalHom [AlgebraicStack X] (F G : QCoh X)
    [SheafOfModules.IsFiniteLocallyFree F.obj] :
    ∃ (H : QCoh X) (ev : tensor F H ⟶ G),
      IsIso (internalHomComparison F G H ev) :=
  sorry

end AlgebraicGeometry.GroupoidsOver.QCoh.Fppf

