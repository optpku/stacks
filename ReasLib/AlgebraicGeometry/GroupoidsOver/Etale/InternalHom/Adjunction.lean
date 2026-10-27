/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.GroupoidsOver.Etale.InternalHom
public import ReasLib.AlgebraicGeometry.GroupoidsOver.Etale.LocallyQuasiCoherent
public import ReasLib.Algebra.Category.ModuleCat.Presheaf.Tensor.Bilinear
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.SheafificationMonoidal

/-! # Tensor adjunction for the small étale internal Hom -/

@[expose] public section

open CategoryTheory CategoryTheory.MonoidalCategory Opposite
open SheafOfModules.RingedSite
open scoped TensorProduct

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidsOver

variable {S : Scheme.{u}} {X : GroupoidsOver S}

/-- Sheafification of the pointwise tensor of two étale module sheaves. -/
def etalePointwiseTensorSheafify (H F : etaleModules X) : etaleModules X :=
  (moduleSheafification.{u + 1, u, u, u} (commEtaleStructureSheaf X)).obj
    (PresheafOfModules.Monoidal.tensorObj H.val F.val)

/-- The section of the sheafified tensor induced by a pair of sections. -/
def etalePointwiseTensorSection {H F : etaleModules X}
    (U : X.totalᵒᵖ) (x : H.val.obj U) (y : F.val.obj U) :
    (etalePointwiseTensorSheafify H F).val.obj U :=
  (moduleSheafificationUnitToVal.{u + 1, u, u, u} (commEtaleStructureSheaf X)
    (PresheafOfModules.Monoidal.tensorObj H.val F.val)).app U (x ⊗ₜ y)

/-- Sheafification of the pointwise tensor agrees with the tensor of module sheaves. -/
def etalePointwiseTensorSheafify_iso (H F : etaleModules X) :
    etalePointwiseTensorSheafify H F ≅ moduleTensorEtale H F :=
  (Functor.Monoidal.μIso
    (moduleSheafification.{u + 1, u, u, u} (commEtaleStructureSheaf X))
    H.val F.val).symm ≪≫
  tensorIso
    (moduleSheafificationValIso.{u + 1, u, u, u} (commEtaleStructureSheaf X) H)
    (moduleSheafificationValIso.{u + 1, u, u, u} (commEtaleStructureSheaf X) F)

namespace EtaleSheafHom

variable (F G H : etaleModules X) [F.IsFinitePresentation]

/-- Evaluate the local morphism classified by a section at the terminal slice object. -/
def uncurryFun (f : H ⟶ moduleSheafHomEtale F G) (U : X.totalᵒᵖ)
    (x : H.val.obj U) (y : F.val.obj U) : G.val.obj U :=
  ((sectionsEquiv F G U ((f.val.app U) x)).val.app (op (Over.mk (𝟙 U.unop)))) y

/-- Evaluation of a morphism into the internal Hom is bilinear and commutes with restriction. -/
theorem uncurry_laws (f : H ⟶ moduleSheafHomEtale F G) :
    (∀ U (x x' : H.val.obj U) (y : F.val.obj U),
      uncurryFun F G H f U (x + x') y =
        uncurryFun F G H f U x y + uncurryFun F G H f U x' y) ∧
    (∀ U (r : (commEtaleStructureSheaf X).obj.obj U) (x : H.val.obj U) (y : F.val.obj U),
      uncurryFun F G H f U (r • x) y = r • uncurryFun F G H f U x y) ∧
    (∀ U (x : H.val.obj U) (y y' : F.val.obj U),
      uncurryFun F G H f U x (y + y') =
        uncurryFun F G H f U x y + uncurryFun F G H f U x y') ∧
    (∀ U (r : (commEtaleStructureSheaf X).obj.obj U) (x : H.val.obj U) (y : F.val.obj U),
      uncurryFun F G H f U x (r • y) = r • uncurryFun F G H f U x y) ∧
    (∀ {U V} (i : U ⟶ V) (x : H.val.obj U) (y : F.val.obj U),
      G.val.map i (uncurryFun F G H f U x y) =
        uncurryFun F G H f V (H.val.map i x) (F.val.map i y)) := sorry

/-- The compatible bilinear evaluation of a morphism into the small internal Hom. -/
def uncurryBilinear (f : H ⟶ moduleSheafHomEtale F G) :
    PresheafOfModules.BilinearMap (commEtaleStructureSheaf X).obj H.val F.val G.val where
  app U := LinearMap.mk₂ _ (uncurryFun F G H f U)
    ((uncurry_laws F G H f).1 U) ((uncurry_laws F G H f).2.1 U)
    ((uncurry_laws F G H f).2.2.1 U) ((uncurry_laws F G H f).2.2.2.1 U)
  naturality := (uncurry_laws F G H f).2.2.2.2

/-- Uncurrying into the tensor product of étale module sheaves. -/
def uncurry (f : H ⟶ moduleSheafHomEtale F G) : moduleTensorEtale H F ⟶ G :=
  (etalePointwiseTensorSheafify_iso H F).inv ≫
    (moduleSheafificationHomEquiv.{u + 1, u, u, u} (commEtaleStructureSheaf X)
      (PresheafOfModules.Monoidal.tensorObj H.val F.val) G).symm
        (uncurryBilinear F G H f).toHom

/-- Evaluation of a tensor morphism after restricting the first section to a slice object. -/
def curryLocalFun (g : moduleTensorEtale H F ⟶ G) (U : X.totalᵒᵖ)
    (x : H.val.obj U) (W : (Over U.unop)ᵒᵖ)
    (y : (F.over U.unop).val.obj W) : (G.over U.unop).val.obj W :=
  (g.val.app (op W.unop.left))
    ((etalePointwiseTensorSheafify_iso H F).hom.val.app (op W.unop.left)
      (etalePointwiseTensorSection (op W.unop.left) (H.val.map W.unop.hom.op x) y))

/-- Local tensor evaluation is linear and commutes with restriction in the slice. -/
theorem curryLocal_laws (g : moduleTensorEtale H F ⟶ G) (U : X.totalᵒᵖ)
    (x : H.val.obj U) :
    (∀ W (y y' : (F.over U.unop).val.obj W),
      curryLocalFun F G H g U x W (y + y') =
        curryLocalFun F G H g U x W y + curryLocalFun F G H g U x W y') ∧
    (∀ W (r : ((etaleStructureSheaf X).over U.unop).obj.obj W)
      (y : (F.over U.unop).val.obj W),
      curryLocalFun F G H g U x W (r • y) = r • curryLocalFun F G H g U x W y) ∧
    (∀ {W W'} (i : W ⟶ W') (y : (F.over U.unop).val.obj W),
      (G.over U.unop).val.map i (curryLocalFun F G H g U x W y) =
        curryLocalFun F G H g U x W' ((F.over U.unop).val.map i y)) := sorry

/-- The local module morphism obtained by fixing the first tensor argument. -/
def curryLocal (g : moduleTensorEtale H F ⟶ G) (U : X.totalᵒᵖ)
    (x : H.val.obj U) : F.over U.unop ⟶ G.over U.unop where
  val :=
    { app W := ModuleCat.ofHom
        (X := (F.over U.unop).val.obj W) (Y := (G.over U.unop).val.obj W)
        { toFun := curryLocalFun F G H g U x W
          map_add' := (curryLocal_laws F G H g U x).1 W
          map_smul' := (curryLocal_laws F G H g U x).2.1 W }
      naturality := fun {_ _} i => ModuleCat.hom_ext (LinearMap.ext
        (fun y => ((curryLocal_laws F G H g U x).2.2 i y).symm)) }

/-- Encode local tensor evaluation as a section of the small internal Hom. -/
def curryFun (g : moduleTensorEtale H F ⟶ G) (U : X.totalᵒᵖ)
    (x : H.val.obj U) : (moduleSheafHomEtale F G).val.obj U :=
  (encode F G U).rangeRestrict (curryLocal F G H g U x)

/-- Encoded currying is linear and commutes with restriction. -/
theorem curry_laws (g : moduleTensorEtale H F ⟶ G) :
    (∀ U (x x' : H.val.obj U),
      curryFun F G H g U (x + x') = curryFun F G H g U x + curryFun F G H g U x') ∧
    (∀ U (r : (commEtaleStructureSheaf X).obj.obj U) (x : H.val.obj U),
      curryFun F G H g U (r • x) = r • curryFun F G H g U x) ∧
    (∀ {U V} (i : U ⟶ V) (x : H.val.obj U),
      (moduleSheafHomEtale F G).val.map i (curryFun F G H g U x) =
        curryFun F G H g V (H.val.map i x)) := sorry

/-- Currying a tensor morphism into the small étale internal Hom. -/
def curry (g : moduleTensorEtale H F ⟶ G) : H ⟶ moduleSheafHomEtale F G where
  val :=
    { app U := ModuleCat.ofHom
        (X := H.val.obj U) (Y := (moduleSheafHomEtale F G).val.obj U)
        { toFun := curryFun F G H g U
          map_add' := (curry_laws F G H g).1 U
          map_smul' := (curry_laws F G H g).2.1 U }
      naturality := fun {_ _} i => ModuleCat.hom_ext (LinearMap.ext
        (fun x => ((curry_laws F G H g).2.2 i x).symm)) }

/-- Currying after uncurrying recovers a morphism into the internal Hom. -/
theorem curry_uncurry (f : H ⟶ moduleSheafHomEtale F G) :
    curry F G H (uncurry F G H f) = f := sorry

/-- Uncurrying after currying recovers a tensor morphism. -/
theorem uncurry_curry (g : moduleTensorEtale H F ⟶ G) :
    uncurry F G H (curry F G H g) = g := sorry

end EtaleSheafHom

/-- Tensor morphisms correspond to morphisms into the small étale internal Hom. -/
def moduleSheafHomOnEtale_homEquiv (F G H : etaleModules X) [F.IsFinitePresentation] :
    (H ⟶ moduleSheafHomEtale F G) ≃ (moduleTensorEtale H F ⟶ G) where
  toFun := EtaleSheafHom.uncurry F G H
  invFun := EtaleSheafHom.curry F G H
  left_inv := EtaleSheafHom.curry_uncurry F G H
  right_inv := EtaleSheafHom.uncurry_curry F G H

/-- Internal Hom from a finitely presented module into a locally quasi-coherent module
is locally quasi-coherent. -/
instance isLocallyQuasiCoherent_moduleSheafHomEtale
    (F G : etaleModules X) [F.IsFinitePresentation] [IsLocallyQuasiCoherent G] :
    IsLocallyQuasiCoherent (moduleSheafHomEtale F G) := sorry

end AlgebraicGeometry.GroupoidsOver
