/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import ReasLib.AlgebraicGeometry.Scheme.Module.RegularSection
import StacksCheckRecall

open Opposite
open scoped AlgebraicGeometry

noncomputable section

universe u

section LocallyRingedSpace

variable {X : AlgebraicGeometry.LocallyRingedSpace.{u}}
variable (f : X.toRingedSpace.presheaf.obj (op ⊤))

/- Lemma 31.14.7 (1): a global function on a locally ringed space is regular exactly when its
germ is a nonzerodivisor in every stalk. -/
@[stacks 01WZ] #check
  (AlgebraicGeometry.RingedSpace.isRegularStructureSection_iff_stalkwise
      (X := X.toRingedSpace) f :
    AlgebraicGeometry.RingedSpace.IsRegularSection
        (SheafOfModules.unit X.toRingedSpace.ringCatSheaf)
        ((SheafOfModules.unit X.toRingedSpace.ringCatSheaf).unitHomEquiv
          (AlgebraicGeometry.RingedSpace.globalSectionMul f
            (SheafOfModules.unit X.toRingedSpace.ringCatSheaf))) ↔
      ∀ x : X.toRingedSpace,
        IsSMulRegular (X.toRingedSpace.presheaf.stalk x)
          (X.toRingedSpace.presheaf.germ ⊤ x (Set.mem_univ x) f))

end LocallyRingedSpace

section Scheme

variable {X : AlgebraicGeometry.Scheme.{u}}
variable (f : Γ(X, ⊤))

/- Lemma 31.14.7 (2): a global function on a scheme is regular exactly when its restriction is a
nonzerodivisor on every affine open. -/
@[stacks 01WZ] #check
  (AlgebraicGeometry.Scheme.isRegularStructureSection_iff_forall_affineOpen f :
    AlgebraicGeometry.RingedSpace.IsRegularSection
        (SheafOfModules.unit X.toRingedSpace.ringCatSheaf)
        ((SheafOfModules.unit X.toRingedSpace.ringCatSheaf).unitHomEquiv
          (AlgebraicGeometry.RingedSpace.globalSectionMul f
            (SheafOfModules.unit X.toRingedSpace.ringCatSheaf))) ↔
      ∀ U : X.affineOpens,
        IsSMulRegular Γ(X, U)
          (X.presheaf.map (TopologicalSpace.Opens.leTop (U : X.Opens)).op f))

/- Lemma 31.14.7 (3): restriction of a global function is a nonzerodivisor on every affine open
exactly when this holds on every member of some affine open cover. -/
@[stacks 01WZ] #check
  (AlgebraicGeometry.Scheme.forall_affineOpen_isSMulRegular_iff_exists_affineOpenCover f :
    (∀ U : X.affineOpens,
        IsSMulRegular Γ(X, U)
          (X.presheaf.map (TopologicalSpace.Opens.leTop (U : X.Opens)).op f)) ↔
      ∃ 𝒰 : X.AffineOpenCover,
        ∀ i : 𝒰.I₀,
          IsSMulRegular Γ(X, (𝒰.f i).opensRange)
            (X.presheaf.map
              (TopologicalSpace.Opens.leTop ((𝒰.f i).opensRange)).op f))

end Scheme
