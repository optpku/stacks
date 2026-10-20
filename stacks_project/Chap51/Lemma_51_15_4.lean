/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Dualizing.LocalExistence
public import ReasLib.AlgebraicGeometry.Scheme.Module.Depth.ExtensionAlong

import StacksCheckRecall

@[expose] public section

open CategoryTheory
open AlgebraicGeometry
open scoped AlgebraicGeometry ENat

universe u

namespace AlgebraicGeometry.Scheme.Modules

/- Lemma 51.15.4 (1): under a local dualizing-complex hypothesis and the stated
immediate-specialization depth condition, a coherent module admits a coherent
depth-two extension along `T`. -/
@[stacks 0EI3]
#check (AlgebraicGeometry.Scheme.Modules.IsDepthTwoExtensionAlong.«exists» :
  ∀ {X : Scheme.{u}} [IsNoetherian X]
    (T : Set X) (hT : StableUnderSpecialization T)
    (hdual : LocallyHasDualizingComplex X)
    (F : X.Modules) [F.IsCoherent]
    (hdepth : ∀ ⦃x x' : X⦄, IsImmediateSpecialization x x' →
      x' ∈ T → x ∉ T →
        (1 : ℕ∞) ≤
          moduleDepth (X.presheaf.stalk x) (RingedSpace.stalkModuleCat F x)),
    ∃ (G : X.Modules) (hG : G.IsCoherent) (φ : F ⟶ G),
      IsDepthTwoExtensionAlong T φ)

/- Lemma 51.15.4 (2): two coherent depth-two extensions are related by a unique
compatible target isomorphism. -/
@[stacks 0EI3]
#check (AlgebraicGeometry.Scheme.Modules.IsDepthTwoExtensionAlong.existsUniqueIso :
  ∀ {X : Scheme.{u}} [IsNoetherian X]
    (T : Set X) (hT : StableUnderSpecialization T)
    (hdual : LocallyHasDualizingComplex X)
    (F G H : X.Modules) [F.IsCoherent] [G.IsCoherent] [H.IsCoherent]
    (hdepth : ∀ ⦃x x' : X⦄, IsImmediateSpecialization x x' →
      x' ∈ T → x ∉ T →
        (1 : ℕ∞) ≤
          moduleDepth (X.presheaf.stalk x) (RingedSpace.stalkModuleCat F x))
    (φ : F ⟶ G) (ψ : F ⟶ H)
    (hφ : IsDepthTwoExtensionAlong T φ)
    (hψ : IsDepthTwoExtensionAlong T ψ),
    ∃! e : G ≅ H, φ ≫ e.hom = ψ)

/- Lemma 51.15.4 (3): Cohen–Macaulay pullback preserves the depth-two
extension property over the inverse image of the specialization-stable subset. -/
@[stacks 0EI3]
#check (AlgebraicGeometry.Scheme.Modules.IsDepthTwoExtensionAlong.pullback_of_cohenMacaulay :
  ∀ {X Y : Scheme.{u}}
    [IsNoetherian X] [IsNoetherian Y]
    (T : Set X) (hT : StableUnderSpecialization T)
    (F G : X.Modules) [F.IsCoherent] [G.IsCoherent]
    (φ : F ⟶ G) (hφ : IsDepthTwoExtensionAlong T φ)
    (f : Y ⟶ X) [AlgebraicGeometry.CohenMacaulay f],
    IsDepthTwoExtensionAlong (f.base ⁻¹' T) ((pullback f).map φ))

end AlgebraicGeometry.Scheme.Modules
