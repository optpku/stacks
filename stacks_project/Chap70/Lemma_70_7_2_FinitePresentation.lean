module

public import Mathlib.CategoryTheory.Limits.HasLimits
public import stacks_project.Chap65.Definition_65_13_2_Separation
public import stacks_project.Chap66.Definition_66_5_1_QuasiCompact
public import stacks_project.Chap66.Lemma_66_29_2_Pullback
public import stacks_project.Chap67.Definition_67_20_2_Affine
public import stacks_project.Chap70.Lemma_70_5_6_GlobalSections

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Pullback.Equality
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Limit.FinitePresentation

/-!
# Equality transport for module pullback

The canonical equality-transport isomorphism and its component formula are available
alongside the historical module-pullback imports.
-/

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry AlgebraicSpace

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Modules

variable {S : Scheme.{u}}

#check (pullbackCongr : ∀ {X Y : AlgebraicSpace S} {f g : X ⟶ Y} (h : f = g),
    pullback f ≅ pullback g)

#check (pullbackCongr_hom_app :
    ∀ {X Y : AlgebraicSpace S} {f g : X ⟶ Y} (h : f = g) (ℱ : Y.Modules),
      (pullbackCongr h).hom.app ℱ =
        eqToHom (congrArg (fun φ ↦ (pullback φ).obj ℱ) h))

end AlgebraicGeometry.AlgebraicSpace.Modules
