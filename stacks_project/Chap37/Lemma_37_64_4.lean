/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.WeaklyEtale.Locality
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry
open CategoryTheory
open scoped AlgebraicGeometry

universe u

/- Lemma 37.64.4 (1): weak étaleness is detected on section-ring maps induced by every
compatible pair of affine opens. -/
@[stacks 094S] #check
  (AlgebraicGeometry.Scheme.Hom.weaklyEtale_iff_affineOpen_appLE :
    ∀ {X S : Scheme.{u}} (f : X ⟶ S),
      WeaklyEtale f ↔
        ∀ {V : S.Opens}, IsAffineOpen V →
          ∀ {U : X.Opens}, IsAffineOpen U → ∀ e : U ≤ f ⁻¹ᵁ V,
            RingHom.WeaklyEtale (f.appLE V U e).hom)

/- Lemma 37.64.4 (2): compatible open covers of the target and their pullbacks detect weak
étaleness. -/
@[stacks 094S] #check
  (AlgebraicGeometry.Scheme.Hom.weaklyEtale_iff_exists_openCover :
    ∀ {X S : Scheme.{u}} (f : X ⟶ S),
      WeaklyEtale f ↔
        ∃ 𝒱 : S.OpenCover, ∀ j : 𝒱.I₀,
          ∃ 𝒰 : ((𝒱.pullback₁ f).X j).OpenCover,
            ∀ i : 𝒰.I₀, WeaklyEtale (𝒰.f i ≫ 𝒱.pullbackHom f j))

/- Lemma 37.64.4 (3): compatible affine covers detect weak étaleness through their induced
maps on global sections. -/
@[stacks 094S] #check
  (AlgebraicGeometry.Scheme.Hom.weaklyEtale_iff_exists_affineOpenCover :
    ∀ {X S : Scheme.{u}} (f : X ⟶ S),
      WeaklyEtale f ↔
        ∃ 𝒱 : S.AffineOpenCover, ∀ j : 𝒱.I₀,
          ∃ 𝒰 : ((𝒱.openCover.pullback₁ f).X j).AffineOpenCover,
            ∀ i : 𝒰.I₀,
              RingHom.WeaklyEtale
                ((𝒰.f i ≫ 𝒱.openCover.pullbackHom f j).appTop).hom)

/- Lemma 37.64.4 (4): restricting a weakly étale morphism to compatible open subschemes
preserves weak étaleness. -/
@[stacks 094S] #check
  (AlgebraicGeometry.Scheme.Hom.weaklyEtale_resLE :
    ∀ {X S : Scheme.{u}} {f : X ⟶ S} {V : S.Opens} {U : X.Opens}
      (e : U ≤ f ⁻¹ᵁ V),
      WeaklyEtale f → WeaklyEtale (f.resLE V U e))
