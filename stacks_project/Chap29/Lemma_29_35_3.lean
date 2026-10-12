/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import ReasLib.AlgebraicGeometry.Scheme.Morphism.Unramified.Locality
import StacksCheckRecall

open CategoryTheory
open AlgebraicGeometry
open scoped AlgebraicGeometry

universe u

/- Lemma 29.35.3 (1): a morphism of schemes is unramified if and only if every map on
sections induced by compatible affine opens is unramified. -/
@[stacks 02G6] #check
  (AlgebraicGeometry.Scheme.Hom.unramified_iff_affineOpen_appLE_unramified :
    ∀ {X S : Scheme.{u}} (f : X ⟶ S),
      AlgebraicGeometry.Unramified f ↔
        ∀ ⦃V : S.Opens⦄, IsAffineOpen V →
          ∀ ⦃U : X.Opens⦄, IsAffineOpen U → ∀ e : U ≤ f ⁻¹ᵁ V,
            RingHom.Unramified (f.appLE V U e).hom)

/- Lemma 29.35.3 (2): a morphism of schemes is unramified if and only if the target has an
open cover whose pullbacks have open covers by unramified morphisms. -/
@[stacks 02G6] #check
  (AlgebraicGeometry.Scheme.Hom.unramified_iff_exists_openCover :
    ∀ {X S : Scheme.{u}} (f : X ⟶ S),
      AlgebraicGeometry.Unramified f ↔
        ∃ 𝒱 : S.OpenCover, ∀ j : 𝒱.I₀,
          ∃ 𝒰 : ((𝒱.pullback₁ f).X j).OpenCover,
            ∀ i : 𝒰.I₀,
              AlgebraicGeometry.Unramified (𝒰.f i ≫ 𝒱.pullbackHom f j))

/- Lemma 29.35.3 (3): a morphism of schemes is unramified if and only if the target and the
corresponding pullbacks have affine open covers whose induced section maps are unramified. -/
@[stacks 02G6] #check
  (AlgebraicGeometry.Scheme.Hom.unramified_iff_exists_affineOpenCover :
    ∀ {X S : Scheme.{u}} (f : X ⟶ S),
      AlgebraicGeometry.Unramified f ↔
        ∃ 𝒱 : S.AffineOpenCover, ∀ j : 𝒱.I₀,
          ∃ 𝒰 : ((𝒱.openCover.pullback₁ f).X j).AffineOpenCover,
            ∀ i : 𝒰.I₀,
              RingHom.Unramified
                (((𝒰.f i ≫ 𝒱.openCover.pullbackHom f j).appTop).hom))

/- Lemma 29.35.3 (4): restricting an unramified morphism to arbitrary compatible open
subschemes preserves unramifiedness. -/
@[stacks 02G6] #check
  (AlgebraicGeometry.Scheme.Hom.unramified_resLE :
    ∀ {X S : Scheme.{u}} (f : X ⟶ S) (U : X.Opens) (V : S.Opens)
      (e : U ≤ f ⁻¹ᵁ V) [AlgebraicGeometry.Unramified f],
        AlgebraicGeometry.Unramified (f.resLE V U e))

/- Lemma 29.35.3 (5): a morphism of schemes is G-unramified if and only if every map on
sections induced by compatible affine opens is G-unramified. -/
@[stacks 02G6] #check
  (AlgebraicGeometry.Scheme.Hom.gUnramified_iff_affineOpen_appLE_gUnramified :
    ∀ {X S : Scheme.{u}} (f : X ⟶ S),
      AlgebraicGeometry.GUnramified f ↔
        ∀ ⦃V : S.Opens⦄, IsAffineOpen V →
          ∀ ⦃U : X.Opens⦄, IsAffineOpen U → ∀ e : U ≤ f ⁻¹ᵁ V,
            RingHom.GUnramified (f.appLE V U e).hom)

/- Lemma 29.35.3 (6): a morphism of schemes is G-unramified if and only if the target has an
open cover whose pullbacks have open covers by G-unramified morphisms. -/
@[stacks 02G6] #check
  (AlgebraicGeometry.Scheme.Hom.gUnramified_iff_exists_openCover :
    ∀ {X S : Scheme.{u}} (f : X ⟶ S),
      AlgebraicGeometry.GUnramified f ↔
        ∃ 𝒱 : S.OpenCover, ∀ j : 𝒱.I₀,
          ∃ 𝒰 : ((𝒱.pullback₁ f).X j).OpenCover,
            ∀ i : 𝒰.I₀,
              AlgebraicGeometry.GUnramified (𝒰.f i ≫ 𝒱.pullbackHom f j))

/- Lemma 29.35.3 (7): a morphism of schemes is G-unramified if and only if the target and the
corresponding pullbacks have affine open covers whose induced section maps are G-unramified. -/
@[stacks 02G6] #check
  (AlgebraicGeometry.Scheme.Hom.gUnramified_iff_exists_affineOpenCover :
    ∀ {X S : Scheme.{u}} (f : X ⟶ S),
      AlgebraicGeometry.GUnramified f ↔
        ∃ 𝒱 : S.AffineOpenCover, ∀ j : 𝒱.I₀,
          ∃ 𝒰 : ((𝒱.openCover.pullback₁ f).X j).AffineOpenCover,
            ∀ i : 𝒰.I₀,
              RingHom.GUnramified
                (((𝒰.f i ≫ 𝒱.openCover.pullbackHom f j).appTop).hom))

/- Lemma 29.35.3 (8): restricting a G-unramified morphism to arbitrary compatible open
subschemes preserves G-unramifiedness. -/
@[stacks 02G6] #check
  (AlgebraicGeometry.Scheme.Hom.gUnramified_resLE :
    ∀ {X S : Scheme.{u}} (f : X ⟶ S) (U : X.Opens) (V : S.Opens)
      (e : U ≤ f ⁻¹ᵁ V) [AlgebraicGeometry.GUnramified f],
        AlgebraicGeometry.GUnramified (f.resLE V U e))
