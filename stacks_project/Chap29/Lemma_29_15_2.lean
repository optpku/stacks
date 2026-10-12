/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
import ReasLib.AlgebraicGeometry.Scheme.Morphism.FiniteType

open CategoryTheory
open AlgebraicGeometry
open scoped AlgebraicGeometry

universe u

/- Lemma 29.15.2 (1): local finite type is equivalent to finite type on sections over every
compatible pair of affine opens. -/
@[stacks 01T2] #check
  (AlgebraicGeometry.locallyOfFiniteType_iff :
    ∀ {X S : Scheme.{u}} (f : X ⟶ S),
      LocallyOfFiniteType f ↔
        ∀ ⦃U : S.Opens⦄, IsAffineOpen U →
          ∀ ⦃V : X.Opens⦄, IsAffineOpen V → ∀ e : V ≤ f ⁻¹ᵁ U,
            (CommRingCat.Hom.hom (f.appLE U V e)).FiniteType)

/- Lemma 29.15.2 (2): local finite type is equivalent to a two-level open-cover condition whose
restricted morphisms are locally of finite type. -/
@[stacks 01T2] #check
  (AlgebraicGeometry.Scheme.Hom.locallyOfFiniteType_iff_exists_openCover :
    ∀ {X S : Scheme.{u}} (f : X ⟶ S),
      LocallyOfFiniteType f ↔
        ∃ 𝒱 : S.OpenCover, ∀ j : 𝒱.I₀,
          ∃ 𝒰 : ((𝒱.pullback₁ f).X j).OpenCover,
            ∀ i : 𝒰.I₀, LocallyOfFiniteType (𝒰.f i ≫ 𝒱.pullbackHom f j))

/- Lemma 29.15.2 (3): local finite type is equivalent to an affine two-level cover condition whose
induced maps on global sections are of finite type. -/
@[stacks 01T2] #check
  (AlgebraicGeometry.Scheme.Hom.locallyOfFiniteType_iff_exists_affineOpenCover :
    ∀ {X S : Scheme.{u}} (f : X ⟶ S),
      LocallyOfFiniteType f ↔
        ∃ 𝒱 : S.AffineOpenCover, ∀ j : 𝒱.I₀,
          ∃ 𝒰 : ((𝒱.openCover.pullback₁ f).X j).AffineOpenCover,
            ∀ i : 𝒰.I₀,
              (CommRingCat.Hom.hom
                (Scheme.Hom.appTop (𝒰.f i ≫ 𝒱.openCover.pullbackHom f j))).FiniteType)

/- Lemma 29.15.2 (4): local finite type is preserved by restricting to arbitrary compatible open
subschemes of the source and target. -/
@[stacks 01T2] #check
  (AlgebraicGeometry.instLocallyOfFiniteTypeResLE :
    ∀ {X S : Scheme.{u}} (f : X ⟶ S) (U : X.Opens) (V : S.Opens)
      (e : U ≤ f ⁻¹ᵁ V) [LocallyOfFiniteType f],
        LocallyOfFiniteType (f.resLE V U e))
