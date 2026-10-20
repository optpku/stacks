/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Restrict
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import ReasLib.Algebra.Module.FinitePresentation.Relative
public import ReasLib.AlgebraicGeometry.Scheme.Module.Sections
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FiniteType

/-!
# Relative finite presentation for scheme modules

Relative finite presentation is tested on compatible affine opens by the corresponding
relative finite-presentation predicate for modules over commutative rings.
-/

@[expose] public section

open CategoryTheory
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules

variable {X S : Scheme.{u}}

/-- A scheme module is relatively finitely presented when its sections on every compatible pair
of affine opens are relatively finitely presented over the induced section-ring map. -/
def finitePresentationOver (f : X ⟶ S) [LocallyOfFiniteType f] : ObjectProperty X.Modules :=
  fun F ↦
    ∀ ⦃U : X.Opens⦄, IsAffineOpen U →
      ∀ ⦃V : S.Opens⦄, IsAffineOpen V → ∀ e : U ≤ f ⁻¹ᵁ V,
        @Module.FinitePresentationRelativeTo
          Γ(S, V) Γ(X, U) Γ(F, U) _ _ (Scheme.Hom.sectionsAlgebra f V U e) _ _

/-- `IsFinitePresentationOver F f` is the relative finite-presentation property of `F` over `f`.
-/
abbrev IsFinitePresentationOver (F : X.Modules) (f : X ⟶ S)
    [LocallyOfFiniteType f] : Prop :=
  finitePresentationOver f F

/-- Relative finite presentation is equivalent to the compatible affine-open section criterion.
-/
theorem finitePresentationOver_iff_affineOpenCover (F : X.Modules) (f : X ⟶ S)
    [LocallyOfFiniteType f] :
    F.IsFinitePresentationOver f ↔
      ∀ ⦃U : X.Opens⦄, IsAffineOpen U →
        ∀ ⦃V : S.Opens⦄, IsAffineOpen V → ∀ e : U ≤ f ⁻¹ᵁ V,
          @Module.FinitePresentationRelativeTo
            Γ(S, V) Γ(X, U) Γ(F, U) _ _ (Scheme.Hom.sectionsAlgebra f V U e) _ _ := sorry

/-- A quasicoherent scheme module is relatively finitely presented exactly when this holds for
its section modules on suitable nested affine open covers of the target and its inverse images. -/
theorem isFinitePresentationOver_iff_exists_affineOpenCover (f : X ⟶ S)
    [LocallyOfFiniteType f] (F : X.Modules) [F.IsQuasicoherent] :
    F.IsFinitePresentationOver f ↔
      ∃ 𝒱 : S.AffineOpenCover.{u}, ∀ j : 𝒱.I₀,
        ∃ 𝒰 : ((𝒱.openCover.pullback₁ f).X j).AffineOpenCover.{u}, ∀ i : 𝒰.I₀,
          @Module.FinitePresentationRelativeTo
            Γ(Spec (𝒱.X j), ⊤) Γ(Spec (𝒰.X i), ⊤)
            Γ((Scheme.Modules.pullback
              (𝒰.f i ≫ (𝒱.openCover.pullback₁ f).f j)).obj F, ⊤)
            _ _ (Scheme.Hom.appTop
              (𝒰.f i ≫ 𝒱.openCover.pullbackHom f j)).hom.toAlgebra _ _ := sorry

end AlgebraicGeometry.Scheme.Modules
