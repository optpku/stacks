module

public import Mathlib.Data.List.TFAE
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.LocallyNoetherianFibers
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.LocallyOfType
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Regular
public import ReasLib.RingTheory.Regular.Locality

/-!
# Criteria for regular morphisms of schemes

This file characterizes regular scheme morphisms using affine section rings and compatible
open covers.
-/

@[expose] public section

open CategoryTheory
open AlgebraicGeometry
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry
namespace Scheme.Hom

variable {X Y : Scheme.{u}}

/-- Under the locally Noetherian fibre hypothesis, a scheme morphism is regular exactly when
it locally satisfies regularity on affine section rings. -/
theorem regular_iff_locallyOfType (f : X ⟶ Y)
    (h_fibers : LocallyNoetherianFibers f) :
    Regular f ↔ LocallyOfType RingHom.Regular f := sorry

/-- Under the locally Noetherian fibre hypothesis, a scheme morphism is regular exactly when
every map on sections induced by compatible affine opens is regular. -/
theorem regular_iff_affineOpen_appLE (f : X ⟶ Y)
    (h_fibers : LocallyNoetherianFibers f) :
    Regular f ↔
      ∀ {V : Y.Opens}, IsAffineOpen V →
        ∀ {U : X.Opens}, IsAffineOpen U →
          ∀ e : U ≤ f ⁻¹ᵁ V,
            RingHom.Regular (f.appLE V U e).hom := sorry

/-- Under the locally Noetherian fibre hypothesis, a scheme morphism is regular exactly when
the target and its pullbacks have compatible open covers by regular morphisms. -/
theorem regular_iff_exists_openCover (f : X ⟶ Y)
    (h_fibers : LocallyNoetherianFibers f) :
    Regular f ↔
      ∃ 𝒱 : Y.OpenCover,
        ∀ j : 𝒱.I₀,
          ∃ 𝒰 : ((𝒱.pullback₁ f).X j).OpenCover,
            ∀ i : 𝒰.I₀,
              Regular (𝒰.f i ≫ 𝒱.pullbackHom f j) := sorry

/-- Under the locally Noetherian fibre hypothesis, a scheme morphism is regular exactly when
compatible affine covers induce regular maps on global sections. -/
theorem regular_iff_exists_affineOpenCover (f : X ⟶ Y)
    (h_fibers : LocallyNoetherianFibers f) :
    Regular f ↔
      ∃ 𝒱 : Y.AffineOpenCover,
        ∀ j : 𝒱.I₀,
          ∃ 𝒰 : ((𝒱.openCover.pullback₁ f).X j).AffineOpenCover,
            ∀ i : 𝒰.I₀,
              RingHom.Regular
                ((𝒰.f i ≫ 𝒱.openCover.pullbackHom f j).appTop).hom := sorry

/-- For a scheme morphism with locally Noetherian fibres, regularity, flatness with
geometrically regular fibres, and the affine and cover-local criteria are equivalent. -/
theorem regular_tfae (f : X ⟶ Y) (h_fibers : LocallyNoetherianFibers f) :
    List.TFAE [
      Regular f,
      Flat f ∧
        ∀ y : Y,
          Scheme.Hom.IsGeometricallyRegular (f.fiberToSpecResidueField y),
      ∀ {V : Y.Opens}, IsAffineOpen V →
        ∀ {U : X.Opens}, IsAffineOpen U →
          ∀ e : U ≤ f ⁻¹ᵁ V,
            RingHom.Regular (f.appLE V U e).hom,
      ∃ 𝒱 : Y.OpenCover,
        ∀ j : 𝒱.I₀,
          ∃ 𝒰 : ((𝒱.pullback₁ f).X j).OpenCover,
            ∀ i : 𝒰.I₀,
              Regular (𝒰.f i ≫ 𝒱.pullbackHom f j),
      ∃ 𝒱 : Y.AffineOpenCover,
        ∀ j : 𝒱.I₀,
          ∃ 𝒰 : ((𝒱.openCover.pullback₁ f).X j).AffineOpenCover,
            ∀ i : 𝒰.I₀,
              RingHom.Regular
                ((𝒰.f i ≫ 𝒱.openCover.pullbackHom f j).appTop).hom
    ] := sorry

end Scheme.Hom
end AlgebraicGeometry
