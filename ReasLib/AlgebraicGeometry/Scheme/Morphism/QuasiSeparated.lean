module

public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.AffineOpenPair

/-!
# Reusable criteria for quasi-separated scheme morphisms
-/

@[expose] public section

noncomputable section

open CategoryTheory Limits TopologicalSpace
open scoped AlgebraicGeometry

universe u v w

namespace AlgebraicGeometry

namespace Scheme.AffineOpenCover

/-- An affine open cover has compact intersections when every two chart images have compact
intersection in the ambient scheme. -/
@[stacks 01KO "affine cover with compact intersections"]
def HasCompactIntersections {X : Scheme.{u}} (𝒱 : X.AffineOpenCover.{v}) : Prop :=
  ∀ i j : 𝒱.I₀,
    IsCompact ((𝒱.f i).opensRange ∩ (𝒱.f j).opensRange : Set X)

/-- Quasi-separatedness of a scheme is detected by compact intersections in any fixed affine
open cover. -/
@[stacks 01KO "fixed affine-cover criterion"]
theorem quasiSeparatedSpace_iff_hasCompactIntersections
    {X : Scheme.{u}} (𝒱 : X.AffineOpenCover.{v}) :
    QuasiSeparatedSpace X ↔ 𝒱.HasCompactIntersections := sorry

/-- Compact intersections in a fixed affine open cover are equivalently finite unions of affine
opens of the ambient scheme. -/
@[stacks 01KO "finite affine presentation of chart intersections"]
theorem hasCompactIntersections_iff_finiteCover
    {X : Scheme.{u}} (𝒱 : X.AffineOpenCover.{v}) :
    𝒱.HasCompactIntersections ↔
      ∀ i j : 𝒱.I₀, ∃ s : Set X.affineOpens, s.Finite ∧
        (𝒱.f i).opensRange ⊓ (𝒱.f j).opensRange =
          ⨆ W ∈ s, (W : X.Opens) := sorry

end Scheme.AffineOpenCover

/-- Pullback comparisons along quasi-separated scheme morphisms are canonically quasi-compact. -/
@[stacks 01KR "quasi-compact pullback comparison", instance]
instance pullbackMapDesc_quasiCompact
    {X Y T S : Scheme.{u}} (f : X ⟶ T) (g : Y ⟶ T) (h : T ⟶ S)
    [QuasiSeparated h] : QuasiCompact (pullback.mapDesc f g h) := sorry

/-- A scheme morphism is quasi-separated exactly when intersections of affine opens with a
common affine target are compact. -/
@[stacks 01KO]
theorem Scheme.Hom.quasiSeparated_iff_affineInter_isCompact
    {X S : Scheme.{u}} (f : X ⟶ S) :
    QuasiSeparated f ↔
      ∀ (U V : X.affineOpens),
        f.HasCommonAffineTarget U V →
          IsCompact (U ∩ V : Set X) := sorry

/-- A scheme morphism is quasi-separated exactly when every intersection of affine opens with a
common affine target is a finite union of affine opens. -/
@[stacks 01KO "finite affine intersections over a common target"]
theorem Scheme.Hom.quasiSeparated_iff_affineInter_finiteCover
    {X S : Scheme.{u}} (f : X ⟶ S) :
    QuasiSeparated f ↔
      ∀ U V : X.affineOpens, f.HasCommonAffineTarget U V →
        ∃ s : Set X.affineOpens, s.Finite ∧
          (U : X.Opens) ⊓ V = ⨆ W ∈ s, (W : X.Opens) := sorry

/-- Quasi-separatedness can be checked after pullback along any affine open cover of the
target. -/
@[stacks 01KO "fixed target affine-cover criterion"]
theorem Scheme.Hom.quasiSeparated_iff_pullback_quasiSeparatedSpace
    {X S : Scheme.{u}} (f : X ⟶ S) (𝒰 : S.OpenCover) [∀ i, IsAffine (𝒰.X i)] :
    QuasiSeparated f ↔
      ∀ i : 𝒰.I₀, QuasiSeparatedSpace ((𝒰.pullback₁ f).X i) := sorry

/-- A scheme morphism is quasi-separated exactly when some affine open cover of the target has
quasi-separated pullback schemes. -/
@[stacks 01KO]
theorem Scheme.Hom.quasiSeparated_iff_exists_affineCover_pullback
    {X S : Scheme.{u}} (f : X ⟶ S) :
    QuasiSeparated f ↔
      ∃ 𝒰 : S.AffineOpenCover.{v},
        ∀ i : 𝒰.I₀, QuasiSeparatedSpace ((𝒰.openCover.pullback₁ f).X i) := sorry

/-- A scheme morphism is quasi-separated exactly when some affine target cover has inverse-image
affine covers with compact intersections. -/
@[stacks 01KO "affine-cover intersection criterion"]
theorem Scheme.Hom.quasiSeparated_iff_exists_affineCover_hasCompactIntersections
    {X S : Scheme.{u}} (f : X ⟶ S) :
    QuasiSeparated f ↔
      ∃ 𝒰 : S.AffineOpenCover.{v}, ∀ i : 𝒰.I₀,
        ∃ 𝒱 : ((𝒰.openCover.pullback₁ f).X i).AffineOpenCover.{w},
          𝒱.HasCompactIntersections := sorry

end AlgebraicGeometry
