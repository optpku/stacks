module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Smooth.Locality
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry
open CategoryTheory
open scoped AlgebraicGeometry

universe u

/- Lemma 29.34.2: a scheme morphism is smooth if and only if all maps on sections induced by
compatible affine opens are smooth. -/
@[stacks 01V6] #check
  (AlgebraicGeometry.smooth_iff :
    ∀ {X S : Scheme.{u}} (f : X ⟶ S),
      Smooth f ↔
        ∀ {V : S.Opens}, IsAffineOpen V →
          ∀ {U : X.Opens}, IsAffineOpen U → ∀ e : U ≤ f ⁻¹ᵁ V,
            RingHom.Smooth (f.appLE V U e).hom)

/- A scheme morphism is smooth if and only if the target has an open cover whose pullbacks
have open covers by smooth morphisms. -/
#check
  (AlgebraicGeometry.Scheme.Hom.smooth_iff_exists_openCover :
    ∀ {X S : Scheme.{u}} (f : X ⟶ S),
      Smooth f ↔
        ∃ 𝒱 : S.OpenCover, ∀ j : 𝒱.I₀,
          ∃ 𝒰 : ((𝒱.pullback₁ f).X j).OpenCover,
            ∀ i : 𝒰.I₀, Smooth (𝒰.f i ≫ 𝒱.pullbackHom f j))

/- A scheme morphism is smooth if and only if the target has an affine open cover whose
pullbacks have affine open covers with smooth induced maps on global sections. -/
#check
  (AlgebraicGeometry.Scheme.Hom.smooth_iff_exists_affineOpenCover :
    ∀ {X S : Scheme.{u}} (f : X ⟶ S),
      Smooth f ↔
        ∃ 𝒱 : S.AffineOpenCover, ∀ j : 𝒱.I₀,
          ∃ 𝒰 : ((𝒱.openCover.pullback₁ f).X j).AffineOpenCover,
            ∀ i : 𝒰.I₀,
              RingHom.Smooth
                (((𝒰.f i ≫ 𝒱.openCover.pullbackHom f j).appTop).hom))

/- Restricting a smooth morphism to arbitrary compatible open subschemes preserves
smoothness. -/
#check
  (AlgebraicGeometry.instSmoothResLE :
    ∀ {X S : Scheme.{u}} (f : X ⟶ S) (U : X.Opens) (V : S.Opens)
      (e : U ≤ f ⁻¹ᵁ V) [Smooth f],
        Smooth (f.resLE V U e))
