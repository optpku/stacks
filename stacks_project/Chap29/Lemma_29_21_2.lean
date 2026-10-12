/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FinitePresentation
import StacksCheckRecall

@[expose] public section

open CategoryTheory
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry

/- Lemma 29.21.2 (1): a morphism of schemes is locally of finite presentation if and only if
every map on sections induced by compatible affine opens is of finite presentation. -/
@[stacks 01TQ] #check
  (AlgebraicGeometry.locallyOfFinitePresentation_iff :
    ∀ {X S : Scheme.{u}} (f : X ⟶ S),
      LocallyOfFinitePresentation f ↔
        ∀ {V : S.Opens}, IsAffineOpen V →
          ∀ {U : X.Opens}, IsAffineOpen U → ∀ e : U ≤ f ⁻¹ᵁ V,
            RingHom.FinitePresentation (f.appLE V U e).hom)

/- Lemma 29.21.2 (2): a morphism of schemes is locally of finite presentation if and only if
the target has an open cover whose pullbacks have open covers by locally finitely presented
morphisms. -/
@[stacks 01TQ] #check
  (AlgebraicGeometry.Scheme.Hom.locallyOfFinitePresentation_iff_exists_openCover :
    ∀ {X S : Scheme.{u}} (f : X ⟶ S),
      LocallyOfFinitePresentation f ↔
        ∃ 𝒱 : S.OpenCover, ∀ j : 𝒱.I₀,
          ∃ 𝒰 : ((𝒱.pullback₁ f).X j).OpenCover,
            ∀ i : 𝒰.I₀, LocallyOfFinitePresentation (𝒰.f i ≫ 𝒱.pullbackHom f j))

/- Lemma 29.21.2 (3): a morphism of schemes is locally of finite presentation if and only if
the target has an affine open cover whose pullbacks have affine open covers on which every
induced map on global sections is of finite presentation. -/
@[stacks 01TQ] #check
  (AlgebraicGeometry.Scheme.Hom.locallyOfFinitePresentation_iff_exists_affineOpenCover :
    ∀ {X S : Scheme.{u}} (f : X ⟶ S),
      LocallyOfFinitePresentation f ↔
        ∃ 𝒱 : S.AffineOpenCover, ∀ j : 𝒱.I₀,
          ∃ 𝒰 : ((𝒱.openCover.pullback₁ f).X j).AffineOpenCover,
            ∀ i : 𝒰.I₀,
              RingHom.FinitePresentation
                ((𝒰.f i ≫ 𝒱.openCover.pullbackHom f j).appTop).hom)

/- Lemma 29.21.2 (4): restricting a locally finitely presented morphism to arbitrary compatible
open subschemes preserves local finite presentation. -/
@[stacks 01TQ] #check
  (AlgebraicGeometry.instLocallyOfFinitePresentationResLE :
    ∀ {X S : Scheme.{u}} (f : X ⟶ S) (U : X.Opens) (V : S.Opens)
      (e : U ≤ f ⁻¹ᵁ V) [LocallyOfFinitePresentation f],
        LocallyOfFinitePresentation (f.resLE V U e))

end AlgebraicGeometry
