/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FormallySmooth.Locality
import StacksCheckRecall

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.FormallySmooth

/- Lemma 37.11.10: formal smoothness of a scheme morphism is equivalent to formal
smoothness on pointwise open neighborhoods, on every compatible pair of affine opens,
and on the members of compatible affine open covers. -/
@[stacks 0D0F] #check (AlgebraicGeometry.FormallySmooth.affineOpen_tfae :
  ∀ {X Y : Scheme.{u}} (f : X ⟶ Y),
    List.TFAE [
      FormallySmooth f,
      ∀ x : X,
        ∃ U : X.Opens, ∃ V : Y.Opens,
          ∃ (hx : x ∈ U) (e : U ≤ f ⁻¹ᵁ V),
            FormallySmooth (f.resLE V U e),
      ∀ {V : Y.Opens}, IsAffineOpen V →
        ∀ {U : X.Opens}, IsAffineOpen U →
          ∀ e : U ≤ f ⁻¹ᵁ V,
            (f.appLE V U e).hom.FormallySmooth,
      ∃ 𝒱 : Y.AffineOpenCover,
        ∀ j : 𝒱.I₀,
          ∃ 𝒰 : ((𝒱.openCover.pullback₁ f).X j).AffineOpenCover,
            ∀ i : 𝒰.I₀,
              ((𝒰.f i ≫ 𝒱.openCover.pullbackHom f j).appTop).hom.FormallySmooth
    ])

end AlgebraicGeometry.FormallySmooth
