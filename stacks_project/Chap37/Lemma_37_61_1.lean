module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Perfect.Locality
import StacksCheckRecall

@[expose] public section

open CategoryTheory
open AlgebraicGeometry
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Hom

/- Lemma 37.61.1: for a locally finite-type morphism, perfectness of the section-ring maps
on one compatible pair of affine covers is equivalent to perfectness on every compatible
pair of affine opens. -/
@[stacks 0686] #check
  (AlgebraicGeometry.Scheme.Hom.perfect_tfae :
    ∀ {X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFiniteType f],
      List.TFAE [
        ∃ 𝒱 : S.AffineOpenCover,
          ∀ j : 𝒱.I₀,
            ∃ 𝒰 : ((𝒱.openCover.pullback₁ f).X j).AffineOpenCover,
              ∀ i : 𝒰.I₀,
                RingHom.IsPerfectRingMap
                  ((𝒰.f i ≫ 𝒱.openCover.pullbackHom f j).appTop).hom,
        ∀ {V : S.Opens}, IsAffineOpen V →
          ∀ {U : X.Opens}, IsAffineOpen U →
            ∀ e : U ≤ f ⁻¹ᵁ V,
              RingHom.IsPerfectRingMap (f.appLE V U e).hom
      ])

end AlgebraicGeometry.Scheme.Hom
