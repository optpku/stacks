module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Integral.Cover
import StacksCheckRecall

@[expose] public section

open CategoryTheory
open AlgebraicGeometry
open scoped AlgebraicGeometry

universe u

/- Lemma 29.44.2 (1): a morphism of schemes is integral if and only if there exists an affine
open covering of the target such that every preimage is affine and the induced map on global
sections is integral. -/
@[stacks 02K8] #check
  (AlgebraicGeometry.isIntegralHom_iff_exists_affineOpenCover :
    ∀ {X S : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ S),
      AlgebraicGeometry.IsIntegralHom f ↔
        ∃ 𝒰 : S.AffineOpenCover.{u},
          ∀ i : 𝒰.I₀,
            AlgebraicGeometry.IsAffine (f ⁻¹ᵁ (𝒰.f i).opensRange) ∧
              (CommRingCat.Hom.hom
                (AlgebraicGeometry.Scheme.Hom.appTop
                  (f ∣_ (𝒰.f i).opensRange))).IsIntegral)

/- Lemma 29.44.2 (2): a morphism of schemes is integral if and only if there exists an open
covering of the target such that every restriction over a member is integral. -/
@[stacks 02K8] #check
  (AlgebraicGeometry.isIntegralHom_iff_exists_openCover :
    ∀ {X S : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ S),
      AlgebraicGeometry.IsIntegralHom f ↔
        ∃ 𝒰 : S.OpenCover.{u},
          ∀ i : 𝒰.I₀,
            AlgebraicGeometry.IsIntegralHom (f ∣_ (𝒰.f i).opensRange))

/- Lemma 29.44.2 (3): an integral morphism remains integral after restriction to every open
subscheme of the target. -/
@[stacks 02K8] #check
  (AlgebraicGeometry.IsZariskiLocalAtTarget.restrict
      (P := @AlgebraicGeometry.IsIntegralHom) :
    ∀ {X S : AlgebraicGeometry.Scheme.{u}} {f : X ⟶ S},
      AlgebraicGeometry.IsIntegralHom f →
        ∀ U : S.Opens, AlgebraicGeometry.IsIntegralHom (f ∣_ U))
