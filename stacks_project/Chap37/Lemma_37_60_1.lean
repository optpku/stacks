/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.PseudoCoherent.Locality
import StacksCheckRecall

open CategoryTheory
open AlgebraicGeometry
open scoped AlgebraicGeometry

universe u

/- Lemma 37.60.1: pseudo-coherence on one compatible pair of affine covers,
pseudo-coherence on every compatible pair of affine opens, and local finite type together
with relative pseudo-coherence of `𝒪_X` are equivalent. -/
@[stacks 067Y] #check
  (AlgebraicGeometry.Scheme.Hom.pseudoCoherent_tfae :
    ∀ {X S : Scheme.{u}} (f : X ⟶ S),
      List.TFAE [
        ∃ 𝒱 : S.AffineOpenCover,
          ∀ j : 𝒱.I₀,
            ∃ 𝒰 : ((𝒱.openCover.pullback₁ f).X j).AffineOpenCover,
              ∀ i : 𝒰.I₀,
                RingHom.IsPseudoCoherentRingMap
                  ((𝒰.f i ≫ 𝒱.openCover.pullbackHom f j).appTop).hom,
        ∀ {V : S.Opens}, IsAffineOpen V →
          ∀ {U : X.Opens}, IsAffineOpen U →
            ∀ e : U ≤ f ⁻¹ᵁ V,
              RingHom.IsPseudoCoherentRingMap (f.appLE V U e).hom,
        ∃ h_finiteType : LocallyOfFiniteType f,
          @Scheme.Modules.IsPseudoCoherentOver X S
            (SheafOfModules.unit X.ringCatSheaf : X.Modules) f h_finiteType
      ])
