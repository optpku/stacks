module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Picard.Norm
import StacksCheckRecall

/-!
# Lemma 31.17.2

The norm homomorphism on Picard groups of schemes.

@stack 0BCY
-/

@[expose] public section

universe u

#check @AlgebraicGeometry.Scheme.normPullbackSectionAlgebra
#check @AlgebraicGeometry.Scheme.FiniteMorphismNorm
#check @AlgebraicGeometry.Scheme.IsFiniteMorphismNorm

/- Lemma 31.17.2: A degree-`d` norm for a finite morphism induces a norm
homomorphism on Picard groups, compatible with pullback and `d`-fold tensor power. -/
@[stacks 0BCY] #check
  (AlgebraicGeometry.Scheme.exists_picardNorm_of_exists_norm :
    ∀ {X Y : AlgebraicGeometry.Scheme.{u}} (π : X ⟶ Y) (d : ℕ)
      [AlgebraicGeometry.IsFinite π],
      (∃ N : AlgebraicGeometry.Scheme.FiniteMorphismNorm π,
        AlgebraicGeometry.Scheme.IsFiniteMorphismNorm π d N) →
      ∃ normπ : X.PicardGroup →+ Y.PicardGroup,
        ∀ (𝒩 : Y.Modules)
          [CategoryTheory.MonoidalCategory.isInvertibleObject 𝒩],
          normπ (AlgebraicGeometry.Scheme.Hom.picardPullbackClass π 𝒩) =
            d • AlgebraicGeometry.Scheme.Modules.picardClass 𝒩)
