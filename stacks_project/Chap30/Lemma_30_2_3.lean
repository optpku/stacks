module

public import ReasLib.AlgebraicGeometry.Scheme.HigherDirectImage.Affine
import StacksCheckRecall

universe u

/- Lemma 30.2.3: let `f : X ⟶ S` be an affine morphism of schemes and let `ℱ` be a
quasi-coherent `𝒪_X`-module. Then `R^i f_* ℱ = 0` for every `i > 0`. -/
@[stacks 01XC] #check
  (AlgebraicGeometry.Scheme.higherDirectImageModule_isZero_of_isAffineHom :
    ∀ {X S : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ S) [AlgebraicGeometry.IsAffineHom f]
      [CategoryTheory.HasInjectiveResolutions X.Modules]
      (ℱ : X.Modules) [ℱ.IsQuasicoherent] (i : ℕ), 0 < i →
        CategoryTheory.Limits.IsZero
          (((AlgebraicGeometry.Scheme.Modules.pushforward f).rightDerived i).obj ℱ))
