module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Cohomology.AmpleCriterion
import StacksCheckRecall

/-!
# Lemma 69.21.1

A cohomological criterion for ampleness of an invertible sheaf on a proper algebraic
space over a Noetherian ring.
-/

@[expose]
public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory

noncomputable section

universe u

/- Lemma 69.21.1: let `R` be a Noetherian ring, let `X` be a proper algebraic space over
`R`, and let `L` be an invertible `𝒪_X`-module. The following are equivalent: `X` is a
scheme and `L` is ample on `X`; for every coherent `𝒪_X`-module `F` there exists `n₀ ≥ 0`
such that `H^p(X, F ⊗ L^{⊗ n}) = 0` for all `n ≥ n₀` and `p > 0`; and for every coherent
`𝒪_X`-module `F` there exists `n ≥ 1` such that `H¹(X, F ⊗ L^{⊗ n}) = 0`. -/
@[stacks 0GFA] #check (AlgebraicGeometry.AlgebraicSpace.isSchemeAndAmple_tfae :
    ∀ {R : Type u} [CommRing R] [IsNoetherianRing R]
    {X : AlgebraicSpace (Spec (CommRingCat.of R))}
    (f : X ⟶ ofOver (Over.mk (𝟙 (Spec (CommRingCat.of R))))) [Proper f]
    [HasSheafify (smallEtaleTopology X) AddCommGrpCat.{u}]
    [HasExt.{u} (Sheaf (smallEtaleTopology X) AddCommGrpCat.{u})]
    (L : X.Modules) [isInvertibleObject L],
    List.TFAE
      [ Modules.isSchemeAndAmple L,
        ∀ F : X.Modules, F.IsCoherent →
          ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n → ∀ p : ℕ, 0 < p →
            IsZero (cohomology X (F ⊗ tensorPower L n) p),
        ∀ F : X.Modules, F.IsCoherent →
          ∃ n : ℕ, 0 < n ∧
            IsZero (cohomology X (F ⊗ tensorPower L n) 1) ])
