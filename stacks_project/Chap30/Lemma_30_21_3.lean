module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Ample.FiberCohomology
import StacksCheckRecall

/-!
# Ampleness on a fibre and stalks of twisted higher direct images

For a proper morphism to a Noetherian scheme, an invertible module that is ample
on one scheme-theoretic fibre yields eventual vanishing of positive-degree
higher-direct-image stalks and surjectivity of the canonical map to fibre
cohomology after twisting.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.ConcreteCategory CategoryTheory.Limits
open CategoryTheory.MonoidalCategory
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Hom

/- Lemma 30.21.3: let `f : X ⟶ Y` be a proper morphism of schemes with `Y` Noetherian,
let `L` be an invertible `𝒪_X`-module, let `F` be a coherent `𝒪_X`-module, and let
`y` be a point of `Y` such that the pullback of `L` to the scheme-theoretic fibre `X_y`
is ample. Then there exists `d0 : ℕ` such that for every `d ≥ d0`, the stalk
`(R^p f_*(F ⊗ L ^⊗ d))_y` is zero for all `p > 0`, and the canonical map
`(f_*(F ⊗ L ^⊗ d))_y ⟶ H^0(X_y, F_y ⊗ L_y ^⊗ d)` is surjective. -/
@[stacks 0D2M]
#check (AlgebraicGeometry.Scheme.Hom.exists_twist_bound_of_isAmple_fiber :
    ∀ {X Y : Scheme.{u}} (f : X ⟶ Y) [IsNoetherian Y] [IsProper f]
      (L : X.Modules) [L.Invertible] (F : X.Modules) [F.IsCoherent] (y : Y)
      [Scheme.Modules.IsAmple ((Scheme.Modules.pullback (f.fiberι y)).obj L)],
    ∃ d0 : ℕ, ∀ d : ℕ, d0 ≤ d →
      (∀ p : ℕ, 0 < p →
          IsZero (RingedSpace.stalkModuleCat
            (RingedSpace.Hom.higherDirectImageModule f.toShHom (F ⊗ L ^⊗ (d : ℤ)) p) y)) ∧
        Function.Surjective (stalkToFiberSections f (F ⊗ L ^⊗ (d : ℤ)) y).hom)

end AlgebraicGeometry.Scheme.Hom
