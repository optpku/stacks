module

public import ReasLib.AlgebraicGeometry.Scheme.Module.WeaklyAssociatedPoints.Relative.Pushforward
import StacksCheckRecall

@[expose] public section

open CategoryTheory

universe u

/- Lemma 31.8.3: for a finite morphism `i : Z ⟶ X`, pushforward carries the relative weak
assassin of a quasicoherent module over `Z/S` exactly to its image in `X`. -/
@[stacks 0CUD] #check
  (AlgebraicGeometry.Scheme.Modules.relativeWeakAss_pushforward_eq_image_of_isFinite :
    ∀ {X Z S : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ S) (i : Z ⟶ X)
      [AlgebraicGeometry.IsFinite i] (ℱ : Z.Modules) [ℱ.IsQuasicoherent],
      AlgebraicGeometry.Scheme.Modules.relativeWeakAss f
          ((AlgebraicGeometry.Scheme.Modules.pushforward i).obj ℱ) =
        i.base '' AlgebraicGeometry.Scheme.Modules.relativeWeakAss (i ≫ f) ℱ)
