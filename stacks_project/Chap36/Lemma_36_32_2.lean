module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Pushforward.FiberEulerCharacteristic

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules

/- Lemma 36.32.2 (1): for a proper finitely presented morphism and a finitely presented
module sheaf flat over the base, the fiber Euler-characteristic function is locally constant. -/
@[stacks 0B9T] #check
  (AlgebraicGeometry.Scheme.Modules.relativeEulerChar_isLocallyConstant :
    ∀ {X S : Scheme.{u}} (f : X ⟶ S)
      [IsProper f] [Scheme.Hom.FinitePresentation f]
      (ℱ : X.Modules) [ℱ.IsFinitePresentation]
      [SheafOfModules.IsFlatOver ℱ f.toShHom],
      IsLocallyConstant (relativeEulerChar f ℱ))

/- Lemma 36.32.2 (2): formation of the fiber Euler-characteristic function commutes
with arbitrary base change. -/
@[stacks 0B9T] #check
  (AlgebraicGeometry.Scheme.Modules.relativeEulerChar_baseChange :
    ∀ {X' X S' S : Scheme.{u}}
      (g' : X' ⟶ X) (f' : X' ⟶ S') (f : X ⟶ S) (g : S' ⟶ S)
      [IsProper f] [Scheme.Hom.FinitePresentation f]
      (ℱ : X.Modules) [ℱ.IsFinitePresentation]
      [SheafOfModules.IsFlatOver ℱ f.toShHom]
      (sq : IsPullback g' f' f g),
      relativeEulerChar f' ((Scheme.Modules.pullback g').obj ℱ) =
        fun s' : S' ↦ relativeEulerChar f ℱ (g s'))

end AlgebraicGeometry.Scheme.Modules
