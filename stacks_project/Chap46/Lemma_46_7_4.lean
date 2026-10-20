module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Module.Adequacy.Derived
import StacksCheckRecall

@[expose] public section

open CategoryTheory CategoryTheory.Functor.RightDerived CategoryTheory.Limits
open AlgebraicGeometry Opposite

universe u

namespace SheafOfModules.AffineAdeq

/- Lemma 46.7.4 -/
@[stacks 06ZU] #check
  (SheafOfModules.AffineAdeq.coreflectorRightDerivedIsZero :
    ∀ (τ : StandardTopology) (A : CommRingCat.{u}) (ℱ : SheafOfModules.AffineAdeq τ A)
      [HasInjectiveResolutions (ambientModuleCat τ A)] (p : ℕ), 0 < p →
        IsZero (((coreflector τ A).rightDerived p).obj ((inclusion τ A).obj ℱ)))

#check
  (coreflectorVanishesAboveZero :
    ∀ (τ : StandardTopology) (A : CommRingCat.{u}) (ℱ : SheafOfModules.AffineAdeq τ A)
      [HasInjectiveResolutions (ambientModuleCat τ A)],
      Vanishes.aboveZero (coreflector τ A) ((inclusion τ A).obj ℱ))

end SheafOfModules.AffineAdeq
