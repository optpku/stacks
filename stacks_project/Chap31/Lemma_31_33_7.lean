module

public import ReasLib.AlgebraicGeometry.Scheme.StrictTransform.Exact
import StacksCheckRecall

universe u

/- Lemma 31.33.7: if a quasicoherent short complex remains short exact after every base change,
then its strict transform along a blowup is short exact. -/
@[stacks 080W] #check
  (AlgebraicGeometry.Scheme.Modules.strictTransform_shortExact_of_forall_pullback_shortExact :
    ∀ {S S' X : AlgebraicGeometry.Scheme.{u}}
      (I : S.IdealSheafData) (b : S' ⟶ S) [AlgebraicGeometry.IsBlowup b I]
      (f : X ⟶ S) (S₀ : CategoryTheory.ShortComplex X.Modules)
      [S₀.X₁.IsQuasicoherent] [S₀.X₂.IsQuasicoherent] [S₀.X₃.IsQuasicoherent],
      (∀ {T : AlgebraicGeometry.Scheme.{u}} (t : T ⟶ S),
        (S₀.map (AlgebraicGeometry.Scheme.Modules.pullback
          (CategoryTheory.Limits.pullback.fst f t))).ShortExact) →
      (S₀.map (AlgebraicGeometry.strictTransformFunctor b (I.comap b) f)).ShortExact)
