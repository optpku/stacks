module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.FormalGlueing
import StacksCheckRecall

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace CategoryTheory

universe u

/- Lemma 81.10.5: For a morphism which is an isomorphism over a closed subspace
and flat along its inverse image, the canonical derived pullback-pushforward
counit is invertible on quasi-coherent complexes supported on that inverse image. -/
@[stacks 0AEU] #check
  (AlgebraicGeometry.AlgebraicSpace.DerivedQCoh.derivedPullback_pushforward_counit_isIso :
    ∀ {S : Scheme.{u}} {X Y Z : AlgebraicSpace S} (f : Y ⟶ X) (i : Z ⟶ X)
      [IsClosedImmersion i] [IsIso (inverseImageTo f i)]
      (hf : ∀ x : Points Y, x ∈ pointsImage (inverseImageι f i) → FlatAt f x)
      (Q : DerivedQCoh Y)
      (hQ : ModuleDerived.IsSupportedOn Q.obj (pointsImage (inverseImageι f i))),
      IsIso ((Modules.derivedPullbackPushforwardAdjunction f).counit.app Q.obj))
