module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.ClosedImmersion.Lifting
import StacksCheckRecall

@[expose] public section

open CategoryTheory

universe u

/- Lemma 37.81.4: a quasi-compact scheme morphism is a closed immersion exactly when
it has the right lifting property against `Spec.map φ : Spec B ⟶ Spec A` for every
injective commutative-ring morphism `φ : A ⟶ B`. -/
@[stacks 0H2S] #check
  (AlgebraicGeometry.IsClosedImmersion.iff_hasLiftingProperty_spec_injective_of_quasiCompact :
    ∀ {X Y : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ Y)
      [AlgebraicGeometry.QuasiCompact f],
      AlgebraicGeometry.IsClosedImmersion f ↔
        ∀ {A B : CommRingCat.{u}} (φ : A ⟶ B), Function.Injective φ →
          HasLiftingProperty (AlgebraicGeometry.Spec.map φ) f)
