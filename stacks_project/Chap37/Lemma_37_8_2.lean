module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FormallyEtale.Lifting
import StacksCheckRecall

@[expose] public section

open CategoryTheory

universe u

/- Lemma 37.8.2: a formally étale morphism admits exactly one lift through every
first-order thickening, without any affineness assumptions on the thickened schemes. -/
@[stacks 04FD]
#check (AlgebraicGeometry.FormallyEtale.existsUnique_lift_firstOrder :
  ∀ {X S T T' : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ S)
    [AlgebraicGeometry.FormallyEtale f]
    (i : T ⟶ T') [AlgebraicGeometry.IsFirstOrderThickening i]
    (g : T ⟶ X) (h : T' ⟶ S) (sq : CommSq g i f h),
    Nonempty (Unique sq.LiftStruct))

/- Formal étaleness is equivalently characterized by unique lifting through arbitrary
first-order thickenings. -/
#check (AlgebraicGeometry.FormallyEtale.iff_existsUnique_lift_firstOrder :
  ∀ {X S : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ S),
    AlgebraicGeometry.FormallyEtale f ↔
      ∀ {T T' : AlgebraicGeometry.Scheme.{u}} (i : T ⟶ T')
        [AlgebraicGeometry.IsFirstOrderThickening i]
        (g : T ⟶ X) (h : T' ⟶ S) (sq : CommSq g i f h),
        Nonempty (Unique sq.LiftStruct))
