module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Birational.Dominant
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry

universe u

/- Lemma 29.50.2: a birational morphism between schemes with finitely many irreducible
components is dominant. -/
@[stacks 01RP] #check
  (AlgebraicGeometry.instIsDominantOfIsBirational :
    ∀ {X Y : Scheme.{u}} [Finite (irreducibleComponents X)]
      [Finite (irreducibleComponents Y)] (f : X ⟶ Y) [IsBirational f], IsDominant f)
