module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Dualizing.BaseChange
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

/-
Lemma 48.26.1
-/
@[stacks 0E4N] #check (AlgebraicGeometry.Scheme.IsDualizingComplex.iff_pullback :
  {X Y : Scheme.{u}} → (f : X ⟶ Y) →
    [IsLocallyNoetherian X] → [IsLocallyNoetherian Y] → [Surjective f] →
    (Syntomic f ∨
      (Flat f ∧ LocallyOfType RingHom.IsLocalCompleteIntersection f) ∨
      (AlgebraicGeometry.Gorenstein f ∧ Scheme.Hom.FiniteType f)) →
    (K : Scheme.DerivedQCoh Y) →
      Scheme.IsDualizingComplex K.obj ↔
        Scheme.IsDualizingComplex ((Scheme.DerivedQCoh.pullback f).obj K).obj)
