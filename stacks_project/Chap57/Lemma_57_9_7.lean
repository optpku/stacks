module

public import ReasLib.AlgebraicGeometry.Scheme.OverField.PerfectDerived.StrongGenerator
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory
universe u

/- Lemma 57.9.7: The perfect derived category of a scheme proper and smooth over a
field has a strong triangulated generator. -/
@[stacks 0FZ6] #check
  (AlgebraicGeometry.SchemeOverField.PerfectDerived.existsStrongTriangulatedGenerator :
    ∀ {k : Type u} [Field k] (X : SchemeOverField k) [IsProper X.hom] [Smooth X.hom],
      ∃ E : SchemeOverField.PerfectDerived X,
        (CategoryTheory.ObjectProperty.singleton E).IsStrongTriangulatedGenerator)
