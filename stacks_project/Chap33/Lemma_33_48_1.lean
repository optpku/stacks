module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Ample.NegativeCohomology
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry
open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.MonoidalCategory
open scoped AlgebraicGeometry

universe u

/- Lemma 33.48.1: if the associated points of a coherent module on a scheme proper over a
field contain no closed points, then the module has no global sections after every sufficiently
negative twist by an ample invertible module. -/
@[stacks 0FD7] #check
  (AlgebraicGeometry.Scheme.Modules.IsAmple.twistZeroCohomology_eventually_isZero :
    ∀ {k : Type u} [Field k] {X : Scheme.{u}}
      (f : X ⟶ Spec (CommRingCat.of k)) [IsProper f]
      (L F : X.Modules) [L.Invertible] [Scheme.Modules.IsAmple L] [F.IsCoherent],
      Disjoint (Scheme.Modules.associatedPoints F) (closedPoints X) →
        ∃ b : ℤ, ∀ d : ℤ, d ≤ b →
          IsZero (Scheme.Hom.cohomology f (F ⊗ L ^⊗ d) 0))
