module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Groupoid.Inertia.Comparison
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Groupoid.Inertia.Presentation
import StacksCheckRecall

/-!
# Inertia and quotient stacks

The stabilizer-conjugation groupoid presents the inertia stack of a groupoid quotient.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicSpace GroupoidAlgebraicSpace

universe u

/- Lemma 78.26.1. The stabilizer-conjugation groupoid with arrows
`R ×_{s,U} G`, source `(r,g) ↦ g`, and target `(r,g) ↦ c(r,c(g,i(r)))`
presents the inertia stack of the quotient stack `[U/R]`. -/
@[stacks 06PB] #check
  (AlgebraicGeometry.GroupoidAlgebraicSpace.inertia_quotientStack :
    ∀ {S : Scheme.{u}} {B : AlgebraicSpace S} (G : GroupoidAlgebraicSpace B),
      ∃ F : CartesianBasedFunctor (StackOver.Groupoids.inertia (fppfQuotientStack G)).p
        (fppfQuotientStack (inertiaPresentation G)).p,
        F.toBasedFunctor.IsEquivalence)

#check (AlgebraicGeometry.GroupoidAlgebraicSpace.inertiaPresentation :
  ∀ {S : Scheme.{u}} {B : AlgebraicSpace S},
    GroupoidAlgebraicSpace B → GroupoidAlgebraicSpace B)
