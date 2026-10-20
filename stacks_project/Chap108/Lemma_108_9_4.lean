module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Picard.Relative.Separated
import StacksCheckRecall

/-!
# Lemma 108.9.4

If the geometric fibres of `f : X ⟶ B` are integral, in addition to the
standing hypotheses of Stacks 108.9, then the Picard functor `Pic_{X/B}` is
separated over `B`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u

/- Lemma 108.9.4: under the standing hypotheses, integral geometric fibres imply
that the relative Picard sheaf is separated over the base. -/
@[stacks 0DNJ] #check (AlgebraicGeometry.AlgebraicSpace.RelativePicard.separated :
  ∀ {S : Scheme.{u}} {X B : AlgebraicSpace S} (f : X ⟶ B),
    [Flat f] → [Proper f] → [FinitePresentation f] →
    [Hom.IsIsoBaseChangeStructurePushforward f] → [Hom.HasIntegralGeometricFibres f] →
      SchemeOver.IsClosedImmersion (CategoryTheory.Limits.diag (picardFunctor f).obj))
