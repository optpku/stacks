module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Ample.Family.CompletelyDecomposed
import StacksCheckRecall

open CategoryTheory

universe u

/- Proposition 37.80.3: every quasi-compact, quasi-separated scheme admits a finitely
presented, proper, completely decomposed morphism from a scheme with an ample family of
invertible modules. -/
@[stacks 0GTU] #check
  (AlgebraicGeometry.Scheme.Modules.AmpleFamily.exists_proper_completelyDecomposed :
    ∀ {X : AlgebraicGeometry.Scheme.{u}} [CompactSpace X] [QuasiSeparatedSpace X],
      ∃ (Y : AlgebraicGeometry.Scheme.{u}) (f : Y ⟶ X)
        (_ : AlgebraicGeometry.Scheme.Hom.FinitePresentation f)
        (_ : AlgebraicGeometry.IsProper f)
        (_ : AlgebraicGeometry.Scheme.Hom.CompletelyDecomposed f)
        (ι : Type u) (L : ι → Y.Modules),
          AlgebraicGeometry.Scheme.Modules.AmpleFamily L)
