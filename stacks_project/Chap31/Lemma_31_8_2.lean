module

public import ReasLib.AlgebraicGeometry.Scheme.Module.WeaklyAssociatedPoints.Relative.FiniteType
import StacksCheckRecall

@[expose] public section

universe u

/- Lemma 31.8.2: for a locally finite type morphism of schemes, the relative weak assassin of a
quasicoherent module equals its relative assassin. -/
@[stacks 05F2] #check
  (AlgebraicGeometry.Scheme.Modules.relativeWeakAss_eq_relativeAssassin_of_locallyOfFiniteType :
    ∀ {X S : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ S)
      [AlgebraicGeometry.LocallyOfFiniteType f] (ℱ : X.Modules) [ℱ.IsQuasicoherent],
      AlgebraicGeometry.Scheme.Modules.relativeWeakAss f ℱ =
        AlgebraicGeometry.Scheme.Modules.relativeAssassin f ℱ)
