module

public import ReasLib.AlgebraicGeometry.Scheme.Normal.Nagata.Noetherian
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 28.13.3

The locally Noetherian consequence of the neutral `Scheme.Nagata` owner lives
in `ReasLib.AlgebraicGeometry.Scheme.Normal.Nagata.Noetherian`.
-/

universe u

/- Lemma 28.13.3: A Nagata scheme is locally Noetherian. -/
@[stacks 033U]
#check (AlgebraicGeometry.Scheme.isLocallyNoetherian_of_nagata :
  ∀ (X : AlgebraicGeometry.Scheme.{u}), AlgebraicGeometry.Scheme.Nagata X →
    AlgebraicGeometry.IsLocallyNoetherian X)
