module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.Immersion.Noetherian
import StacksCheckRecall

/-!
# Immersions into (locally) Noetherian algebraic stacks

An immersion of algebraic stacks into a locally Noetherian algebraic stack has
locally Noetherian source and is quasi-compact. If the target is Noetherian,
the source is Noetherian.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open Groupoids.Hom (Immersion)
open scoped Bicategory

universe u

namespace AlgebraicGeometry.AlgebraicStack

/- Lemma 101.8.2 (1): an immersion of algebraic stacks into a locally
Noetherian algebraic stack has locally Noetherian source. -/
@[stacks 0CPM] #check
  (AlgebraicGeometry.AlgebraicStack.IsLocallyNoetherian.of_immersion :
    ∀ {S : Scheme.{u}} {X Y : GroupoidsOver S}
      [AlgebraicStack X] [AlgebraicStack Y] (j : X ⟶ Y) [Immersion j]
      [IsLocallyNoetherian Y], IsLocallyNoetherian X)

/- Lemma 101.8.2 (2): an immersion of algebraic stacks into a locally
Noetherian algebraic stack is quasi-compact. -/
@[stacks 0CPM] #check
  (AlgebraicGeometry.AlgebraicStack.QuasiCompact.of_immersion :
    ∀ {S : Scheme.{u}} {X Y : GroupoidsOver S}
      [AlgebraicStack X] [AlgebraicStack Y] (j : X ⟶ Y) [Immersion j]
      [IsLocallyNoetherian Y], QuasiCompact j)

/- Lemma 101.8.2 (3): an immersion of algebraic stacks into a Noetherian
algebraic stack has Noetherian source. -/
@[stacks 0CPM] #check
  (AlgebraicGeometry.AlgebraicStack.IsNoetherian.of_immersion :
    ∀ {S : Scheme.{u}} {X Y : GroupoidsOver S}
      [AlgebraicStack X] [AlgebraicStack Y] (j : X ⟶ Y) [Immersion j]
      [IsNoetherian Y], IsNoetherian X)

end AlgebraicGeometry.AlgebraicStack
