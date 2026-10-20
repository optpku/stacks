module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.Thickening.Properties
import StacksCheckRecall

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.AlgebraicStack
open scoped Bicategory

universe u

/- Lemma 106.3.9 (1): a thickening of algebraic stacks is an algebraic space if
and only if the target is an algebraic space. -/
@[stacks 0BPW] #check
  (AlgebraicGeometry.AlgebraicStack.IsThickening.isRepresentableByAlgebraicSpace_iff :
    ∀ {S : Scheme.{u}} {X X' : GroupoidsOver S}
      [AlgebraicStack X] [AlgebraicStack X'] (i : X ⟶ X') [IsThickening i],
      IsRepresentableByAlgebraicSpace X ↔ IsRepresentableByAlgebraicSpace X')

/- Lemma 106.3.9 (2): a thickening of algebraic stacks is a scheme if and only
if the target is a scheme. -/
@[stacks 0BPW] #check
  (AlgebraicGeometry.AlgebraicStack.IsThickening.isScheme_iff :
    ∀ {S : Scheme.{u}} {X X' : GroupoidsOver S}
      [AlgebraicStack X] [AlgebraicStack X'] (i : X ⟶ X') [IsThickening i],
      (∃ F : AlgebraicSpace S, AlgebraicSpace.IsScheme F ∧ Nonempty (X ≌ F.toGroupoids)) ↔
        (∃ F : AlgebraicSpace S, AlgebraicSpace.IsScheme F ∧ Nonempty (X' ≌ F.toGroupoids)))

/- Lemma 106.3.9 (3): a thickening of algebraic stacks is DM if and only if the
target is DM. -/
@[stacks 0BPW] #check
  (AlgebraicGeometry.AlgebraicStack.IsThickening.isDM_iff :
    ∀ {S : Scheme.{u}} {X X' : GroupoidsOver S}
      [AlgebraicStack X] [AlgebraicStack X'] (i : X ⟶ X') [IsThickening i],
      IsDM X ↔ IsDM X')

/- Lemma 106.3.9 (4): a thickening of algebraic stacks is quasi-DM if and only
if the target is quasi-DM. -/
@[stacks 0BPW] #check
  (AlgebraicGeometry.AlgebraicStack.IsThickening.isQuasiDM_iff :
    ∀ {S : Scheme.{u}} {X X' : GroupoidsOver S}
      [AlgebraicStack X] [AlgebraicStack X'] (i : X ⟶ X') [IsThickening i],
      IsQuasiDM X ↔ IsQuasiDM X')

/- Lemma 106.3.9 (5): a thickening of algebraic stacks is separated if and only
if the target is separated. -/
@[stacks 0BPW] #check
  (AlgebraicGeometry.AlgebraicStack.IsThickening.isSeparated_iff :
    ∀ {S : Scheme.{u}} {X X' : GroupoidsOver S}
      [AlgebraicStack X] [AlgebraicStack X'] (i : X ⟶ X') [IsThickening i],
      IsSeparated X ↔ IsSeparated X')

/- Lemma 106.3.9 (6): a thickening of algebraic stacks is quasi-separated if and
only if the target is quasi-separated. -/
@[stacks 0BPW] #check
  (AlgebraicGeometry.AlgebraicStack.IsThickening.isQuasiSeparated_iff :
    ∀ {S : Scheme.{u}} {X X' : GroupoidsOver S}
      [AlgebraicStack X] [AlgebraicStack X'] (i : X ⟶ X') [IsThickening i],
      IsQuasiSeparated X ↔ IsQuasiSeparated X')
