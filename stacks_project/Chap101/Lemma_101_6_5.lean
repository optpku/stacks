module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.Separation.Diagonals
import StacksCheckRecall

/-!
# First and second diagonals of separation axioms

A morphism of algebraic stacks is separated, quasi-separated, quasi-DM, or DM
if and only if both its first diagonal `Hom.diagonal f` and its second
diagonal `Hom.diagonal (Hom.diagonal f)` are universally closed, quasi-compact,
locally quasi-finite, or unramified, respectively, on scheme-slice tests.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open FiberedCategoryOver.Groupoids
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicStack

namespace Separated

/- Lemma 101.6.5 (1): a morphism `f : X ⟶ Y` of algebraic stacks is
separated if and only if the first diagonal `Hom.diagonal f` and the second
diagonal `Hom.diagonal (Hom.diagonal f)` are universally closed. -/
@[stacks 04Z0] #check (AlgebraicGeometry.AlgebraicStack.Separated.iff_diagonals_universallyClosed :
    ∀ {S : Scheme.{u}}
    {X Y : GroupoidsOver S} [AlgebraicStack X] [AlgebraicStack Y]
    (f : X ⟶ Y),
    Separated f ↔
      Groupoids.Hom.has (@AlgebraicSpace.UniversallyClosed S)
          (Hom.diagonal.{u + 1, u, u + 1} f) ∧
        Groupoids.Hom.has (@AlgebraicSpace.UniversallyClosed S)
          (Hom.diagonal.{u + 1, u, u + 1} (Hom.diagonal.{u + 1, u, u + 1} f)))

end Separated

namespace QuasiSeparated

/- Lemma 101.6.5 (2): a morphism `f : X ⟶ Y` of algebraic stacks is
quasi-separated if and only if the first diagonal `Hom.diagonal f` and the
second diagonal `Hom.diagonal (Hom.diagonal f)` are quasi-compact. -/
@[stacks 04Z0] #check (AlgebraicGeometry.AlgebraicStack.QuasiSeparated.iff_diagonals_quasiCompact :
    ∀ {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y),
    QuasiSeparated f ↔
      Groupoids.Hom.has (@AlgebraicSpace.QuasiCompact S)
          (Hom.diagonal.{u + 1, u, u + 1} f) ∧
        Groupoids.Hom.has (@AlgebraicSpace.QuasiCompact S)
          (Hom.diagonal.{u + 1, u, u + 1} (Hom.diagonal.{u + 1, u, u + 1} f)))

end QuasiSeparated

namespace QuasiDM

/- Lemma 101.6.5 (3): a morphism `f : X ⟶ Y` of algebraic stacks is
quasi-DM if and only if the first diagonal `Hom.diagonal f` and the second
diagonal `Hom.diagonal (Hom.diagonal f)` are locally quasi-finite. -/
@[stacks 04Z0] #check (AlgebraicGeometry.AlgebraicStack.QuasiDM.iff_diagonals_locallyQuasiFinite :
    ∀ {S : Scheme.{u}}
    {X Y : GroupoidsOver S} [AlgebraicStack X] [AlgebraicStack Y]
    (f : X ⟶ Y),
    QuasiDM f ↔
      Groupoids.Hom.has (@AlgebraicSpace.LocallyQuasiFinite S)
          (Hom.diagonal.{u + 1, u, u + 1} f) ∧
        Groupoids.Hom.has (@AlgebraicSpace.LocallyQuasiFinite S)
          (Hom.diagonal.{u + 1, u, u + 1} (Hom.diagonal.{u + 1, u, u + 1} f)))

end QuasiDM

namespace DM

/- Lemma 101.6.5 (4): a morphism `f : X ⟶ Y` of algebraic stacks is DM if
and only if the first diagonal `Hom.diagonal f` and the second diagonal
`Hom.diagonal (Hom.diagonal f)` are unramified. -/
@[stacks 04Z0] #check (AlgebraicGeometry.AlgebraicStack.DM.iff_diagonals_unramified :
    ∀ {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y),
    DM f ↔
      Groupoids.Hom.has (@AlgebraicSpace.Unramified S)
          (Hom.diagonal.{u + 1, u, u + 1} f) ∧
        Groupoids.Hom.has (@AlgebraicSpace.Unramified S)
          (Hom.diagonal.{u + 1, u, u + 1} (Hom.diagonal.{u + 1, u, u + 1} f)))

end DM

end AlgebraicGeometry.AlgebraicStack
