module

public import ReasLib.AlgebraicGeometry.GroupoidsOver.VersalAt
public import ReasLib.AlgebraicGeometry.GroupoidsOver.Representable
public import ReasLib.AlgebraicGeometry.GroupoidsOver.LimitPreserving
public import ReasLib.AlgebraicGeometry.GroupoidsOver.StrongRimSchlessinger
public import ReasLib.CategoryTheory.Fibered.Groupoids.Diagonal.Construction
import Mathlib.Tactic.CrossRefAttribute

/-!
# Versality under generalization

Versality is stable under generalization between finite type points for a
limit-preserving category fibred in groupoids with representable diagonal
and the strong Rim-Schlessinger property over a locally Noetherian base.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

universe u

namespace AlgebraicGeometry.GroupoidsOver

/-- Over a locally Noetherian scheme, let a category fibred in groupoids have
diagonal representable by algebraic spaces, satisfy the strong Rim-Schlessinger
condition, and be limit preserving. An object over a finite type scheme that is
versal at a finite type point is versal at every finite type generalization of
that point. -/
@[stacks 0G2K]
theorem isVersalAt_of_specializes {S : Scheme.{u}} [IsLocallyNoetherian S]
    {X : GroupoidsOver S} [HasStrongRimSchlessinger X]
    [Groupoids.LimitPreserving X]
    (h_diag : relativelyRepresentableByAlgebraicSpaces
      (FiberedCategoryOver.Groupoids.diagonal.{u + 1, u, u + 1} X))
    {U : Scheme.{u}} (hU : U ⟶ S) [Scheme.Hom.FiniteType hU]
    (x : X.total) (hx : X.p.obj x = Over.mk hU) {u u0 : U}
    [IsFiniteTypePoint u] [IsFiniteTypePoint u0]
    (h_specializes : Specializes u u0) (h_versal : IsVersalAt hU x hx u0) :
    IsVersalAt hU x hx u :=
  sorry

end AlgebraicGeometry.GroupoidsOver
