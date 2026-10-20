module

public import Mathlib.AlgebraicGeometry.Sites.Etale
public import Mathlib.CategoryTheory.Sites.Over
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FiniteType.Point
public import ReasLib.AlgebraicGeometry.AlgebraicStack.Basic
public import ReasLib.AlgebraicGeometry.GroupoidsOver.BoundedFiniteTypeFibers
public import ReasLib.AlgebraicGeometry.GroupoidsOver.RimSchlessinger
public import ReasLib.AlgebraicGeometry.GroupoidsOver.FormalObject.Effective
public import ReasLib.AlgebraicGeometry.GroupoidsOver.LimitPreserving
public import ReasLib.AlgebraicGeometry.GroupoidsOver.OpennessOfVersality
public import ReasLib.AlgebraicGeometry.GroupoidsOver.FiniteDimensionalPredeformations
public import ReasLib.RingTheory.Regular.GRing

@[expose] public section

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.Groupoids
open AlgebraicGeometry.GroupoidsOver
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicStack

/-- A category fibred in groupoids over a locally Noetherian scheme is an
algebraic stack if it has a representable diagonal, uniformly bounded finite-type
field fibres, étale descent, limit preservation, the Rim-Schlessinger condition,
finite-dimensional tangent and infinitesimal automorphism spaces, effective
formal objects, openness of versality, and G-ring stalks at finite-type points. -/
theorem of_representableDiagonal {S : Scheme.{u}} [IsLocallyNoetherian S]
    {X : GroupoidsOver S}
    [IsStack.InGroupoids (Scheme.etaleTopology.over S) X.p]
    [LimitPreserving X] [HasRimSchlessinger X]
    [HasFiniteDimensionalPredeformations X] [OpennessOfVersality X]
    [HasBoundedFiniteTypeFibers X]
    (h_diag :
      relativelyRepresentableByAlgebraicSpaces
        (FiberedCategoryOver.Groupoids.diagonal.{u + 1, u, u + 1} X))
    (h_eff : ∀ ξ : FormalObject X, FormalObject.IsEffective ξ)
    (hG : ∀ s : S, IsFiniteTypePoint s → IsGRing (S.presheaf.stalk s)) :
    AlgebraicStack X :=
  sorry

/-- A category fibred in groupoids over a locally Noetherian scheme is an
algebraic stack if its second diagonal is representable by algebraic spaces,
its finite-type field fibres are uniformly bounded, it satisfies étale descent,
limit preservation, the Rim-Schlessinger condition, finite-dimensional tangent
and infinitesimal automorphism spaces, equivalence of the approximation functor,
openness of versality for itself and its diagonal, and G-ring stalks at
finite-type points of the base. -/
theorem of_representableSecondDiagonal {S : Scheme.{u}} [IsLocallyNoetherian S]
    {X : GroupoidsOver S}
    [IsStack.InGroupoids (Scheme.etaleTopology.over S) X.p]
    [LimitPreserving X] [HasRimSchlessinger X]
    [HasFiniteDimensionalPredeformations X]
    [(approximation X).IsEquivalence]
    [GroupoidsOver.OpennessOfVersality X]
    [Groupoids.Hom.OpennessOfVersality
      (FiberedCategoryOver.Groupoids.diagonal.{u + 1, u, u + 1} X)]
    [HasBoundedFiniteTypeFibers X]
    (h_diag :
      relativelyRepresentableByAlgebraicSpaces
        (FiberedCategoryOver.Groupoids.Hom.diagonal.{u + 1, u, u + 1}
          (FiberedCategoryOver.Groupoids.diagonal.{u + 1, u, u + 1} X)))
    (hG : ∀ s : S, IsFiniteTypePoint s → IsGRing (S.presheaf.stalk s)) :
    AlgebraicStack X :=
  sorry

end AlgebraicGeometry.AlgebraicStack
