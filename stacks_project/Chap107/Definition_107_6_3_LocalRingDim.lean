module

public import stacks_project.Chap107.Lemma_107_6_2_SmoothChart

/-!
# Dimension of the local ring of an algebraic stack

For a finite type point of a locally Noetherian algebraic stack, the
local-ring dimension is the common value of
`SmoothSchemeChart.localRingDimDiff` along smooth scheme neighbourhoods.
-/

@[expose]
public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicStack

/-- The dimension of the local ring of a locally Noetherian algebraic stack at a
finite type point, as the supremum of `SmoothSchemeChart.localRingDimDiff`
along smooth scheme neighbourhoods of that point. -/
noncomputable def localRingDimAt {S : Scheme.{u}} {X : GroupoidsOver S}
    [AlgebraicStack X] [IsLocallyNoetherian X] (x : Points X)
    (hx : IsFiniteTypePoint x) : EInt :=
  let _ := hx
  ⨆ c : SmoothSchemeChart x, c.localRingDimDiff

/-- Unfolding of `localRingDimAt` as a supremum of chart differences. -/
theorem localRingDimAt_def {S : Scheme.{u}} {X : GroupoidsOver S}
    [AlgebraicStack X] [IsLocallyNoetherian X] (x : Points X)
    (hx : IsFiniteTypePoint x) :
    localRingDimAt x hx = ⨆ c : SmoothSchemeChart x, c.localRingDimDiff :=
  sorry

/-- The local-ring dimension at a finite type point equals the local-ring
dimension difference of any smooth scheme neighbourhood of that point. -/
theorem localRingDimAt_eq {S : Scheme.{u}} {X : GroupoidsOver S}
    [AlgebraicStack X] [IsLocallyNoetherian X] {x : Points X}
    (hx : IsFiniteTypePoint x) (c : SmoothSchemeChart x) :
    localRingDimAt x hx = c.localRingDimDiff :=
  sorry

/-- The local-ring dimension at a finite type point equals `d` if and only if
some smooth scheme neighbourhood has local-ring dimension difference `d`. -/
theorem localRingDimAt_iff {S : Scheme.{u}} {X : GroupoidsOver S}
    [AlgebraicStack X] [IsLocallyNoetherian X] {x : Points X}
    (hx : IsFiniteTypePoint x) (d : ℤ) :
    localRingDimAt x hx = d ↔
      ∃ c : SmoothSchemeChart x, c.localRingDimDiff = d :=
  sorry

/-- The local-ring dimension at a finite type point equals `d` if and only if
every smooth scheme neighbourhood has local-ring dimension difference `d`. -/
theorem localRingDimAt_iff_forall {S : Scheme.{u}} {X : GroupoidsOver S}
    [AlgebraicStack X] [IsLocallyNoetherian X] {x : Points X}
    (hx : IsFiniteTypePoint x) (d : ℤ) :
    localRingDimAt x hx = d ↔
      ∀ c : SmoothSchemeChart x, c.localRingDimDiff = d :=
  sorry

/-- The local-ring dimension at a finite type point is an ordinary integer. -/
theorem localRingDimAt_eq_int {S : Scheme.{u}} {X : GroupoidsOver S}
    [AlgebraicStack X] [IsLocallyNoetherian X] {x : Points X}
    (hx : IsFiniteTypePoint x) :
    ∃ n : ℤ, localRingDimAt x hx = n :=
  sorry

/-- Unbundled form of `localRingDimAt_iff`, quantifying over a scheme, a smooth
morphism to `X`, a representing self 2-fibre product, and a finite type point
mapping to `x`. -/
theorem localRingDimAt_unbundled_iff {S : Scheme.{u}} {X : GroupoidsOver S}
    [AlgebraicStack X] [IsLocallyNoetherian X] {x : Points X}
    (hx : IsFiniteTypePoint x) (d : ℤ) :
    localRingDimAt x hx = d ↔
      ∃ (U : Over S) (hom : GroupoidsOver.slice U ⟶ X) (R : AlgebraicSpace S)
        (s t : R ⟶ AlgebraicSpace.ofOver U) (e : AlgebraicSpace.ofOver U ⟶ R)
        (u : U.left),
        Groupoids.Hom.Smooth hom ∧ IsSelfFibreProduct hom s t e ∧
          AlgebraicGeometry.IsFiniteTypePoint u ∧ Points.mapSlice hom u = x ∧
            localRingDimDiff e u = d :=
  sorry

end AlgebraicGeometry.AlgebraicStack

