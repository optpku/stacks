module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.Dimension.SmoothChart
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

universe u

namespace AlgebraicGeometry.AlgebraicStack

/- Lemma 107.6.2: Let `X` be a locally Noetherian algebraic stack. Let
`x : Points X` be a finite type point. Let `d : ℤ`. The following are
equivalent: there exists a scheme `U`, a smooth morphism
`U ⟶ X`, and a finite type point `u` of `U` mapping to `x` such that
`localRingDimDiff = d`, and for every such chart the same equality holds.
Here `localRingDimDiff` is
`2 dim (Scheme.etaleLocalRing U.left ubar) - dim (AlgebraicSpace.etaleLocalRing R ((GeometricPoint.ofScheme ubar).map e))`,
`R` represents the self 2-fibre product of the chart morphism via
`IsSelfFibreProduct` with projections `s`, `t` and diagonal `e`, and
`Points.mapSlice` sends `u` to `x`. -/
@[stacks 0DS9]
#check (AlgebraicGeometry.AlgebraicStack.exists_localRingDimDiff_eq_iff :
  ∀ {S : Scheme.{u}} {X : GroupoidsOver S}
    [AlgebraicStack X] [IsLocallyNoetherian X] {x : Points X}
    (hx : IsFiniteTypePoint x) (d : ℤ),
    (∃ c : SmoothSchemeChart x, c.localRingDimDiff = d) ↔
      ∀ c : SmoothSchemeChart x, c.localRingDimDiff = d)

#check (AlgebraicGeometry.AlgebraicStack.exists_localRingDimDiff_eq_unbundled_iff :
  ∀ {S : Scheme.{u}}
    {X : GroupoidsOver S} [AlgebraicStack X] [IsLocallyNoetherian X]
    {x : Points X} (hx : IsFiniteTypePoint x) (d : ℤ),
    (∃ (U : Over S) (hom : GroupoidsOver.slice U ⟶ X) (R : AlgebraicSpace S)
        (s t : R ⟶ AlgebraicSpace.ofOver U) (e : AlgebraicSpace.ofOver U ⟶ R)
        (u : U.left),
      Groupoids.Hom.Smooth hom ∧ IsSelfFibreProduct hom s t e ∧
        AlgebraicGeometry.IsFiniteTypePoint u ∧ Points.mapSlice hom u = x ∧
          localRingDimDiff e u = d) ↔
      ∀ (U : Over S) (hom : GroupoidsOver.slice U ⟶ X) (R : AlgebraicSpace S)
        (s t : R ⟶ AlgebraicSpace.ofOver U) (e : AlgebraicSpace.ofOver U ⟶ R)
        (u : U.left),
        Groupoids.Hom.Smooth hom → IsSelfFibreProduct hom s t e →
          AlgebraicGeometry.IsFiniteTypePoint u → Points.mapSlice hom u = x →
            localRingDimDiff e u = d)

end AlgebraicGeometry.AlgebraicStack
