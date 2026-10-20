module

public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import ReasLib.AlgebraicGeometry.ProjectiveSpace.LinearProjection
public import ReasLib.AlgebraicGeometry.Scheme.OverField
public import ReasLib.AlgebraicGeometry.Scheme.Variety

/-!
# Intersections detected by linear projection

This file records the coincidence locus of two restricted linear projections and its generic
dimension bound for closed subvarieties of projective space.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.ProjectiveSpace.VectorSpace.LinearProjection

variable {k : Type u} [Field k] [IsAlgClosed k]
variable {V : Type u} [AddCommGroup V] [Module k V] [FiniteDimensional k V]

/-- The locus in the source of `f` whose image also lies in the image of `g`. -/
def coincidenceLocus {X Y Z : Scheme.{u}} (f : Y ⟶ X) (g : Z ⟶ X) : Set Y :=
  f.base ⁻¹' Set.range g.base

/-- For two proper closed subvarieties of projective space, the coincidence locus of their
restricted projections from a general closed center is their intersection together with a closed
exceptional locus whose dimension satisfies the expected additive bound. -/
theorem exists_open_coincidenceLocus_eq_union
    (n : ℕ) (hV : Module.finrank k V = n + 1)
    (Y Z : SchemeOverField k) [Variety Y] [Variety Z]
    (iY : Y ⟶ Over.mk (toSpec k V))
    (iZ : Z ⟶ Over.mk (toSpec k V))
    [IsClosedImmersion iY.left] [IsClosedImmersion iZ.left]
    (hY : Set.range iY.left.base ≠ Set.univ)
    (hZ : Set.range iZ.left.base ≠ Set.univ)
    (projection : ∀ (p : scheme k V),
      IsClosed ({p} : Set (scheme k V)) → LinearProjection k V p) :
    ∃ U : (scheme k V).Opens, Nonempty U ∧
      ∀ (p : scheme k V), p ∈ U →
        (hp : IsClosed ({p} : Set (scheme k V))) →
          p ∉ Set.range iY.left.base ∧ p ∉ Set.range iZ.left.base ∧
            ∀ (hpY : p ∉ Set.range iY.left.base) (hpZ : p ∉ Set.range iZ.left.base),
              ∃ E : TopologicalSpace.Closeds Y.left,
                coincidenceLocus
                    ((projection p hp).restrict iY.left
                      ((projection p hp).range_subset_domain iY.left hpY))
                    ((projection p hp).restrict iZ.left
                      ((projection p hp).range_subset_domain iZ.left hpZ)) =
                    iY.left.base ⁻¹' Set.range iZ.left.base ∪ (E : Set Y.left) ∧
                  topologicalKrullDim (E : Set Y.left) + (n : WithBot ℕ∞) ≤
                    topologicalKrullDim Y.left + topologicalKrullDim Z.left + 1 := sorry

end AlgebraicGeometry.ProjectiveSpace.VectorSpace.LinearProjection
