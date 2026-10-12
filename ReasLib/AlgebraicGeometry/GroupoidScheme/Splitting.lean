/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import ReasLib.AlgebraicGeometry.GroupoidScheme
public import ReasLib.AlgebraicGeometry.Scheme.PreRelation.Stabilizer
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.QuasiFinite

@[expose] public section

open AlgebraicGeometry CategoryTheory

universe u

namespace AlgebraicGeometry.GroupoidScheme

/-- The set of stabilizer points of a groupoid scheme mapping to a given object point. -/
def stabilizerOver {S : Scheme.{u}} (G : GroupoidScheme S) (point : G.U.left) :
    Set G.toPreRelation.stabilizer.left.left :=
  G.toPreRelation.stabilizer.hom.left ⁻¹' ({point} : Set G.U.left)

/-- A stabilizer point belongs to the fibre over an object point exactly when its image
under the stabilizer structure morphism is that object point. -/
theorem mem_stabilizerOver {S : Scheme.{u}} (G : GroupoidScheme S) (point : G.U.left)
    (g : G.toPreRelation.stabilizer.left.left) :
    g ∈ stabilizerOver G point ↔ G.toPreRelation.stabilizer.hom.left g = point := sorry

/-- The source and target maps of a pointed groupoid scheme are separated and locally of
finite type, its stabilizer fibre is finite, and the source map is quasi-finite in the
finite-type sense at the arrow-image of every point of that fibre. -/
def SplittingHypotheses {S : Scheme.{u}} (G : GroupoidScheme S) (point : G.U.left) : Prop :=
  IsSeparated G.s.left ∧ IsSeparated G.t.left ∧
    LocallyOfFiniteType G.s.left ∧ LocallyOfFiniteType G.t.left ∧
      (stabilizerOver G point).Finite ∧
        ∀ g ∈ stabilizerOver G point,
          Scheme.Hom.FiniteType.QuasiFiniteAt G.s.left
            (G.toPreRelation.stabilizerToArrows.left g)

/-- Separatedness and local finite type of the source and target, finiteness of the
stabilizer fibre, and source quasi-finiteness on its arrow-images imply the splitting
hypotheses at the chosen object point. -/
theorem SplittingHypotheses.of {S : Scheme.{u}} (G : GroupoidScheme S) (point : G.U.left)
    (h_sourceSeparated : IsSeparated G.s.left) (h_targetSeparated : IsSeparated G.t.left)
    (h_sourceLocallyOfFiniteType : LocallyOfFiniteType G.s.left)
    (h_targetLocallyOfFiniteType : LocallyOfFiniteType G.t.left)
    (h_finite : (stabilizerOver G point).Finite)
    (h_quasiFinite : ∀ g ∈ stabilizerOver G point,
      Scheme.Hom.FiniteType.QuasiFiniteAt G.s.left
        (G.toPreRelation.stabilizerToArrows.left g)) :
    SplittingHypotheses G point := sorry

/-- The splitting hypotheses are equivalent to separatedness and local finite type of
the source and target, finiteness of the stabilizer fibre, and source quasi-finiteness
in the finite-type sense at its arrow-images. -/
theorem splittingHypotheses_iff {S : Scheme.{u}} (G : GroupoidScheme S) (point : G.U.left) :
    SplittingHypotheses G point ↔
      IsSeparated G.s.left ∧ IsSeparated G.t.left ∧
        LocallyOfFiniteType G.s.left ∧ LocallyOfFiniteType G.t.left ∧
          (stabilizerOver G point).Finite ∧
            ∀ g ∈ stabilizerOver G point,
              Scheme.Hom.FiniteType.QuasiFiniteAt G.s.left
                (G.toPreRelation.stabilizerToArrows.left g) := sorry

/-- The discrete groupoid scheme on a scheme over the base satisfies the splitting
hypotheses at every object point. -/
theorem splittingHypotheses_discrete {S : Scheme.{u}} (U : Over S) (point : U.left) :
    SplittingHypotheses (discrete U) point := sorry

end AlgebraicGeometry.GroupoidScheme
