/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Limits.Shapes.ZeroObjects
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Cech
public import Mathlib.Topology.Sheaves.AddCommGrpCat
public import ReasLib.Topology.Opens.Instances
public import ReasLib.Topology.Presheaf.Cech.Basic
public import ReasLib.Topology.Presheaf.Cech.Coordinates
public import ReasLib.Topology.Sheaf.Cohomology.Cech.ColimitComparison
public import ReasLib.Topology.Sheaf.Cohomology.Cech.LowDegree
public import ReasLib.Topology.Sheaf.Cohomology.Cech.Compact
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Čech vanishing from surjective restriction maps

This leaf owns the reusable topological Čech statement used by the flasque-sheaf arguments in
Chapter 20.  Finite intersections and their arbitrary unions are expressed in the presheaf Cech
namespace; the vanishing theorem is then exposed at the sheaf cohomology layer.  No chapter file
is imported here.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped BigOperators

noncomputable section

universe u v

namespace TopCat.Presheaf.Cech

variable {X : TopCat.{u}} {ι : Type v}

/-- Every nonempty finite Cech intersection is contained in the union of its family. -/
@[stacks 0A36 "finite Cech intersections lie in the family union"]
theorem intersection_le_iSup (𝒰 : ι → Opens X) {n : ℕ} (σ : Fin (n + 1) → ι) :
    intersection 𝒰 σ ≤ iSup 𝒰 := sorry

/-- Every nonempty finite Cech intersection of a cover lies in the covered open. -/
@[stacks 0A36 "finite Cech intersections lie in the covered open"]
theorem intersection_le_of_iSup_eq (U : Opens X) (𝒰 : ι → Opens X)
    (hcover : U = iSup 𝒰) {n : ℕ} (σ : Fin (n + 1) → ι) :
    intersection 𝒰 σ ≤ U := sorry

/-- An open is a union of finite Cech intersections of an indexed family.

The indexing subtype is canonical: choosing a set of finite tuples avoids forcing an auxiliary
index type or exposing a witness family as part of downstream statements.
-/
@[stacks 0A36 "unions of finite Cech intersections"]
def IsUnionOfFiniteIntersections (𝒰 : ι → Opens X) (U' : Opens X) : Prop :=
  ∃ s : Set (Σ n : ℕ, Fin (n + 1) → ι),
    U' = iSup fun σ : s ↦ intersection 𝒰 σ.1.2

/-- A union of finite Cech intersections is contained in the union of the family. -/
@[stacks 0A36 "finite-intersection union inclusion"]
theorem IsUnionOfFiniteIntersections.le_iSup
    {𝒰 : ι → Opens X} {U' : Opens X}
    (hU' : IsUnionOfFiniteIntersections 𝒰 U') :
    U' ≤ iSup 𝒰 := sorry

end TopCat.Presheaf.Cech

namespace TopCat.Sheaf.Cohomology.Cech

variable {X : TopCat.{u}} {ι : Type v}

/-- Positive-degree Cech cohomology vanishes when all finite-intersection unions lift sections.

The hypothesis is phrased using the intrinsic open-subset predicate, so a downstream argument
only supplies the restriction maps it actually needs and never carries a chosen indexing family.
-/
@[stacks 0A36 "positive-degree Cech vanishing from surjective restrictions"]
theorem isZero_of_surjective_restrictions
    (𝒰 : ι → Opens X)
    (ℱ : X.Sheaf AddCommGrpCat.{max u v})
    (hres : ∀ ⦃U' : Opens X⦄
      (hU'fin : TopCat.Presheaf.Cech.IsUnionOfFiniteIntersections 𝒰 U'),
      Function.Surjective
        (ℱ.presheaf.map (homOfLE hU'fin.le_iSup).op))
    (p : ℕ) (hp : 0 < p) :
    IsZero (((cechComplexFunctor 𝒰).obj ℱ.presheaf).homology p) := sorry



end TopCat.Sheaf.Cohomology.Cech

end
