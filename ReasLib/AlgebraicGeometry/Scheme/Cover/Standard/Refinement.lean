/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.Cover.MorphismProperty
public import Mathlib.CategoryTheory.Sites.Sieves
public import ReasLib.AlgebraicGeometry.Scheme.Cover.Standard
public import ReasLib.AlgebraicGeometry.Scheme.Sites.ChosenPresentation.Standard

@[expose] public section

open CategoryTheory
open AlgebraicGeometry

universe u v

namespace AlgebraicGeometry.StandardTopology

/-- Every cover of an affine scheme for one of the five standard topologies
admits a finite affine standard cover refining it. -/
theorem exists_standardCover_refinement
    {T : Scheme.{u}} [IsAffine T] (τ : StandardTopology)
    (𝒰 : Scheme.Cover.{v} τ.precoverage T) :
    ∃ 𝒱 : AffineFamilyOver T,
      τ.IsCover 𝒱 ∧
        Sieve.ofArrows 𝒱.U 𝒱.map ≤ 𝒰.sieve₀ := sorry

end AlgebraicGeometry.StandardTopology
