/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap73.Definition_73_4_5_Site
public import stacks_project.Chap73.Definition_73_7_1_FppfCover
public import stacks_project.Chap73.Lemma_73_7_3_Precoverage

/-!
# Chosen big fppf sites of algebraic spaces

A big fppf site of algebraic spaces over a scheme `S` is a cardinal truncation
of `fppfPrecoverage S` supplied by Sets Lemma 3.11.1: the underlying category
is `AlgebraicSpace S`, and the chosen covering families are combinatorially
equivalent to the class of fppf coverings.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped Cardinal

noncomputable section

universe u v

namespace AlgebraicGeometry.AlgebraicSpace

/-- The fppf covering class of algebraic spaces over `S` satisfies the site
axioms. -/
instance instFppfPrecoverageIsSite (S : Scheme.{u}) :
    (fppfPrecoverage S).IsSite :=
  sorry

/-- A big fppf site of algebraic spaces over a scheme `S` is a chosen big site
for the fppf covering class. -/
abbrev ChosenBigFppfSite (S : Scheme.{u}) :=
  ChosenBigSite (fppfPrecoverage S)

namespace ChosenBigFppfSite

/-- Package an infinite cardinal at which the truncated fppf covering class is a
site and combinatorially represents every fppf covering. -/
def ofCardinal {S : Scheme.{u}} (κ : Cardinal.{u + 1}) (aleph0_le : ℵ₀ ≤ κ)
    (equivalent :
      (fppfPrecoverage S).coversUpToCombinatorialEquivalence
        ((fppfPrecoverage S).restrictCardinalLE κ)) :
    ChosenBigFppfSite S :=
  ChosenBigSite.ofBound κ (Precoverage.isSite_restrictCardinalLE aleph0_le) equivalent

/-- The bound of `ofCardinal κ aleph0_le equivalent` is `κ`. -/
theorem ofCardinal_bound {S : Scheme.{u}} (κ : Cardinal.{u + 1})
    (aleph0_le : ℵ₀ ≤ κ)
    (equivalent :
      (fppfPrecoverage S).coversUpToCombinatorialEquivalence
        ((fppfPrecoverage S).restrictCardinalLE κ)) :
    (ofCardinal κ aleph0_le equivalent).bound = κ :=
  sorry

/-- An indexed family belongs to the chosen covering set if and only if it is an
fppf covering whose uncurried support is bounded by the chosen cardinal. -/
theorem ofArrows_mem_precoverage_iff {S : Scheme.{u}} (𝒮 : ChosenBigFppfSite S)
    {X : AlgebraicSpace S} {ι : Type v} {Xᵢ : ι → AlgebraicSpace S}
    (f : (i : ι) → Xᵢ i ⟶ X) :
    Presieve.ofArrows Xᵢ f ∈ 𝒮.precoverage X ↔
      FppfCovering Xᵢ f ∧
        Cardinal.lift #((Presieve.ofArrows Xᵢ f).uncurry) ≤
          Cardinal.lift 𝒮.bound :=
  sorry

end ChosenBigFppfSite

/-- Sets Lemma 3.11.1 supplies a chosen big fppf site of algebraic spaces over
`S`. -/
theorem ChosenBigFppfSite.exists (S : Scheme.{u}) :
    Nonempty (ChosenBigFppfSite S) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace

