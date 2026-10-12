/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.StructureSheaf
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.HasExt
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import Mathlib.RingTheory.LocalRing.Defs
public import Mathlib.Tactic.CrossRefAttribute
public import Mathlib.Topology.Sheaves.Abelian
public import ReasLib.CategoryTheory.Sites.AbelianSheaf.Grothendieck
public import ReasLib.Topology.Sheaves.Abelian.Sheafification

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace TopCat

noncomputable section

universe u

namespace TopCat.Sheaf.Cohomology

/-- Higher cohomology vanishes on the spectrum of a commutative local ring. -/
@[stacks 0D8T]
theorem isZero_higherCohomology_of_isLocalRing
    {R : Type u} [CommRing R] [IsLocalRing R]
    (F : (PrimeSpectrum.Top R).Sheaf AddCommGrpCat.{u}) {i : ℕ} (hi : 0 < i) :
    IsZero (F.H' i (⊤ : Opens (PrimeSpectrum.Top R))) := sorry

end TopCat.Sheaf.Cohomology
