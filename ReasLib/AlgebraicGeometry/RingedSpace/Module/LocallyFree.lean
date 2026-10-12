/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Module.Projective
public import Mathlib.RingTheory.Finiteness.Basic
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.FinitePresentation.Neighborhood
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.FiniteLocallyFree.Rank
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Definition
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Site

/-!
# Finite Locally Free Module Sheaves on Ringed Spaces

The canonical properties are `SheafOfModules.IsFiniteLocallyFree` and
`SheafOfModules.IsFiniteLocallyFreeOfRank`.  This file supplies their point-neighborhood and
module-stalk views on a ringed space; it does not introduce competing property owners.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits TopologicalSpace

noncomputable section

universe u

namespace SheafOfModules

variable {X : RingedSpace.{u}}

/-- Local freeness is equivalent to admitting a free
trivialization on a neighborhood of every point. -/
@[stacks 01C6 "(1), point-neighborhood characterization"]
theorem IsLocallyFree.iff_exists_neighborhood (ℱ : RingedSpace.Modules X) :
    ℱ.IsLocallyFree ↔
      ∀ x : X,
        ∃ (U : Opens X) (_ : x ∈ U) (I : Type u),
          Nonempty
            (ℱ.over U ≅
              (.free.{u} I :
                SheafOfModules ((RingedSpace.ringCatSheaf X).over U))) := sorry

/-- A locally free module sheaf admits a point-neighborhood trivialization by a free module
sheaf. -/
theorem IsLocallyFree.exists_neighborhood
    (ℱ : RingedSpace.Modules X)
    [ℱ.IsLocallyFree] (x : X) :
    ∃ (U : Opens X) (_ : x ∈ U) (I : Type u),
      Nonempty
        (ℱ.over U ≅
          (.free.{u} I :
            SheafOfModules ((RingedSpace.ringCatSheaf X).over U))) := sorry

namespace IsLocallyFree

/-- Every stalk of a locally free module sheaf is projective over the corresponding stalk
ring. -/
@[stacks 01C6 "locally free stalks are projective", instance]
theorem moduleStalkProjective
    (ℱ : RingedSpace.Modules X) [ℱ.IsLocallyFree] (x : X) :
    Module.Projective (X.presheaf.stalk x) (RingedSpace.stalkModuleCat ℱ x) := sorry

end IsLocallyFree

/-- Finite local freeness is equivalent to
admitting a finite-free trivialization on a neighborhood of every point. -/
@[stacks 01C6 "(2), point-neighborhood characterization"]
theorem IsFiniteLocallyFree.iff_exists_neighborhood (ℱ : RingedSpace.Modules X) :
    IsFiniteLocallyFree ℱ ↔
      ∀ x : X,
        ∃ (U : Opens X) (_ : x ∈ U) (I : Type u), Finite I ∧
          Nonempty
            (ℱ.over U ≅
              (.free.{u} I :
                SheafOfModules ((RingedSpace.ringCatSheaf X).over U))) := sorry

/-- A finite locally free module sheaf admits a finite-free trivialization on a neighborhood of
every point. -/
theorem IsFiniteLocallyFree.exists_neighborhood
    (ℱ : RingedSpace.Modules X) [IsFiniteLocallyFree ℱ] (x : X) :
    ∃ (U : Opens X) (_ : x ∈ U) (I : Type u), Finite I ∧
      Nonempty
        (ℱ.over U ≅
          (.free.{u} I :
            SheafOfModules ((RingedSpace.ringCatSheaf X).over U))) := sorry

/-- Finite local freeness of rank `r` is equivalent to a rank-`r` free
trivialization on a neighborhood of every point. -/
@[stacks 01C6 "(3), point-neighborhood characterization"]
theorem IsFiniteLocallyFreeOfRank.iff_exists_neighborhood
    (r : ℕ) (ℱ : RingedSpace.Modules X) :
    IsFiniteLocallyFreeOfRank r ℱ ↔
      ∀ x : X,
        ∃ (U : Opens X) (_ : x ∈ U),
          Nonempty (ℱ.over U ≅ SheafOfModules.freeFin r) := sorry

/-- A finite locally free module sheaf of rank `r` admits a rank-`r` free trivialization on a
neighborhood of every point. -/
theorem IsFiniteLocallyFreeOfRank.exists_neighborhood
    (r : ℕ) (ℱ : RingedSpace.Modules X) [IsFiniteLocallyFreeOfRank r ℱ] (x : X) :
    ∃ (U : Opens X) (_ : x ∈ U),
      Nonempty
        (ℱ.over U ≅ SheafOfModules.freeFin r) := sorry

/-- A globally finite free module sheaf is finite locally free. -/
@[stacks 01C6 "finite free implies finite locally free", instance]
theorem isFiniteLocallyFree_of_isFiniteFree
    (ℱ : RingedSpace.Modules X) [ℱ.IsFiniteFree] :
    IsFiniteLocallyFree ℱ := sorry

namespace IsFiniteLocallyFree

/-- Every stalk of a finite locally free module sheaf is a finite module over the stalk ring. -/
instance moduleStalkFinite
    (ℱ : RingedSpace.Modules X) [IsFiniteLocallyFree ℱ] (x : X) :
    Module.Finite (X.presheaf.stalk x) (RingedSpace.stalkModuleCat ℱ x) := sorry

/-- Every stalk of a finite locally free module sheaf is projective over the stalk ring. -/
instance moduleStalkProjective
    (ℱ : RingedSpace.Modules X) [IsFiniteLocallyFree ℱ] (x : X) :
    Module.Projective (X.presheaf.stalk x) (RingedSpace.stalkModuleCat ℱ x) := sorry

end IsFiniteLocallyFree

namespace IsFiniteLocallyFreeOfRank

/-- The stalk of a finite locally free module sheaf of rank `r` is a standard free module of
rank `r`.  The isomorphism is noncanonical, so the public statement records its existence. -/
theorem moduleStalkIsoFree
    (r : ℕ) (ℱ : RingedSpace.Modules X) [IsFiniteLocallyFreeOfRank r ℱ] (x : X) :
    Nonempty
      (RingedSpace.stalkModuleCat ℱ x ≅ ModuleCat.freeFin (X.presheaf.stalk x) r) := sorry

end IsFiniteLocallyFreeOfRank

end SheafOfModules
