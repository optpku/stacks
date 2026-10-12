/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Homology.DerivedCategory.ModuleCat.DerivedTower.Restriction
public import ReasLib.CategoryTheory.Pretriangulated.HomotopyLimit.Presentation.Definition
import Mathlib.Tactic.CrossRefAttribute

/-!
# Base Change from Presented Limits of Derived Towers

An explicit homotopy-limit presentation supplies maps from its limit object to every restricted
stage.  An explicit derived extension model turns these into base-change maps to the original
varying-ring tower.  This construction is independent of finiteness hypotheses and does not
select concrete data from derived-functor existence proofs.
@stack 0CQF
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits

noncomputable section

universe u

namespace CategoryTheory.ModuleCat.DerivedTower.Limit.BaseChange

variable {A : SequentialInverseSystem CommRingCat.{u}}

/-- Derived extension of a fixed-base object along the map from a ring cone to stage `n`. -/
noncomputable abbrev obj (s : Cone A)
    (K : DerivedCategory (ModuleCat.{u, u} (s.pt : Type u))) (n : ℕ)
    (E : DerivedExtension (s.stageMap n).hom) :
    DerivedCategory (ModuleCat.{u, u} (A.family n : Type u)) :=
  E.obj K

/-- The stage base-change comparison adjoint to the stage projection of an explicit
homotopy-limit presentation. -/
@[stacks 0CQF "stage map from a presented derived inverse limit"]
noncomputable def map (T : DerivedTower A) (s : Cone A)
    {K : DerivedCategory (ModuleCat.{u, u} (s.pt : Type u))}
    (P : HomotopyLimit.Presentation (T.restrict s) K) (n : ℕ)
    (E : DerivedExtension (s.stageMap n).hom) :
    obj s K n E ⟶ T.obj n :=
  E.transpose (P.stageProjection n)

/-- The presented base-change map transposes back to the corresponding stage projection. -/
@[simp]
theorem map_untranspose (T : DerivedTower A) (s : Cone A)
    {K : DerivedCategory (ModuleCat.{u, u} (s.pt : Type u))}
    (P : HomotopyLimit.Presentation (T.restrict s) K) (n : ℕ)
    (E : DerivedExtension (s.stageMap n).hom) :
    E.untranspose (map T s P n E) = P.stageProjection n := sorry

/-- If every presented stage base-change map is invertible, an intrinsic homotopy limit is
nonemptily isomorphic after base change to the corresponding stage. -/
@[stacks 0CQF "presentation-independent stage base change"]
theorem nonemptyIso_of_isIso (T : DerivedTower A) (s : Cone A)
    {K : DerivedCategory (ModuleCat.{u, u} (s.pt : Type u))}
    (hK : HomotopyLimit.IsOf (T.restrict s) K) (n : ℕ)
    (E : DerivedExtension (s.stageMap n).hom)
    (h_map : ∀ P : HomotopyLimit.Presentation (T.restrict s) K,
      IsIso (map T s P n E)) :
    Nonempty (obj s K n E ≅ T.obj n) := sorry

end CategoryTheory.ModuleCat.DerivedTower.Limit.BaseChange
