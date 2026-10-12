/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Homology.HomotopyCategory.Pretriangulated
public import ReasLib.Algebra.Homology.CochainComplex.FiniteProjective
import Mathlib.Tactic.CrossRefAttribute

/-!
# Triangulated closure of bounded finite-projective complexes

Shifts and mapping cones preserve bounded finite-projective cochain complexes of modules.  These
facts are the complex-level input for the triangulated closure of perfect derived objects.

@stack 066R
-/

@[expose] public section

noncomputable section

open CategoryTheory

universe u

namespace CochainComplex.IsBoundedFiniteProjective

variable {R : Type u} [Ring R]

local notation "Cpx" => CochainComplex (ModuleCat R) ℤ

/-- Shifts preserve bounded finite-projective cochain complexes. -/
theorem shift (L : Cpx) [L.IsBoundedFiniteProjective] (n : ℤ) :
    (L⟦n⟧).IsBoundedFiniteProjective := sorry

/-- The canonical bounded finite-projective instance on a shifted complex. -/
instance shift_instance (L : Cpx) [L.IsBoundedFiniteProjective] (n : ℤ) :
    (L⟦n⟧).IsBoundedFiniteProjective := sorry

/-- Mapping cones preserve bounded finite-projective cochain complexes. -/
theorem mappingCone {L M : Cpx} (f : L ⟶ M)
    [L.IsBoundedFiniteProjective] [M.IsBoundedFiniteProjective] :
    (CochainComplex.mappingCone f).IsBoundedFiniteProjective := sorry

/-- The canonical bounded finite-projective instance on a mapping cone. -/
instance mappingCone_instance {L M : Cpx} (f : L ⟶ M)
    [L.IsBoundedFiniteProjective] [M.IsBoundedFiniteProjective] :
    (CochainComplex.mappingCone f).IsBoundedFiniteProjective := sorry

end CochainComplex.IsBoundedFiniteProjective
