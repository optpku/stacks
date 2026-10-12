/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Category.ModuleCat.AB
public import Mathlib.Algebra.Category.ModuleCat.Colimits
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Symmetric
public import ReasLib.Algebra.Homology.CochainComplex.KFlat.Colimit
import Mathlib.Tactic.CrossRefAttribute

/-!
# Filtered colimits of K-flat module complexes

@stack 06Y3

Filtered colimits of K-flat cochain complexes of modules are K-flat.  This ModuleCat bridge
specializes the categorical exact-colimit owner and makes the standard module-category
instances available to downstream users.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u v

namespace CochainComplex

variable {R : Type u} [CommRing R]

/-- Lemma 15.59.8 (06Y3): a filtered colimit of K-flat cochain complexes of modules is K-flat.
The sequential-system statement is the specialization to the filtered category `ℕ`. -/
@[stacks 06Y3 "filtered colimits of K-flat complexes are K-flat"]
theorem isKFlat_colimit_of_isFiltered
    {I : Type v} [Category.{v} I] [IsFiltered I]
    (F : I ⥤ CochainComplex (ModuleCat R) ℤ) [HasColimit F]
    (hF : ∀ i : I, (F.obj i).IsKFlat) :
    (colimit F).IsKFlat := sorry

end CochainComplex
