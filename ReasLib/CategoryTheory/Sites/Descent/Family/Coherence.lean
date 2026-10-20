/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Sites.Descent.Basic
public import ReasLib.CategoryTheory.Sites.Descent.Family.DescentDatum
public import ReasLib.CategoryTheory.Sites.Descent.Family.Overlap
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Coherence specializations for family descent data

This file gives names to the diagonal and pairwise-overlap specializations of the
general comparison isomorphism of `Pseudofunctor.DescentData`.  Formulating them
through arbitrary common restriction legs avoids tying the API to one particular
chosen-pullback presentation of descent data.

## Main declarations

* `DescentDatum.diagonalComparisonIso` -- the self-comparison over a family member.
* `DescentDatum.overlapComparisonIso` -- the comparison on a pairwise overlap.
* `DescentDatum.switchedOverlapComparisonIso` -- the comparison with the overlap legs reversed.
-/

@[expose] public section

noncomputable section

universe w v₁ v₂ u₁ u₂

namespace CategoryTheory

open Functor Limits
open SemiRepresentableFamily.Over

variable {C : Type u₁} [Category.{v₁} C]
variable {S : Type u₂} [Category.{v₂} S]
variable {p : S ⥤ C}
variable {hc : Functor.Cleavage p}
variable {U : C} {𝒰 : SemiRepresentableFamily.Over U}

namespace DescentDatum

variable (D : DescentDatum hc 𝒰)

/-- The self-comparison of a descent datum over `Uᵢ`; this is the generalized
form of restricting the diagonal comparison to the diagonal of `Uᵢ ×[U] Uᵢ`. -/
@[stacks 026C "diagonal comparison isomorphism for family descent data"]
noncomputable def diagonalComparisonIso (i : 𝒰.index) :=
  D.iso (𝒰.obj i).hom (𝟙 _) (𝟙 _) (Category.id_comp _) (Category.id_comp _)

/-- Remarks 8.3.2 (1): the diagonal self-comparison is the identity isomorphism. -/
@[stacks 026C "(1) diagonal comparison"]
theorem Comparison.diagonal_eq_refl (i : 𝒰.index) :
    D.diagonalComparisonIso i = Iso.refl _ := sorry

section Pairwise

variable [𝒰.toPresieve.HasPairwisePullbacks]

/-- The comparison isomorphism of a descent datum on the overlap `Uᵢ ×[U] Uⱼ`. -/
@[stacks 026C "overlap comparison isomorphism for family descent data"]
noncomputable def overlapComparisonIso (i j : 𝒰.index) :=
  D.iso (𝒰.overlapMap i j) (𝒰.fst i j) (𝒰.snd i j)
    (𝒰.fst_hom i j) (𝒰.snd_hom i j)

/-- The overlap comparison with its two restriction legs reversed.  In a
chosen-pullback presentation, this is the pullback of the reverse comparison
along the overlap-switching morphism. -/
@[stacks 026C "switched overlap comparison isomorphism for family descent data"]
noncomputable def switchedOverlapComparisonIso (i j : 𝒰.index) :=
  D.iso (𝒰.overlapMap i j) (𝒰.snd i j) (𝒰.fst i j)
    (𝒰.snd_hom i j) (𝒰.fst_hom i j)

/-- Reversing the two overlap legs gives the inverse comparison isomorphism. -/
@[stacks 026C "symmetry of switched overlap comparison"]
theorem Comparison.switched_eq_symm (i j : 𝒰.index) :
    D.switchedOverlapComparisonIso i j = (D.overlapComparisonIso i j).symm := sorry

/-- Remarks 8.3.2 (2): a comparison on an overlap followed by the comparison
with switched legs is the identity. -/
@[stacks 026C "(2) overlap comparison with switched legs"]
theorem Comparison.comp_switched_eq_refl (i j : 𝒰.index) :
    D.overlapComparisonIso i j ≪≫ D.switchedOverlapComparisonIso i j = Iso.refl _ := sorry

end Pairwise

end DescentDatum

/- Data audit (mathlib 4.32): all three isomorphisms specialize the comparison isomorphism stored
by the supplied descent datum.  They neither select pullbacks nor choose representatives; their
non-`Prop` morphism data are inherited directly from `DescentDatum.iso`. -/

end CategoryTheory
