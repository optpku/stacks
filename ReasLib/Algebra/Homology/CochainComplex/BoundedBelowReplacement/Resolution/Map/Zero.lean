/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Homology.CochainComplex.BoundedBelowReplacement.Resolution.Map
public import ReasLib.CategoryTheory.Localization.LocalizerMorphism.Resolution.Right.Map.Zero
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Zero Maps of Fixed-Lower-Bound Resolutions

This file specializes the neutral zero-map API to fixed-lower-bound resolutions without adding a
second data owner.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe v u

namespace CochainComplex.StrictlyGE.TermsIn.QuasiIsoTo.Map

variable {A : Type u} [Category.{v} A] [Preadditive A] [CategoryWithHomology A]
  {P : ObjectProperty A} {a : ℤ}
  {K L : CochainComplex A ℤ}

/-- The zero map between fixed-lower-bound resolutions, lying over the zero cochain map. -/
@[stacks 05T6 "zero map of fixed-lower-bound resolutions"]
abbrev zero (R : QuasiIsoTo P a K) (S : QuasiIsoTo P a L) :
    Map (0 : K ⟶ L) R S :=
  LocalizerMorphism.RightResolution.Map.zero R S

/-- The zero fixed-bound resolution map has zero model morphism. -/
@[simp]
theorem zero_modelHom (R : QuasiIsoTo P a K) (S : QuasiIsoTo P a L) :
    (zero R S).modelHom = 0 := sorry

/-- The zero fixed-bound resolution map has zero underlying cochain map. -/
@[simp]
theorem zero_hom (R : QuasiIsoTo P a K) (S : QuasiIsoTo P a L) :
    (zero R S).hom = 0 := sorry

/-- The zero fixed-bound resolution map satisfies the comparison square over the zero cochain
map. -/
theorem zero_naturality (R : QuasiIsoTo P a K) (S : QuasiIsoTo P a L) :
    R.comparison ≫ (zero R S).hom = (0 : K ⟶ L) ≫ S.comparison := sorry

end CochainComplex.StrictlyGE.TermsIn.QuasiIsoTo.Map


