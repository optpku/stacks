/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Homology.CochainComplex.BoundedBelowReplacement.Resolution.Variable.Map
public import ReasLib.Algebra.Homology.CochainComplex.BoundedBelowReplacement.Resolution.Variable.Preadditive
public import ReasLib.CategoryTheory.Localization.LocalizerMorphism.Resolution.Right.Map.Zero

/-!
# Zero Maps of Variable-Lower-Bound Resolutions

This file specializes the neutral zero-map calculus to variable-lower-bound termwise right
resolutions. The underlying data remain owned by the neutral resolution-map API.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe v u

namespace CochainComplex.Plus.TermsIn.QuasiIsoTo.Map

variable {A : Type u} [Category.{v} A] [Preadditive A] [CategoryWithHomology A]
  {P : ObjectProperty A}
  {K L M : CochainComplex A ℤ} {f : K ⟶ L} {g : L ⟶ M}
  {R : QuasiIsoTo P K} {S : QuasiIsoTo P L} {T : QuasiIsoTo P M}

/-- The zero map between variable-lower-bound resolutions, lying over the zero cochain map. -/
abbrev zero (R : QuasiIsoTo P K) (S : QuasiIsoTo P L) : Map (0 : K ⟶ L) R S :=
  LocalizerMorphism.RightResolution.Map.zero R S

/-- The zero variable-lower-bound resolution map has zero model morphism. -/
@[simp]
theorem zero_modelHom (R : QuasiIsoTo P K) (S : QuasiIsoTo P L) :
    (zero R S).modelHom = 0 := sorry

/-- The zero variable-lower-bound resolution map has zero underlying cochain map. -/
@[simp]
theorem zero_hom (R : QuasiIsoTo P K) (S : QuasiIsoTo P L) :
    (zero R S).hom = 0 := sorry

/-- The zero variable-lower-bound resolution map satisfies its comparison square. -/
theorem zero_naturality (R : QuasiIsoTo P K) (S : QuasiIsoTo P L) :
    R.comparison ≫ (zero R S).hom = (0 : K ⟶ L) ≫ S.comparison := sorry

/-- Reindexing a zero variable-lower-bound resolution map along a zero equality is trivial. -/
@[simp]
theorem reindex_zero (R : QuasiIsoTo P K) (S : QuasiIsoTo P L)
    (e : (0 : K ⟶ L) = 0) : reindex e (zero R S) = zero R S := sorry

/-- Composing a zero variable-lower-bound resolution map on the left gives zero. -/
@[simp]
theorem zero_comp (m : Map g S T) :
    reindex Limits.zero_comp (comp (zero R S) m) = zero R T := sorry

/-- Composing a zero variable-lower-bound resolution map on the right gives zero. -/
@[simp]
theorem comp_zero (m : Map f R S) :
    reindex Limits.comp_zero (comp m (zero S T)) = zero R T := sorry

end CochainComplex.Plus.TermsIn.QuasiIsoTo.Map


