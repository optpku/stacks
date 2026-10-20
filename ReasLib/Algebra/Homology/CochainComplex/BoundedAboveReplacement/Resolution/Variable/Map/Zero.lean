/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Homology.CochainComplex.BoundedAboveReplacement.Resolution.Variable.Map
public import ReasLib.Algebra.Homology.CochainComplex.BoundedAboveReplacement.Resolution.Variable.Preadditive
public import ReasLib.CategoryTheory.Localization.LocalizerMorphism.Resolution.Left.Map.Zero

/-!
# Zero Maps of Variable-Upper-Bound Resolutions

This file specializes the neutral zero-map calculus to variable-upper-bound termwise left
resolutions. The underlying data remain owned by the neutral resolution-map API.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe v u

namespace CochainComplex.Minus.TermsIn.QuasiIsoFrom.Map

variable {A : Type u} [Category.{v} A] [Preadditive A] [CategoryWithHomology A]
  {P : ObjectProperty A}
  {K L M : CochainComplex A ℤ} {f : K ⟶ L} {g : L ⟶ M}
  {R : QuasiIsoFrom P K} {S : QuasiIsoFrom P L} {T : QuasiIsoFrom P M}

/-- The zero map between variable-upper-bound resolutions, lying over the zero cochain map. -/
abbrev zero (R : QuasiIsoFrom P K) (S : QuasiIsoFrom P L) : Map (0 : K ⟶ L) R S :=
  LocalizerMorphism.LeftResolution.Map.zero R S

/-- The zero variable-upper-bound resolution map has zero model morphism. -/
@[simp]
theorem zero_modelHom (R : QuasiIsoFrom P K) (S : QuasiIsoFrom P L) :
    (zero R S).modelHom = 0 := sorry

/-- The zero variable-upper-bound resolution map has zero underlying cochain map. -/
@[simp]
theorem zero_hom (R : QuasiIsoFrom P K) (S : QuasiIsoFrom P L) :
    (zero R S).hom = 0 := sorry

/-- The zero variable-upper-bound resolution map satisfies its comparison square. -/
theorem zero_naturality (R : QuasiIsoFrom P K) (S : QuasiIsoFrom P L) :
    (zero R S).hom ≫ S.comparison = R.comparison ≫ (0 : K ⟶ L) := sorry

/-- Reindexing a zero variable-upper-bound resolution map along a zero equality is trivial. -/
@[simp]
theorem reindex_zero (R : QuasiIsoFrom P K) (S : QuasiIsoFrom P L)
    (e : (0 : K ⟶ L) = 0) : reindex e (zero R S) = zero R S := sorry

/-- Composing a zero variable-upper-bound resolution map on the left gives zero. -/
@[simp]
theorem zero_comp (m : Map g S T) :
    reindex Limits.zero_comp (comp (zero R S) m) = zero R T := sorry

/-- Composing a zero variable-upper-bound resolution map on the right gives zero. -/
@[simp]
theorem comp_zero (m : Map f R S) :
    reindex Limits.comp_zero (comp m (zero S T)) = zero R T := sorry

end CochainComplex.Minus.TermsIn.QuasiIsoFrom.Map


