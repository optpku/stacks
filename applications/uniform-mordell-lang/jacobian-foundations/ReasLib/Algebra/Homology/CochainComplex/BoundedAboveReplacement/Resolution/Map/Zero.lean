module

public import ReasLib.Algebra.Homology.CochainComplex.BoundedAboveReplacement.Resolution.Map
public import ReasLib.CategoryTheory.Localization.LocalizerMorphism.Resolution.Left.Map.Zero
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Zero Maps of Fixed-Upper-Bound Resolutions

This file specializes the neutral zero-map API to fixed-upper-bound resolutions without adding a
second data owner.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe v u

namespace CochainComplex.StrictlyLE.TermsIn.QuasiIsoFrom.Map

variable {A : Type u} [Category.{v} A] [Preadditive A] [CategoryWithHomology A]
  {P : ObjectProperty A} {a : ℤ}
  {K L : CochainComplex A ℤ}

/-- The zero map between fixed-upper-bound resolutions, lying over the zero cochain map. -/
@[stacks 05T7 "zero map of fixed-upper-bound resolutions"]
abbrev zero (R : QuasiIsoFrom P a K) (S : QuasiIsoFrom P a L) :
    Map (0 : K ⟶ L) R S :=
  LocalizerMorphism.LeftResolution.Map.zero R S

/-- The zero fixed-bound resolution map has zero model morphism. -/
@[simp]
theorem zero_modelHom (R : QuasiIsoFrom P a K) (S : QuasiIsoFrom P a L) :
    (zero R S).modelHom = 0 := sorry

/-- The zero fixed-bound resolution map has zero underlying cochain map. -/
@[simp]
theorem zero_hom (R : QuasiIsoFrom P a K) (S : QuasiIsoFrom P a L) :
    (zero R S).hom = 0 := sorry

/-- The zero fixed-bound resolution map satisfies the comparison square over the zero cochain
map. -/
theorem zero_naturality (R : QuasiIsoFrom P a K) (S : QuasiIsoFrom P a L) :
    (zero R S).hom ≫ S.comparison = R.comparison ≫ (0 : K ⟶ L) := sorry

end CochainComplex.StrictlyLE.TermsIn.QuasiIsoFrom.Map


