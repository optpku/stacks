/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Pretriangulated.HomotopyColimit.RepresentedHom.DerivedLimit
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.CategoryTheory.Triangulated.Triangulated
import Mathlib.Tactic.CrossRefAttribute

/-!
# The represented Hom Milnor short complex

This leaf packages the first-derived-limit inclusion and the map to the inverse limit as a
short complex, and exposes all three objects and both maps for downstream rewriting.
@stack 0CQX
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated Opposite

noncomputable section

universe u v

namespace CategoryTheory.HomotopyColimit.RepresentedHom

open SequentialInverseSystem.Milnor.ProductCone

variable {D : Type u} [Category.{v} D] [HasZeroObject D] [Preadditive D]
  [HasShift D ℤ] [∀ n : ℤ, Functor.Additive (shiftFunctor D n)] [Pretriangulated D]

/-- The represented Hom Milnor short complex attached to a telescope presentation. -/
@[stacks 0CQX]
def shortComplex {K : ℕ ⥤ D} {X : D} (P : Presentation K X) (L : D) :
    ShortComplex AddCommGrpCat :=
  ShortComplex.mk (r1Inclusion P L) (homToLimit P L)
    (r1Inclusion_comp_homToLimit P L)

/-- The left object of the represented Hom short complex is the canonical first derived limit
of the shifted represented Hom tower. -/
@[simp]
theorem shortComplex_X₁ {K : ℕ ⥤ D} {X : D} (P : Presentation K X) (L : D) :
    (shortComplex P L).X₁ = canonicalR1 (shiftedTower K L) := sorry

/-- The middle object of the represented Hom short complex is `Hom_D(X, L)`. -/
@[simp]
theorem shortComplex_X₂ {K : ℕ ⥤ D} {X : D} (P : Presentation K X) (L : D) :
    (shortComplex P L).X₂ = (preadditiveYoneda.obj L).obj (op X) := sorry

/-- The right object of the represented Hom short complex is the inverse limit of the
represented Hom tower. -/
@[simp]
theorem shortComplex_X₃ {K : ℕ ⥤ D} {X : D} (P : Presentation K X) (L : D) :
    (shortComplex P L).X₃ = limit (tower K L) := sorry

/-- The first map of the represented Hom short complex is the first-derived-limit
inclusion. -/
@[simp]
theorem shortComplex_f {K : ℕ ⥤ D} {X : D} (P : Presentation K X) (L : D) :
    (shortComplex P L).f = r1Inclusion P L := sorry

/-- The second map of the represented Hom short complex is the canonical map to the inverse
limit. -/
@[simp]
theorem shortComplex_g {K : ℕ ⥤ D} {X : D} (P : Presentation K X) (L : D) :
    (shortComplex P L).g = homToLimit P L := sorry

/-- Lemma 15.87.7 (Stacks 0CQX): the represented Hom Milnor short complex of a telescope
presentation is short exact. -/
@[stacks 0CQX]
theorem shortExact [IsTriangulated D] {K : ℕ ⥤ D} {X : D}
    (P : Presentation K X) (L : D) :
    (shortComplex P L).ShortExact := sorry

end CategoryTheory.HomotopyColimit.RepresentedHom

end
