/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Homology.DegreewiseSplit
public import ReasLib.CategoryTheory.ShortComplex.MiddleMap
public import ReasLib.Algebra.Homology.HomologicalComplex.Double
public import Mathlib.Algebra.Category.Grp.Preadditive
public import Mathlib.Algebra.Category.Grp.Zero
public import Mathlib.Algebra.Homology.HomotopyCategory.DegreewiseSplit
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Tactic.CrossRefAttribute

/-!
# The degreewise-split middle-map obstruction

The Stacks Project constructs the obstruction over a ring of dual numbers.  This leaf records a
fully explicit instance in `ZMod 4`, where multiplication by `2` is a nonzero square-zero
endomorphism.  The canonical single--double--single row supplies the degreewise-split short
complex, while the maps and the homotopy witnessing the left square are exposed as concrete data.
-/

@[expose] public section

open CategoryTheory ComplexShape HomologicalComplex

universe v u

namespace CochainComplex

namespace DegreewiseSplit.Strictification

namespace ZModFour

/-- The additive group underlying the concrete coefficient ring `ZMod 4`. -/
@[stacks 014J "concrete coefficient object for the middle-map obstruction"]
abbrev R : AddCommGrpCat := AddCommGrpCat.of (ZMod 4)

/-- Multiplication by `2` on `ZMod 4`, regarded as an additive endomorphism. -/
@[stacks 014J "square-zero endomorphism for the middle-map obstruction"]
def epsilon : R ⟶ R := (2 : ℤ) • 𝟙 R

/-- The endomorphism `1 + epsilon`, which is multiplication by `3` on `ZMod 4`. -/
@[stacks 014J "twisted endpoint map for the middle-map obstruction"]
def onePlusEpsilon : R ⟶ R := 𝟙 R + epsilon

/-- The arrow whose two-term cochain complex has differential `epsilon`. -/
@[stacks 014J "two-term differential for the middle-map obstruction"]
def differential : Arrow AddCommGrpCat := Arrow.mk epsilon

/-- Degrees `0` and `1` are related by the cochain-complex shape. -/
theorem relZeroOne : (up ℤ).Rel (0 : ℤ) 1 := sorry

/-- The two supporting degrees of the concrete two-term complex are distinct. -/
theorem zero_ne_one : (0 : ℤ) ≠ 1 := sorry

/-- The canonical degreewise-split row
`R[1] ⟶ (R ⟶[ε] R) ⟶ R[0]` used by the concrete obstruction. -/
@[stacks 014J "explicit degreewise-split row for the middle-map obstruction"]
noncomputable abbrev row : ShortComplex (CochainComplex AddCommGrpCat ℤ) :=
  HomologicalComplex.double.shortComplex.app relZeroOne zero_ne_one differential

/-- The canonical chosen splitting of `row` in every degree. -/
@[stacks 014J "chosen splitting of the concrete obstruction row"]
noncomputable def splitting : ShortComplex.DegreewiseSplitting row :=
  HomologicalComplex.double.degreewiseSplitting differential relZeroOne zero_ne_one

/-- The vertical map on the left endpoint, induced by `1 + epsilon`. -/
@[stacks 014J "left endpoint map in the middle-map obstruction"]
noncomputable def leftMap : row.X₁ ⟶ row.X₁ :=
  (HomologicalComplex.single AddCommGrpCat (up ℤ) 1).map onePlusEpsilon

/-- The prescribed vertical map on the middle two-term complex. -/
@[stacks 014J "middle map in the strictification obstruction"]
noncomputable def middleMap : row.X₂ ⟶ row.X₂ := 𝟙 _

/-- The vertical map on the right endpoint. -/
@[stacks 014J "right endpoint map in the middle-map obstruction"]
noncomputable def rightMap : row.X₃ ⟶ row.X₃ := 𝟙 _

/-- Evaluation of `epsilon` is multiplication by `2`. -/
@[simp, stacks 014J "evaluation of the concrete square-zero endomorphism"]
theorem epsilon_apply (x : ZMod 4) : epsilon x = (2 : ZMod 4) * x := sorry

/-- Evaluation of `onePlusEpsilon` is multiplication by `3`. -/
@[simp, stacks 014J "evaluation of the concrete twisted endpoint map"]
theorem onePlusEpsilon_apply (x : ZMod 4) :
    onePlusEpsilon x = (3 : ZMod 4) * x := sorry

/-- The endomorphism `epsilon` is square-zero. -/
@[stacks 014J "square-zero relation in the concrete obstruction"]
theorem epsilon_sq : epsilon ≫ epsilon = 0 := sorry

/-- The endomorphism `epsilon` is nonzero. -/
@[stacks 014J "nontriviality of the concrete obstruction"]
theorem epsilon_ne_zero : epsilon ≠ 0 := sorry

/-- The degree `-1` family whose sole nonzero coordinate is the identity
`row.X₁.X 1 ⟶ row.X₂.X 0`, under the canonical endpoint identifications. -/
@[stacks 014J "explicit homotopy coordinate for the left square"]
noncomputable def leftHomotopyComponent (i j : ℤ) :
    row.X₁.X i ⟶ row.X₂.X j :=
  if h : i = 1 ∧ j = 0 then
    eqToHom (congrArg (fun n ↦ row.X₁.X n) h.1) ≫
      (HomologicalComplex.singleObjXSelf (up ℤ) 1 R).hom ≫
        (HomologicalComplex.doubleXIso₀ epsilon relZeroOne).inv ≫
          eqToHom (congrArg (fun n ↦ row.X₂.X n) h.2.symm)
  else 0

/-- The unique nonzero coordinate of the selected homotopy is the identity after the canonical
single- and double-complex endpoint identifications. -/
@[simp, stacks 014J "central coordinate of the explicit left-square homotopy"]
theorem leftHomotopyComponent_one_zero :
    leftHomotopyComponent 1 0 =
      (HomologicalComplex.singleObjXSelf (up ℤ) 1 R).hom ≫
        (HomologicalComplex.doubleXIso₀ epsilon relZeroOne).inv := sorry

/-- The explicit left-square homotopy family vanishes outside adjacent degrees. -/
theorem leftHomotopyComponent_zero (i j : ℤ) (hij : ¬ (up ℤ).Rel j i) :
    leftHomotopyComponent i j = 0 := sorry

/-- The explicit left-square homotopy family satisfies the homotopy equation. -/
theorem leftHomotopyComponent_comm (i : ℤ) :
    (leftMap ≫ row.f).f i =
      dNext i leftHomotopyComponent + prevD i leftHomotopyComponent +
        (row.f ≫ middleMap).f i := sorry

/-- The chosen homotopy from the twisted left composite to the identity middle composite. -/
@[stacks 014J "explicit homotopy witnessing the left square"]
noncomputable def leftHomotopy :
    Homotopy (leftMap ≫ row.f) (row.f ≫ middleMap) :=
  Homotopy.mk leftHomotopyComponent leftHomotopyComponent_zero
    leftHomotopyComponent_comm

/-- The components of `leftHomotopy` are the explicitly selected family
`leftHomotopyComponent`. -/
@[simp, stacks 014J "component formula for the explicit left-square homotopy"]
theorem leftHomotopy_hom (i j : ℤ) :
    leftHomotopy.hom i j = leftHomotopyComponent i j := sorry

/-- The concrete short-complex row is degreewise split. -/
@[stacks 014J "degreewise splitness of the concrete obstruction row"]
theorem isDegreewiseSplit : row.IsDegreewiseSplit := sorry

/-- The left square of the concrete diagram commutes in the homotopy category. -/
@[stacks 014J "homotopy-commutative left square of the concrete obstruction"]
theorem leftCommSq :
    let Q := HomotopyCategory.quotient AddCommGrpCat (up ℤ)
    CommSq (Q.map row.f) (Q.map leftMap) (Q.map middleMap) (Q.map row.f) := sorry

/-- The right square of the concrete diagram commutes in the homotopy category. -/
@[stacks 014J "commutative right square of the concrete obstruction"]
theorem rightCommSq :
    let Q := HomotopyCategory.quotient AddCommGrpCat (up ℤ)
    CommSq (Q.map row.g) (Q.map middleMap) (Q.map rightMap) (Q.map row.g) := sorry

/-- Remark 13.9.11: the explicit `ZMod 4` middle map cannot be replaced by a homotopic map
that makes both squares strictly commute. -/
@[stacks 014J "explicit non-strictifiable middle map"]
theorem notStrictifiable :
    let Q := HomotopyCategory.quotient AddCommGrpCat (up ℤ)
    ¬ ShortComplex.IsMiddleMapStrictifiable Q row row leftMap middleMap rightMap := sorry

end ZModFour

/-- Remark 13.9.11: degreewise-split rows can have homotopy-commutative outer squares for which no
strict short-complex morphism realizes the prescribed middle map in the homotopy category.  This
is the existential compatibility view of `ZModFour.notStrictifiable`. -/
@[stacks 014J]
theorem exists_nonStrictifiableMiddleMap :
    let Q := HomotopyCategory.quotient AddCommGrpCat (up ℤ)
    ∃ (S₁ S₂ : ShortComplex (CochainComplex AddCommGrpCat ℤ))
      (a : S₁.X₁ ⟶ S₂.X₁) (b : S₁.X₂ ⟶ S₂.X₂) (c : S₁.X₃ ⟶ S₂.X₃),
      S₁.IsDegreewiseSplit ∧ S₂.IsDegreewiseSplit ∧
      CommSq (Q.map S₁.f) (Q.map a) (Q.map b) (Q.map S₂.f) ∧
      CommSq (Q.map S₁.g) (Q.map b) (Q.map c) (Q.map S₂.g) ∧
      ¬ ShortComplex.IsMiddleMapStrictifiable Q S₁ S₂ a b c := sorry

end DegreewiseSplit.Strictification

end CochainComplex
