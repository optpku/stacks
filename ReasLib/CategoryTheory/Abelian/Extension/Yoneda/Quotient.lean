/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Abelian.Extension.Yoneda
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Quotients of Yoneda Extensions

This file owns the degree-lowering operation on a positive Yoneda extension.  It quotients the
leftmost monomorphism, retains the exact tail, and records the short exact sequence removed from
the head.  The construction is independent of derived categories and `Ext`.
-/

@[expose] public section

open CategoryTheory Limits ComposableArrows

noncomputable section

universe v u

namespace CategoryTheory.YonedaExtension

variable {C : Type u} [Category.{v} C] [Abelian C]
variable {A B : C}

namespace Quotient

namespace Index

/-- The first nontrivial pair of positions in a composable row is ordered. -/
theorem one_two : (1 : ℕ) ≤ 2 := by decide

/-- A degree-`n + 1` Yoneda row contains its second nontrivial object. -/
theorem two_length (n : ℕ+) : (2 : ℕ) ≤ ((n + 1 : ℕ+) : ℕ) :=
  Nat.succ_le_succ n.pos

end Index

/-- The arrow following the first map of a positive-degree Yoneda extension. -/
abbrev next {n : ℕ+} (E : YonedaExtension A B (n + 1)) :
    E.obj.obj' 1 ⟶ E.obj.obj' 2 (Index.two_length (n + 1)) :=
  E.obj.map' 1 2 Index.one_two (Index.two_length (n + 1))

/-- The first two maps of a positive-degree Yoneda extension compose to zero. -/
theorem firstMap_comp_next {n : ℕ+} (E : YonedaExtension A B (n + 1)) :
    E.firstMap ≫ next E = 0 := by
  dsimp only [firstMap, next]
  rw [Category.assoc, E.exact.toIsComplex.zero 0 (Index.two_length (n + 1)), comp_zero]

/-- The map from the cokernel of the first arrow to the next object in the extension. -/
@[stacks 06XU]
noncomputable def map {n : ℕ+} (E : YonedaExtension A B (n + 1)) :
    cokernel E.firstMap ⟶ E.obj.obj' 2 (Index.two_length (n + 1)) :=
  cokernel.desc E.firstMap (next E) (firstMap_comp_next E)

/-- The quotient projection followed by `map E` recovers the second arrow of `E`. -/
@[reassoc (attr := simp), stacks 06XU]
theorem π_comp_map {n : ℕ+} (E : YonedaExtension A B (n + 1)) :
    cokernel.π E.firstMap ≫ map E = next E := by
  exact cokernel.π_desc _ _ _

/-- The descended quotient map carries its canonical monomorphism instance. -/
noncomputable instance mapMono {n : ℕ+} (E : YonedaExtension A B (n + 1)) :
    Mono (map E) := by
  let φ : ShortComplex.mk E.firstMap (next E) (firstMap_comp_next E) ⟶
      E.exact.sc 0 (Index.two_length (n + 1)) :=
    { τ₁ := eqToHom E.leftEq.symm
      τ₂ := 𝟙 _
      τ₃ := 𝟙 _
      comm₁₂ := by
        change E.firstMap = E.firstMap ≫ 𝟙 _
        exact (Category.comp_id _).symm
      comm₂₃ := by simp [next] }
  exact ((ShortComplex.exact_iff_of_epi_of_isIso_of_mono φ).2
    (E.exact.exact 0 (Index.two_length (n + 1)))).mono_cokernelDesc

/-- The composable row obtained by deleting the first two objects and prepending the descended
quotient map is again exact. -/
theorem row_exact {n : ℕ+} (E : YonedaExtension A B (n + 1)) :
    ((E.obj.δ₀.δ₀).precomp (map E)).Exact := by
  have hn := n.pos
  have hlength : ((n + 1 : ℕ+) : ℕ) = (n : ℕ) + 1 := rfl
  have hz : map E ≫ E.obj.map' 2 3 = 0 := by
    rw [← cancel_epi (cokernel.π E.firstMap), ← Category.assoc, π_comp_map,
      E.exact.toIsComplex.zero 1, comp_zero]
  refine { toIsComplex := ⟨?_⟩, exact := ?_ }
  · intro i hi
    cases i with
    | zero => exact hz
    | succ i => exact E.exact.toIsComplex.zero (i + 2) (Nat.succ_le_succ hi)
  · intro i hi
    cases i with
    | zero =>
      let φ : E.exact.sc 1 ⟶ ShortComplex.mk (map E) (E.obj.map' 2 3) hz :=
        { τ₁ := cokernel.π E.firstMap
          τ₂ := 𝟙 _
          τ₃ := 𝟙 _
          comm₁₂ := by simpa only [Category.comp_id] using π_comp_map E
          comm₂₃ := by simp }
      exact (ShortComplex.exact_iff_of_epi_of_isIso_of_mono φ).1 (E.exact.exact 1)
    | succ i => exact E.exact.exact (i + 2) (Nat.succ_le_succ hi)

/-- The quotient row has the defining endpoint, exactness, and outer mono/epi properties of a
degree-`n` Yoneda extension. -/
theorem property {n : ℕ+} (E : YonedaExtension A B (n + 1)) :
    IsYonedaExtension (cokernel E.firstMap) B n ((E.obj.δ₀.δ₀).precomp (map E)) where
  left_eq := rfl
  right_eq := E.rightEq
  mono_first := by
    change Mono (𝟙 _ ≫ map E)
    infer_instance
  exact := row_exact E
  epi_last := by
    rcases n with ⟨_ | n, hn⟩
    · omega
    · exact E.property.epi_last

/-- Quotienting the first map of a degree-`n + 1` Yoneda extension produces a degree-`n`
Yoneda extension whose left endpoint is `cokernel E.firstMap`. -/
@[stacks 06XU]
noncomputable def obj {n : ℕ+} (E : YonedaExtension A B (n + 1)) :
    YonedaExtension (cokernel E.firstMap) B n where
  obj := (E.obj.δ₀.δ₀).precomp (map E)
  property := property E

/-- The underlying row of the quotient extension is the explicitly precomposed tail. -/
@[simp, stacks 06XU]
theorem obj_row {n : ℕ+} (E : YonedaExtension A B (n + 1)) :
    (obj E).obj = (E.obj.δ₀.δ₀).precomp (map E) := rfl

/-- The first map of the quotient extension is the descended cokernel map. -/
@[simp, stacks 06XU]
theorem obj_firstMap {n : ℕ+} (E : YonedaExtension A B (n + 1)) :
    (obj E).firstMap = map E := by
  change 𝟙 _ ≫ map E = map E
  exact Category.id_comp _

/-- The cokernel sequence removed from the head of a positive-degree Yoneda extension is short
exact. -/
@[stacks 06XU]
theorem head {n : ℕ+} (E : YonedaExtension A B (n + 1)) :
    (ShortComplex.cokernelSequence E.firstMap).ShortExact where
  exact := ShortComplex.cokernelSequence_exact E.firstMap
  mono_f := by
    change Mono E.firstMap
    infer_instance

end Quotient

end CategoryTheory.YonedaExtension
