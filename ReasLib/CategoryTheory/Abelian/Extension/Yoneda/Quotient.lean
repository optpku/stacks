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
theorem one_two : (1 : ℕ) ≤ 2 := sorry

/-- A degree-`n + 1` Yoneda row contains its second nontrivial object. -/
theorem two_length (n : ℕ+) : (2 : ℕ) ≤ ((n + 1 : ℕ+) : ℕ) := sorry

end Index

/-- The arrow following the first map of a positive-degree Yoneda extension. -/
abbrev next {n : ℕ+} (E : YonedaExtension A B (n + 1)) :
    E.obj.obj' 1 ⟶ E.obj.obj' 2 (Index.two_length (n + 1)) :=
  E.obj.map' 1 2 Index.one_two (Index.two_length (n + 1))

/-- The first two maps of a positive-degree Yoneda extension compose to zero. -/
theorem firstMap_comp_next {n : ℕ+} (E : YonedaExtension A B (n + 1)) :
    E.firstMap ≫ next E = 0 := sorry

/-- The map from the cokernel of the first arrow to the next object in the extension. -/
@[stacks 06XU]
noncomputable def map {n : ℕ+} (E : YonedaExtension A B (n + 1)) :
    cokernel E.firstMap ⟶ E.obj.obj' 2 (Index.two_length (n + 1)) :=
  cokernel.desc E.firstMap (next E) (firstMap_comp_next E)

/-- The quotient projection followed by `map E` recovers the second arrow of `E`. -/
@[reassoc (attr := simp), stacks 06XU]
theorem π_comp_map {n : ℕ+} (E : YonedaExtension A B (n + 1)) :
    cokernel.π E.firstMap ≫ map E = next E := sorry

/-- The descended quotient map carries its canonical monomorphism instance. -/
noncomputable instance mapMono {n : ℕ+} (E : YonedaExtension A B (n + 1)) :
    Mono (map E) := sorry

/-- The composable row obtained by deleting the first two objects and prepending the descended
quotient map is again exact. -/
theorem row_exact {n : ℕ+} (E : YonedaExtension A B (n + 1)) :
    ((E.obj.δ₀.δ₀).precomp (map E)).Exact := sorry

/-- The quotient row has the defining endpoint, exactness, and outer mono/epi properties of a
degree-`n` Yoneda extension. -/
theorem property {n : ℕ+} (E : YonedaExtension A B (n + 1)) :
    IsYonedaExtension (cokernel E.firstMap) B n ((E.obj.δ₀.δ₀).precomp (map E)) := sorry

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
    (obj E).obj = (E.obj.δ₀.δ₀).precomp (map E) := sorry

/-- The first map of the quotient extension is the descended cokernel map. -/
@[simp, stacks 06XU]
theorem obj_firstMap {n : ℕ+} (E : YonedaExtension A B (n + 1)) :
    (obj E).firstMap = map E := sorry

/-- The cokernel sequence removed from the head of a positive-degree Yoneda extension is short
exact. -/
@[stacks 06XU]
theorem head {n : ℕ+} (E : YonedaExtension A B (n + 1)) :
    (ShortComplex.cokernelSequence E.firstMap).ShortExact := sorry

end Quotient

end CategoryTheory.YonedaExtension
