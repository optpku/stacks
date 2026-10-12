/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Functor.Algebraic.Basic
public import ReasLib.Topology.Sheaves.Basis.Cover

/-!
# Basis sheaves detected by an underlying-type functor

The definition only records the functor used to detect the basis sheaf condition.  Algebraicity
of that functor is required by comparison and extension theorems, not by the category itself.
-/

@[expose] public section

open CategoryTheory TopologicalSpace

universe u v w u1

variable {X : Type u} [TopologicalSpace X]
variable {C : Type v} [Category.{w} C]

/-- The full subcategory of `C`-valued presheaves on `B` whose underlying set-valued
presheaves satisfy the basis-cover sheaf condition. -/
abbrev AlgebraicBasisSheaf (F : C ⥤ Type u1) (B : Set (Opens X)) :=
  ObjectProperty.FullSubcategory fun ℱ : (BasisOpen B)ᵒᵖ ⥤ C ↦
    Presheaf.IsBasisSheaf (ℱ ⋙ F)
