module

public import ReasLib.CategoryTheory.InverseSystem.Positive

@[expose] public section

open CategoryTheory Opposite

universe v u

namespace CategoryTheory.PNatInverseSystem

/-- The order hom on positive natural numbers given by `n ↦ c * n + d`. -/
def affineReindex (c d : ℕ+) : ℕ+ →o ℕ+ where
  toFun := fun n ↦ c * n + d
  monotone' := sorry

/-- Affine reindexing is monotone in both its slope and its offset. -/
theorem affineReindex_mono {c₁ d₁ c₂ d₂ : ℕ+} (hc : c₁ ≤ c₂) (hd : d₁ ≤ d₂) :
    affineReindex c₁ d₁ ≤ affineReindex c₂ d₂ := sorry

/-- A linear morphism presentation between positive inverse systems consists of positive affine
reindexing coefficients and a compatible natural transformation from the reindexed source. -/
structure LinearHom {C : Type u} [Category.{v} C] (A B : PNatInverseSystem C) where
  /-- The slope of the affine source index. -/
  slope : ℕ+
  /-- The offset of the affine source index. -/
  offset : ℕ+
  /-- The compatible family of component morphisms. -/
  hom : ((affineReindex slope offset).dual.toFunctor ⋙ A) ⟶ B

namespace LinearHom

variable {C : Type u} [Category.{v} C] {A B : PNatInverseSystem C}

/-- Construct a linear morphism presentation from its affine coefficients and compatible natural
transformation. -/
def of (c d : ℕ+) (f : ((affineReindex c d).dual.toFunctor ⋙ A) ⟶ B) :
    LinearHom A B where
  slope := c
  offset := d
  hom := f

/-- Two linear morphism presentations are equivalent when their induced maps agree after a common
affine refinement whose coefficients bound those of both presentations. -/
def Equivalent (f g : LinearHom A B) : Prop :=
  ∃ (c d : ℕ+)
      (hc : max f.slope g.slope ≤ c) (hd : max f.offset g.offset ≤ d),
    ∀ n : OrderDual ℕ+,
      A.map (homOfLE (OrderDual.toDual_le_toDual.mpr
        ((affineReindex_mono ((le_max_left _ _).trans hc)
          ((le_max_left _ _).trans hd)) n.ofDual))) ≫ f.hom.app n =
        A.map (homOfLE (OrderDual.toDual_le_toDual.mpr
          ((affineReindex_mono ((le_max_right _ _).trans hc)
            ((le_max_right _ _).trans hd)) n.ofDual))) ≫ g.hom.app n

/-- Equivalence of linear morphism presentations is precisely agreement after a common affine
refinement with coefficientwise upper bounds. -/
theorem equivalent_iff (f g : LinearHom A B) :
    Equivalent f g ↔
      ∃ (c d : ℕ+)
          (hc : max f.slope g.slope ≤ c) (hd : max f.offset g.offset ≤ d),
        ∀ n : OrderDual ℕ+,
          A.map (homOfLE (OrderDual.toDual_le_toDual.mpr
            ((affineReindex_mono ((le_max_left _ _).trans hc)
              ((le_max_left _ _).trans hd)) n.ofDual))) ≫ f.hom.app n =
            A.map (homOfLE (OrderDual.toDual_le_toDual.mpr
              ((affineReindex_mono ((le_max_right _ _).trans hc)
                ((le_max_right _ _).trans hd)) n.ofDual))) ≫ g.hom.app n := sorry

end LinearHom

end CategoryTheory.PNatInverseSystem
