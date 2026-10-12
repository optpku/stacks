/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.InverseSystem.Positive.Linear
import StacksCheckRecall

universe v u

open CategoryTheory

variable {C : Type u} [Category.{v} C]

/- Remark 48.30.6: linear pro-morphisms between positive inverse systems are compatible families
indexed by positive affine reindexings. -/
@[stacks 0G4P] #check
  (CategoryTheory.PNatInverseSystem.LinearHom :
    CategoryTheory.PNatInverseSystem C → CategoryTheory.PNatInverseSystem C → Type v)

#check
  (CategoryTheory.PNatInverseSystem.LinearHom.equivalent_iff :
    ∀ {A B : CategoryTheory.PNatInverseSystem C}
        (f g : CategoryTheory.PNatInverseSystem.LinearHom A B),
      CategoryTheory.PNatInverseSystem.LinearHom.Equivalent f g ↔
        ∃ (c d : ℕ+)
            (hc : max f.slope g.slope ≤ c) (hd : max f.offset g.offset ≤ d),
          ∀ n : OrderDual ℕ+,
            A.map (homOfLE (OrderDual.toDual_le_toDual.mpr
              ((CategoryTheory.PNatInverseSystem.affineReindex_mono
                ((le_max_left _ _).trans hc)
                ((le_max_left _ _).trans hd)) n.ofDual))) ≫ f.hom.app n =
              A.map (homOfLE (OrderDual.toDual_le_toDual.mpr
                ((CategoryTheory.PNatInverseSystem.affineReindex_mono
                  ((le_max_right _ _).trans hc)
                  ((le_max_right _ _).trans hd)) n.ofDual))) ≫ g.hom.app n)
