module

public import ReasLib.CategoryTheory.Subobject.Generator
import StacksCheckRecall

@[expose] public section

open CategoryTheory
open CategoryTheory.Subobject.GeneratorBound

universe v u

variable {C : Type u} [Category.{v} C] [Abelian C]
variable {G X : C} (hG : IsSeparator G)

section Chains

variable (κ : Cardinal.{v}) (hκ : Cardinal.mk (G ⟶ X) < κ)

/- Lemma 19.11.1 (1): no strictly increasing chain of subobjects of `X` is indexed by a
cardinal larger than `#(G ⟶ X)`. -/
@[stacks 0E8N] #check
  (noStrictMonoChain hG κ hκ :
    ¬ ∃ S : κ.ord.ToType → Subobject X, StrictMono S)

/- Lemma 19.11.1 (2): no strictly decreasing chain of subobjects of `X` is indexed by a
cardinal larger than `#(G ⟶ X)`. -/
@[stacks 0E8N] #check
  (noStrictAntiChain hG κ hκ :
    ¬ ∃ S : κ.ord.ToType → Subobject X, StrictAnti S)

end Chains

section Monotone

variable (α : Ordinal.{v}) (hα : Cardinal.mk (G ⟶ X) < α.cof)
variable (S : α.ToType → Subobject X) (hS : Monotone S)

/- Lemma 19.11.1 (3): an increasing ordinal-indexed chain whose cofinality exceeds
`#(G ⟶ X)` is eventually constant. -/
@[stacks 0E8N] #check
  (monotoneEventuallyConstant hG α hα S hS :
    ∃ i : α.ToType, ∀ j : α.ToType, i ≤ j → S j = S i)

end Monotone

section Antitone

variable (α : Ordinal.{v}) (hα : Cardinal.mk (G ⟶ X) < α.cof)
variable (S : α.ToType → Subobject X) (hS : Antitone S)

/- Lemma 19.11.1 (4): a decreasing ordinal-indexed chain whose cofinality exceeds
`#(G ⟶ X)` is eventually constant. -/
@[stacks 0E8N] #check
  (antitoneEventuallyConstant hG α hα S hS :
    ∃ i : α.ToType, ∀ j : α.ToType, i ≤ j → S j = S i)

end Antitone

/- Lemma 19.11.1 (5): `#(Subobject X) ≤ 2 ^ #(G ⟶ X)`, with the required universe lift
made explicit by the canonical cardinal expression. -/
@[stacks 0E8N] #check
  (Subobject.GeneratorBound.mk_le (X := X) hG :
    Cardinal.mk (Subobject X) ≤ 2 ^ Cardinal.lift (Cardinal.mk (G ⟶ X)))
