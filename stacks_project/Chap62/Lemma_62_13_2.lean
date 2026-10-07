module

public import stacks_project.Chap62.Lemma_62_11_2_Restrict
public import stacks_project.Chap62.Lemma_62_13_1_Comp
public import stacks_project.Chap62.Lemma_62_13_2_Comp
import Mathlib.Tactic.CrossRefAttribute

/-!
# Open restriction of composition of families of cycles on fibres

This file records that forming the composite family `α ∘ β` commutes with
restriction to compatible opens of the source and of the intermediate scheme.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Hom
namespace CyclesOnFibers

/-- The two presentations of `U ⟶ S` obtained from `f(U) ⊂ V` agree. -/
theorem comp_restrict_hom_eq {S X Y : Scheme.{u}} (p : Y ⟶ S) (f : X ⟶ Y)
    (U : X.Opens) (V : Y.Opens) (hUV : U ≤ f ⁻¹ᵁ V) :
    f.resLE V U hUV ≫ V.ι ≫ p = U.ι ≫ f ≫ p := sorry

/-- The identity-triangle fibre map comparing the two presentations of
`U ⟶ S`. -/
noncomputable def compRestrictFiberMap {S X Y : Scheme.{u}} (p : Y ⟶ S)
    (f : X ⟶ Y) (U : X.Opens) (V : Y.Opens) (hUV : U ≤ f ⁻¹ᵁ V) (s : S) :
    (U.ι ≫ f ≫ p).fiber s ⟶ (f.resLE V U hUV ≫ V.ι ≫ p).fiber s :=
  idTriangleFiberMap (𝟙 _) (comp_restrict_hom_eq p f U V hUV) s

/-- Lemma 62.13.2: If `U ⊂ X` and `V ⊂ Y` are open and `f(U) ⊂ V`, then
`(α ∘ β)|_U` is equal to `α|_U ∘ β|_V`. -/
@[stacks 0H6J]
theorem comp_restrict {S X Y : Scheme.{u}} (p : Y ⟶ S) (f : X ⟶ Y)
    [LocallyOfFiniteType p] [LocallyOfFiniteType f] {r e : ℤ}
    (α : CyclesOnFibers f r) (β : CyclesOnFibers p e) (U : X.Opens)
    (V : Y.Opens) (hUV : U ≤ f ⁻¹ᵁ V) (s : S)
    (x : (U.ι ≫ f ≫ p).fiber s) :
    toAlgebraicCycle (restrictOver (comp α β) U) s x =
      toAlgebraicCycle
        (comp (restrict α U V hUV) (restrictOver β V))
        s (compRestrictFiberMap p f U V hUV s x) := sorry

end CyclesOnFibers
end AlgebraicGeometry.Scheme.Hom
