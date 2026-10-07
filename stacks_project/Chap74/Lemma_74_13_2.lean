module

public import Mathlib.Tactic.CrossRefAttribute
public import stacks_project.Chap65.Definition_65_12_1_Subspace
public import stacks_project.Chap65.Lemma_65_7_3_Pullback
public import stacks_project.Chap67.Definition_67_40_1_Proper
public import stacks_project.Chap69.Lemma_69_12_5_Monoidal
public import stacks_project.Chap71.Lemma_71_14_3_RelativelyAmple

/-!
# Lemma 74.13.2

A proper morphism of algebraic spaces and an invertible module on the source
admit an open subspace of the target through which a test morphism factors
if and only if the pulled-back module is relatively ample on the base change.
-/

@[expose] public section

open AlgebraicGeometry AlgebraicSpace CategoryTheory Limits MonoidalCategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- Lemma 74.13.2: let `S` be a scheme, let `f : X ⟶ Y` be a proper morphism of
algebraic spaces over `S`, and let `L` be an invertible `𝒪_X`-module. There
exists an open subspace `V ⊂ Y` such that a morphism `g : Y' ⟶ Y` of algebraic
spaces factors through `V` if and only if the pullback of `L` to
`X' = Y' ×_Y X` is relatively ample on `X'/Y'` in the sense of
`RelativelyAmple`. -/
@[stacks 0D3D]
theorem RelativelyAmple.exists_openSubspace_factorsThrough_iff
    {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) [Proper f]
    (L : X.Modules) [isInvertibleObject L] :
    ∃ V : OpenSubspace Y, ∀ {Y' : AlgebraicSpace S} (g : Y' ⟶ Y),
      (∃ χ : Y' ⟶ V.X, χ ≫ V.ι = g) ↔
        RelativelyAmple (pullback.snd f g) ((Modules.pullback (pullback.fst f g)).obj L) :=
  sorry

/-- An open subspace of `Y` characterized by relative ampleness of pullbacks of
`L` is unique as a subobject of `Y`. -/
theorem RelativelyAmple.openSubspace_unique
    {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) [Proper f]
    (L : X.Modules) [isInvertibleObject L] (V W : OpenSubspace Y)
    (hV : ∀ {Y' : AlgebraicSpace S} (g : Y' ⟶ Y),
      (∃ χ : Y' ⟶ V.X, χ ≫ V.ι = g) ↔
        RelativelyAmple (pullback.snd f g) ((Modules.pullback (pullback.fst f g)).obj L))
    (hW : ∀ {Y' : AlgebraicSpace S} (g : Y' ⟶ Y),
      (∃ χ : Y' ⟶ W.X, χ ≫ W.ι = g) ↔
        RelativelyAmple (pullback.snd f g) ((Modules.pullback (pullback.fst f g)).obj L)) :
    ∃! χ : V.X ⟶ W.X, χ ≫ W.ι = V.ι :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
