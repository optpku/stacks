module

public import Mathlib.Tactic.CrossRefAttribute
public import stacks_project.Chap67.Definition_67_8_2_QuasiCompact
public import stacks_project.Chap67.Definition_67_4_2_Separation
public import stacks_project.Chap71.Lemma_71_14_3_RelativelyAmple

/-!
# Lemma 71.14.4

Existence of an `f`-ample invertible sheaf on a morphism of algebraic spaces
implies that the morphism is representable, quasi-compact, and separated.
-/

@[expose] public section

open AlgebraicGeometry AlgebraicSpace CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- Lemma 71.14.4 (1): let `S` be a scheme and let `f : X ⟶ Y` be a morphism of
algebraic spaces over `S`. If there exists an `f`-ample invertible sheaf `L`,
then `f` is representable. -/
@[stacks 0D34]
theorem RelativelyAmple.relativelyRepresentable {S : Scheme.{u}}
    {X Y : AlgebraicSpace S} (f : X ⟶ Y) (L : X.Modules)
    [RelativelyAmple f L] : yoneda.relativelyRepresentable f :=
  sorry

/-- Lemma 71.14.4 (2): let `S` be a scheme and let `f : X ⟶ Y` be a morphism of
algebraic spaces over `S`. If there exists an `f`-ample invertible sheaf `L`,
then `f` is quasi-compact. -/
@[stacks 0D34]
theorem RelativelyAmple.quasiCompact {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) (L : X.Modules) [RelativelyAmple f L] : QuasiCompact f :=
  sorry

/-- Lemma 71.14.4 (3): let `S` be a scheme and let `f : X ⟶ Y` be a morphism of
algebraic spaces over `S`. If there exists an `f`-ample invertible sheaf `L`,
then `f` is separated. -/
@[stacks 0D34]
theorem RelativelyAmple.separated {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) (L : X.Modules) [RelativelyAmple f L] : Separated f :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
