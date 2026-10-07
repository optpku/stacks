module

public import Mathlib.Tactic.CrossRefAttribute
public import stacks_project.Chap65.Lemma_65_7_3_Pullback
public import stacks_project.Chap69.Lemma_69_12_5_Monoidal
public import stacks_project.Chap71.Lemma_71_14_3_RelativelyAmple
public import stacks_project.Chap73.Definition_73_9_1_FpqcCovering

/-!
# Lemma 74.13.1

Relative ampleness of an invertible module on a morphism of algebraic spaces
is equivalent to relative ampleness of every pullback along an fpqc covering
of the base.
-/

@[expose] public section

open AlgebraicGeometry AlgebraicSpace CategoryTheory Limits MonoidalCategory

noncomputable section

universe u v

namespace AlgebraicGeometry.AlgebraicSpace

/-- Lemma 74.13.1: let `S` be a scheme, let `f : X ⟶ Y` be a morphism of
algebraic spaces over `S`, and let `L` be an invertible `𝒪_X`-module. Let
`family : ι → Over Y` be an `FpqcCovering`. Then `RelativelyAmple f L` if and
only if for every `i`, `((Modules.pullback (pullback.fst f (family i).hom)).obj L)`
is relatively ample on the base change `pullback.snd f (family i).hom`. -/
@[stacks 0D3C]
theorem RelativelyAmple.iff_forall_baseChange_of_fpqcCovering
    {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) (L : X.Modules)
    [isInvertibleObject L] {ι : Type v} (family : ι → Over Y)
    (hfamily : FpqcCovering family) :
    RelativelyAmple f L ↔
      ∀ i : ι, RelativelyAmple (pullback.snd f (family i).hom)
        ((Modules.pullback (pullback.fst f (family i).hom)).obj L) :=
  sorry

/-- Relative ampleness of every pullback of an invertible module along an
fpqc covering of the base implies relative ampleness over the original base. -/
theorem RelativelyAmple.of_forall_baseChange_of_fpqcCovering
    {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) (L : X.Modules)
    [isInvertibleObject L] {ι : Type v} (family : ι → Over Y)
    (hfamily : FpqcCovering family)
    (hL : ∀ i : ι, RelativelyAmple (pullback.snd f (family i).hom)
      ((Modules.pullback (pullback.fst f (family i).hom)).obj L)) :
    RelativelyAmple f L :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
