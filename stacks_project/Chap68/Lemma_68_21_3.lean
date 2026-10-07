module

public import Mathlib.Data.List.TFAE
public import stacks_project.Chap66.Lemma_66_10_3_LocalRingDim
public import stacks_project.Chap67.Definition_67_27_1_QuasiFinite

/-!
# Quasi-finiteness over a codimension-zero point

For a locally finite type morphism of algebraic spaces, the fibre over a
codimension-zero point of the target consists of codimension-zero points of
the source if and only if the morphism is quasi-finite at every point of that
fibre, equivalently at every codimension-zero point of the fibre.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- Lemma 68.21.3: Let `S` be a scheme. Let `f : X ⟶ Y` be a morphism of
algebraic spaces over `S`. Assume `f` is locally of finite type. Let `X⁰ ⊂ |X|`
and `Y⁰ ⊂ |Y|` denote the sets of codimension `0` points of `X` and of `Y`.
Let `y ∈ Y⁰`. The following are equivalent: `f⁻¹({y}) ⊂ X⁰`; `f` is
quasi-finite at all points lying over `y`; `f` is quasi-finite at all
`x ∈ X⁰` lying over `y`.

Here `|X|` and `|Y|` are `Points X` and `Points Y`, `|f|` is `Points.map f`,
a point of codimension `0` means `localRingDimAt _ = 0`, and quasi-finiteness
at a point is `FiniteType.QuasiFiniteAt`. -/
@[stacks 0BBB]
theorem tfae_fiber_subset_codimZero_quasiFiniteAt {S : Scheme.{u}}
    {X Y : AlgebraicSpace S} (f : X ⟶ Y) [LocallyOfFiniteType f]
    {y : Points Y} (hy : localRingDimAt y = 0) :
    List.TFAE
      [ Points.map f ⁻¹' {y} ⊆ setOf fun x : Points X ↦ localRingDimAt x = 0
      , ∀ x : Points X, Points.map f x = y → FiniteType.QuasiFiniteAt f x
      , ∀ x : Points X,
          localRingDimAt x = 0 → Points.map f x = y → FiniteType.QuasiFiniteAt f x ] :=
  sorry

/-- For a locally finite type morphism of algebraic spaces, the fibre over a
codimension-zero point of the target consists of codimension-zero points of
the source if and only if the morphism is quasi-finite at every point of that
fibre. -/
theorem fiber_subset_codimZero_iff_quasiFiniteAt {S : Scheme.{u}}
    {X Y : AlgebraicSpace S} (f : X ⟶ Y) [LocallyOfFiniteType f]
    {y : Points Y} (hy : localRingDimAt y = 0) :
    Points.map f ⁻¹' {y} ⊆ setOf fun x : Points X ↦ localRingDimAt x = 0 ↔
      ∀ x : Points X, Points.map f x = y → FiniteType.QuasiFiniteAt f x :=
  sorry

/-- For a locally finite type morphism of algebraic spaces, quasi-finiteness at
every point over a codimension-zero point of the target is equivalent to
quasi-finiteness at every codimension-zero point of the source over that
point. -/
theorem quasiFiniteAt_fiber_iff_quasiFiniteAt_codimZero {S : Scheme.{u}}
    {X Y : AlgebraicSpace S} (f : X ⟶ Y) [LocallyOfFiniteType f]
    {y : Points Y} (hy : localRingDimAt y = 0) :
    (∀ x : Points X, Points.map f x = y → FiniteType.QuasiFiniteAt f x) ↔
      ∀ x : Points X,
        localRingDimAt x = 0 → Points.map f x = y → FiniteType.QuasiFiniteAt f x :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
