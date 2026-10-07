module

public import stacks_project.Chap67.Lemma_67_28_11_LocallyOfFinitePresentation
public import stacks_project.Chap67.Lemma_67_30_5_Flat
public import stacks_project.Chap67.Lemma_67_37_4_Smooth
public import stacks_project.Chap74.Lemma_74_7_1_InverseImage
public import stacks_project.Chap100.Lemma_100_9_18_SourceLocus

/-!
# Flat source opens versus the pointwise flat locus

Lemma 100.9.18 applies with `P = Flat`, `Q = ⊤` (the empty condition), and
`R = Flat ⊓ LocallyOfFinitePresentation`. For a morphism of algebraic spaces
the largest open source subspace on which the restriction is flat need not
coincide with the set of points at which the morphism is flat.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits MorphismProperty
open AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- Remark 100.9.19 (1): Lemma 100.9.18 applies with `P = (@Flat S)`, `Q = ⊤`
(the empty condition), and `R = (@Flat S ⊓ @LocallyOfFinitePresentation S)`.
Thus every morphism `f : X ⟶ Y` of algebraic spaces has a largest open source
subspace `W` such that `W.ι ≫ f` is flat. -/
@[stacks 06M4]
theorem exists_isLargestSourceOpen_flat {S : Scheme.{u}}
    {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    ∃ W : OpenSubspace X, IsLargestSourceOpen (@Flat S) f W :=
  sorry

/-- Remark 100.9.19 (2): given a morphism of algebraic spaces `f : X ⟶ Y`, the
largest open subspace `W ⊂ X` such that `W.ι ≫ f` is flat is not, in general,
the set of points at which `f` is flat. -/
@[stacks 06M4]
theorem exists_isLargestSourceOpen_flat_pointsSet_ne_flatAt :
    ∃ (S : Scheme.{u}) (X Y : AlgebraicSpace S) (f : X ⟶ Y)
      (W : OpenSubspace X),
      IsLargestSourceOpen (@Flat S) f W ∧
        W.pointsSet ≠ {x | FlatAt f x} :=
  sorry

/-- Smooth morphisms of algebraic spaces are flat and locally of finite
presentation. -/
theorem smooth_le_flat_inf_locallyOfFinitePresentation {S : Scheme.{u}} :
    (@Smooth S : MorphismProperty (AlgebraicSpace S)) ≤
      (@Flat S ⊓ @LocallyOfFinitePresentation S :
        MorphismProperty (AlgebraicSpace S)) :=
  sorry

/-- The largest open source subspace on which `f` is flat is stable under base
change along morphisms that are flat and locally of finite presentation. -/
theorem isLargestSourceOpen_flat_pullback {S : Scheme.{u}}
    {X Y Y' : AlgebraicSpace S} (f : X ⟶ Y) (g : Y' ⟶ Y)
    [Flat g] [LocallyOfFinitePresentation g] (W : OpenSubspace X)
    (hW : IsLargestSourceOpen (@Flat S) f W) :
    IsLargestSourceOpen (@Flat S) (pullback.snd f g)
      (W.inverseImage (pullback.fst f g)) :=
  sorry

/-- If `W` is a largest open source subspace on which `f` is flat, then every
point of `W` is a point at which `f` is flat. -/
theorem isLargestSourceOpen_flat_pointsSet_subset_flatAt
    {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) (W : OpenSubspace X)
    (hW : IsLargestSourceOpen (@Flat S) f W) :
    W.pointsSet ⊆ {x | FlatAt f x} :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
