module

public import stacks_project.Chap67.Lemma_67_28_11_LocallyOfFinitePresentation
public import stacks_project.Chap67.Lemma_67_30_5_Flat
public import stacks_project.Chap67.Lemma_67_37_4_Smooth
public import stacks_project.Chap74.Lemma_74_7_1_InverseImage
public import stacks_project.Chap100.Lemma_100_9_18_SourceLocus
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.Flat.SourceLocus
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Smooth.Flat
import StacksCheckRecall

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

#check (AlgebraicGeometry.AlgebraicSpace.exists_isLargestSourceOpen_flat :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y),
    ∃ W : OpenSubspace X,
      Flat (W.ι ≫ f) ∧
        ∀ U : OpenSubspace X, Flat (U.ι ≫ f) → U.pointsSet ⊆ W.pointsSet)

/- Remark 100.9.19: The largest flat source open need not coincide with the
pointwise flat locus. -/
@[stacks 06M4] #check
  (AlgebraicGeometry.AlgebraicSpace.exists_isLargestSourceOpen_flat_pointsSet_ne_flatAt :
    ∃ (S : Scheme.{u}) (X Y : AlgebraicSpace S) (f : X ⟶ Y)
      (W : OpenSubspace X),
      (Flat (W.ι ≫ f) ∧
        ∀ U : OpenSubspace X, Flat (U.ι ≫ f) → U.pointsSet ⊆ W.pointsSet) ∧
        W.pointsSet ≠ {x | FlatAt f x})

-- Smooth morphisms satisfy both conditions required of the base change.
#check (AlgebraicGeometry.AlgebraicSpace.Smooth.flat :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) [Smooth f], Flat f)

#check (AlgebraicGeometry.AlgebraicSpace.locallyOfFinitePresentation_of_smooth :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) [Smooth f],
    LocallyOfFinitePresentation f)

#check (AlgebraicGeometry.AlgebraicSpace.isLargestSourceOpen_flat_pullback :
  ∀ {S : Scheme.{u}} {X Y Y' : AlgebraicSpace S} (f : X ⟶ Y) (g : Y' ⟶ Y)
    [Flat g] [LocallyOfFinitePresentation g] (W : OpenSubspace X)
    (hW : Flat (W.ι ≫ f) ∧
      ∀ U : OpenSubspace X, Flat (U.ι ≫ f) → U.pointsSet ⊆ W.pointsSet),
    Flat ((W.inverseImage (pullback.fst f g)).ι ≫ pullback.snd f g) ∧
      ∀ U : OpenSubspace (pullback f g),
        Flat (U.ι ≫ pullback.snd f g) →
          U.pointsSet ⊆ (W.inverseImage (pullback.fst f g)).pointsSet)

#check (AlgebraicGeometry.AlgebraicSpace.isLargestSourceOpen_flat_pointsSet_subset_flatAt :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) (W : OpenSubspace X)
    (hW : Flat (W.ι ≫ f) ∧
      ∀ U : OpenSubspace X, Flat (U.ι ≫ f) → U.pointsSet ⊆ W.pointsSet),
    W.pointsSet ⊆ {x | FlatAt f x})

end AlgebraicGeometry.AlgebraicSpace
