module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Flat
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.OpenSubspace.InverseImage
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.LocallyOfFinitePresentation

/-!
# Largest flat source opens

The largest open restriction on which a morphism is flat is contained in its
pointwise flat locus, but these point sets need not coincide.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- Every morphism of algebraic spaces has a largest open source subspace on
which its restriction is flat. -/
theorem exists_isLargestSourceOpen_flat {S : Scheme.{u}}
    {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    ∃ W : OpenSubspace X,
      Flat (W.ι ≫ f) ∧
        ∀ U : OpenSubspace X, Flat (U.ι ≫ f) → U.pointsSet ⊆ W.pointsSet :=
  sorry

/-- There is a morphism of algebraic spaces whose largest flat source open
does not have the same point set as its pointwise flat locus. -/
theorem exists_isLargestSourceOpen_flat_pointsSet_ne_flatAt :
    ∃ (S : Scheme.{u}) (X Y : AlgebraicSpace S) (f : X ⟶ Y)
      (W : OpenSubspace X),
      (Flat (W.ι ≫ f) ∧
        ∀ U : OpenSubspace X, Flat (U.ι ≫ f) → U.pointsSet ⊆ W.pointsSet) ∧
        W.pointsSet ≠ {x | FlatAt f x} :=
  sorry

/-- The largest flat source open is preserved by base change along a flat
morphism that is locally of finite presentation. -/
theorem isLargestSourceOpen_flat_pullback {S : Scheme.{u}}
    {X Y Y' : AlgebraicSpace S} (f : X ⟶ Y) (g : Y' ⟶ Y)
    [Flat g] [LocallyOfFinitePresentation g] (W : OpenSubspace X)
    (hW : Flat (W.ι ≫ f) ∧
      ∀ U : OpenSubspace X, Flat (U.ι ≫ f) → U.pointsSet ⊆ W.pointsSet) :
    Flat ((W.inverseImage (pullback.fst f g)).ι ≫ pullback.snd f g) ∧
      ∀ U : OpenSubspace (pullback f g),
        Flat (U.ι ≫ pullback.snd f g) →
          U.pointsSet ⊆ (W.inverseImage (pullback.fst f g)).pointsSet :=
  sorry

/-- Every point of a largest flat source open belongs to the pointwise flat
locus of the morphism. -/
theorem isLargestSourceOpen_flat_pointsSet_subset_flatAt
    {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) (W : OpenSubspace X)
    (hW : Flat (W.ι ≫ f) ∧
      ∀ U : OpenSubspace X, Flat (U.ι ≫ f) → U.pointsSet ⊆ W.pointsSet) :
    W.pointsSet ⊆ {x | FlatAt f x} :=
  sorry

/-- A morphism of algebraic spaces that is locally of finite presentation has a
largest flat open source subspace, whose points are exactly its pointwise flat locus. -/
theorem exists_isLargestSourceOpen_flat_of_locallyOfFinitePresentation
    {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [LocallyOfFinitePresentation f] :
    ∃ W : OpenSubspace X,
      (Flat (W.ι ≫ f) ∧
      ∀ U : OpenSubspace X, Flat (U.ι ≫ f) →
        U.pointsSet ⊆ W.pointsSet) ∧ W.pointsSet = {x | FlatAt f x} :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
