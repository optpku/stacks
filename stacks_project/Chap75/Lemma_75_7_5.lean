module

public import stacks_project.Chap75.Lemma_75_7_5_Mapping
import StacksCheckRecall

@[expose] public section

open CategoryTheory

universe u

/- Lemma 75.7.5 (1): if `X` and `Y` are locally of finite type over `B`,
`f : X ⟶ Y` is a morphism over `B`, `Y` is separated over `B`, and `T ⊆ Points X` is
closed and proper over `B`, then `Points.map f '' T` is closed in `Points Y`. -/
@[stacks 0CZG] #check
  (AlgebraicGeometry.AlgebraicSpace.ClosedSubset.image_isClosed_of_isSeparated :
    ∀ {S : AlgebraicGeometry.Scheme.{u}} {X Y B : AlgebraicGeometry.AlgebraicSpace S}
      (pX : X ⟶ B) (pY : Y ⟶ B) (f : X ⟶ Y) (hcomm : f ≫ pY = pX)
      [AlgebraicGeometry.AlgebraicSpace.LocallyOfFiniteType pX]
      [AlgebraicGeometry.AlgebraicSpace.LocallyOfFiniteType pY]
      [AlgebraicGeometry.AlgebraicSpace.Separated pY]
      (T : TopologicalSpace.Closeds (AlgebraicGeometry.AlgebraicSpace.Points X))
      [AlgebraicGeometry.AlgebraicSpace.ClosedSubset.IsProperOver pX T],
      IsClosed (AlgebraicGeometry.AlgebraicSpace.Points.map f ''
        (T : Set (AlgebraicGeometry.AlgebraicSpace.Points X))))

/- Lemma 75.7.5 (2): under the same hypotheses, the exact closed image
`Points.map f '' T` is proper over `B`. -/
@[stacks 0CZG] #check
  (AlgebraicGeometry.AlgebraicSpace.ClosedSubset.IsProperOver.image_of_isSeparated :
    ∀ {S : AlgebraicGeometry.Scheme.{u}} {X Y B : AlgebraicGeometry.AlgebraicSpace S}
      (pX : X ⟶ B) (pY : Y ⟶ B) (f : X ⟶ Y) (hcomm : f ≫ pY = pX)
      [AlgebraicGeometry.AlgebraicSpace.LocallyOfFiniteType pX]
      [AlgebraicGeometry.AlgebraicSpace.LocallyOfFiniteType pY]
      [AlgebraicGeometry.AlgebraicSpace.Separated pY]
      (T : TopologicalSpace.Closeds (AlgebraicGeometry.AlgebraicSpace.Points X))
      [AlgebraicGeometry.AlgebraicSpace.ClosedSubset.IsProperOver pX T],
      AlgebraicGeometry.AlgebraicSpace.ClosedSubset.IsProperOver pY
        (⟨AlgebraicGeometry.AlgebraicSpace.Points.map f ''
            (T : Set (AlgebraicGeometry.AlgebraicSpace.Points X)),
          AlgebraicGeometry.AlgebraicSpace.ClosedSubset.image_isClosed_of_isSeparated
            pX pY f hcomm T⟩ :
          TopologicalSpace.Closeds (AlgebraicGeometry.AlgebraicSpace.Points Y)))

/- Lemma 75.7.5 (3): if `f` is universally closed over `B` and `T ⊆ Points X` is
closed and proper over `B`, then the exact closed image `Points.map f '' T` is
proper over `B`. -/
@[stacks 0CZG] #check
  (AlgebraicGeometry.AlgebraicSpace.ClosedSubset.IsProperOver.image_of_universallyClosed :
    ∀ {S : AlgebraicGeometry.Scheme.{u}} {X Y B : AlgebraicGeometry.AlgebraicSpace S}
      (pX : X ⟶ B) (pY : Y ⟶ B) (f : X ⟶ Y) (hcomm : f ≫ pY = pX)
      [AlgebraicGeometry.AlgebraicSpace.LocallyOfFiniteType pX]
      [AlgebraicGeometry.AlgebraicSpace.LocallyOfFiniteType pY]
      [AlgebraicGeometry.AlgebraicSpace.UniversallyClosed f]
      (T : TopologicalSpace.Closeds (AlgebraicGeometry.AlgebraicSpace.Points X))
      [AlgebraicGeometry.AlgebraicSpace.ClosedSubset.IsProperOver pX T],
      AlgebraicGeometry.AlgebraicSpace.ClosedSubset.IsProperOver pY
        (⟨AlgebraicGeometry.AlgebraicSpace.Points.map f ''
            (T : Set (AlgebraicGeometry.AlgebraicSpace.Points X)),
          AlgebraicGeometry.AlgebraicSpace.ClosedSubset.isClosed_image_of_universallyClosed
            f T⟩ :
          TopologicalSpace.Closeds (AlgebraicGeometry.AlgebraicSpace.Points Y)))

/- Lemma 75.7.5 (4): if `f : X ⟶ Y` is proper over `B` and `T ⊆ Points Y` is
closed and proper over `B`, then its exact inverse image is proper over `B`. -/
@[stacks 0CZG] #check
  (AlgebraicGeometry.AlgebraicSpace.ClosedSubset.IsProperOver.preimage_of_isProper :
    ∀ {S : AlgebraicGeometry.Scheme.{u}} {X Y B : AlgebraicGeometry.AlgebraicSpace S}
      (pX : X ⟶ B) (pY : Y ⟶ B) (f : X ⟶ Y) (hcomm : f ≫ pY = pX)
      [AlgebraicGeometry.AlgebraicSpace.LocallyOfFiniteType pX]
      [AlgebraicGeometry.AlgebraicSpace.LocallyOfFiniteType pY]
      [AlgebraicGeometry.AlgebraicSpace.Proper f]
      (T : TopologicalSpace.Closeds (AlgebraicGeometry.AlgebraicSpace.Points Y))
      [AlgebraicGeometry.AlgebraicSpace.ClosedSubset.IsProperOver pY T],
      AlgebraicGeometry.AlgebraicSpace.ClosedSubset.IsProperOver pX
        (T.preimage (AlgebraicGeometry.AlgebraicSpace.Points.continuous_map f)))
