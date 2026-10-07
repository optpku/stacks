module

public import ReasLib.AlgebraicGeometry.Scheme.ClosedSubscheme.Proper.Mapping
import StacksCheckRecall

@[expose] public section

open CategoryTheory

universe u

/- Lemma 30.26.5 (1), closedness: if `X` and `Y` are locally of finite type over `S`,
`f : X ⟶ Y` is a morphism over `S`, `Y` is separated over `S`, and `Z ⊆ X` is closed and
proper over `S`, then `f(Z)` is closed in `Y`. -/
@[stacks 0CYQ] #check
  (AlgebraicGeometry.ClosedSubset.image_isClosed_of_isSeparated :
    ∀ {S X Y : AlgebraicGeometry.Scheme.{u}} (pX : X ⟶ S) (pY : Y ⟶ S) (f : X ⟶ Y)
      (hcomm : f ≫ pY = pX) [AlgebraicGeometry.LocallyOfFiniteType pX]
      [AlgebraicGeometry.LocallyOfFiniteType pY] [AlgebraicGeometry.IsSeparated pY]
      (Z : TopologicalSpace.Closeds X)
      [AlgebraicGeometry.ClosedSubset.IsProperOver pX Z],
      IsClosed (f '' (Z : Set X)))

/- Lemma 30.26.5 (1), properness: under the same hypotheses, the exact closed image `f(Z)` is
proper over `S`. -/
@[stacks 0CYQ] #check
  (AlgebraicGeometry.ClosedSubset.IsProperOver.image_of_isSeparated :
    ∀ {S X Y : AlgebraicGeometry.Scheme.{u}} (pX : X ⟶ S) (pY : Y ⟶ S) (f : X ⟶ Y)
      (hcomm : f ≫ pY = pX) [AlgebraicGeometry.LocallyOfFiniteType pX]
      [AlgebraicGeometry.LocallyOfFiniteType pY] [AlgebraicGeometry.IsSeparated pY]
      (Z : TopologicalSpace.Closeds X)
      [AlgebraicGeometry.ClosedSubset.IsProperOver pX Z],
      AlgebraicGeometry.ClosedSubset.IsProperOver pY
        (⟨f '' (Z : Set X),
          AlgebraicGeometry.ClosedSubset.image_isClosed_of_isSeparated pX pY f hcomm Z⟩ :
          TopologicalSpace.Closeds Y))

/- Lemma 30.26.5 (2): if `f` is universally closed over `S` and `Z ⊆ X` is closed and proper
over `S`, then the exact closed image `f(Z)` is proper over `S`. -/
@[stacks 0CYQ] #check
  (AlgebraicGeometry.ClosedSubset.IsProperOver.image_of_universallyClosed :
    ∀ {S X Y : AlgebraicGeometry.Scheme.{u}} (pX : X ⟶ S) (pY : Y ⟶ S) (f : X ⟶ Y)
      (hcomm : f ≫ pY = pX) [AlgebraicGeometry.LocallyOfFiniteType pX]
      [AlgebraicGeometry.LocallyOfFiniteType pY] [AlgebraicGeometry.UniversallyClosed f]
      (Z : TopologicalSpace.Closeds X)
      [AlgebraicGeometry.ClosedSubset.IsProperOver pX Z],
      AlgebraicGeometry.ClosedSubset.IsProperOver pY
        (⟨f '' (Z : Set X),
          (AlgebraicGeometry.Scheme.Hom.isClosedMap f) (Z : Set X) Z.2⟩ :
          TopologicalSpace.Closeds Y))

/- Lemma 30.26.5 (3): if `f : X ⟶ Y` is proper over `S` and `Z ⊆ Y` is closed and proper over
`S`, then its exact inverse image is proper over `S`. -/
@[stacks 0CYQ] #check
  (AlgebraicGeometry.ClosedSubset.IsProperOver.preimage_of_isProper :
    ∀ {S X Y : AlgebraicGeometry.Scheme.{u}} (pX : X ⟶ S) (pY : Y ⟶ S) (f : X ⟶ Y)
      (hcomm : f ≫ pY = pX) [AlgebraicGeometry.LocallyOfFiniteType pX]
      [AlgebraicGeometry.LocallyOfFiniteType pY] [AlgebraicGeometry.IsProper f]
      (Z : TopologicalSpace.Closeds Y)
      [AlgebraicGeometry.ClosedSubset.IsProperOver pY Z],
      AlgebraicGeometry.ClosedSubset.IsProperOver pX (Z.preimage f.continuous))
