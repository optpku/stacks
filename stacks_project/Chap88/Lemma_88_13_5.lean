module

import StacksCheckRecall
public import stacks_project.Chap88.Definition_88_13_4
public import ReasLib.AlgebraicGeometry.FormalAlgebraicSpace.Morphism.Flat

/-!
# Local tests of flatness for locally Noetherian formal algebraic spaces
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.FormalAlgebraicSpace

universe u

/- Lemma 88.13.5: For a morphism of locally Noetherian formal algebraic spaces,
flatness is equivalent to the universal affine étale chart test and to the
affine étale covering tests on the target and on the source. -/
@[stacks 0GCD] #check (AlgebraicGeometry.FormalAlgebraicSpace.Flat.tfae :
  ∀ {S : Scheme.{u}} {X Y : (Over S)ᵒᵖ ⥤ Type u}
    [IsFormalAlgebraicSpace X] [IsFormalAlgebraicSpace Y]
    [IsLocallyNoetherian X] [IsLocallyNoetherian Y] (f : X ⟶ Y),
    List.TFAE [Flat f, Flat.etaleAffineLocally f, Flat.existsCoverOnTarget f,
      Flat.existsCoverOnSource f])
