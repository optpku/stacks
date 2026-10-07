module

import StacksCheckRecall
import ReasLib.AlgebraicGeometry.GroupoidScheme.FlatSourceLocus
import ReasLib.AlgebraicGeometry.Scheme.Morphism.SourceLocus.Flat.Counterexample

open AlgebraicGeometry CategoryTheory Limits
open scoped AlgebraicGeometry

universe u

/- Remark 40.6.2 (1): if the source and target maps of a groupoid scheme are flat and locally of
finite presentation, then after any base change the flat source locus is the preimage of an open
in the base-changed object scheme. -/
@[stacks 04LI] #check
  (AlgebraicGeometry.GroupoidScheme.exists_open_preimage_eq_flatSourceLocus :
    ∀ {S U' : Scheme.{u}} (G : GroupoidScheme S) (g : U' ⟶ G.U.left)
      [Flat G.s.left] [LocallyOfFinitePresentation G.s.left]
      [Flat G.t.left] [LocallyOfFinitePresentation G.t.left],
      ∃ W : U'.Opens,
        pullback.fst g G.t.left ⁻¹ᵁ W =
          MorphismProperty.sourceLocus
            (@Flat : MorphismProperty Scheme.{u}) (pullback.snd g G.t.left ≫ G.s.left))

/- Remark 40.6.2 (2): there are a scheme morphism and a point where it is flat, although the point
does not belong to the flat source locus. -/
@[stacks 04LI] #check
  (AlgebraicGeometry.Scheme.Hom.exists_flatAt_not_mem_flatSourceLocus :
    ∃ (X Y : Scheme.{u}) (f : X ⟶ Y) (x : X),
      f.flatAt x ∧ x ∉
        MorphismProperty.sourceLocus (@Flat : MorphismProperty Scheme.{u}) f)
