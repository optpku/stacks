module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Intersection.ProjectionFormula
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry
open CategoryTheory
open scoped AlgebraicGeometry

universe u

/- Lemma 33.45.7: for a morphism of proper schemes over a field, pulling back a family of
invertible modules and intersecting with an integral closed subscheme multiplies the
intersection number on its scheme-theoretic image by the induced function-field degree, or
gives zero when the image dimension drops. -/
@[stacks 0BET] #check
  (AlgebraicGeometry.Scheme.Modules.Intersection.pullbackNumber_eq_imageNumber :
    ∀ {k : Type u} [Field k]
      {X Y : Over (Spec (CommRingCat.of k))} [IsProper X.hom] [IsProper Y.hom]
      (f : Y ⟶ X) (Z : Y.left.IdealSheafData) [IsIntegral Z.subscheme]
      [HasExt (Sheaf (Opens.grothendieckTopology Z.subscheme.carrier) AddCommGrpCat.{u})]
      [HasExt
        (Sheaf
          (Opens.grothendieckTopology
            (Scheme.Hom.image (Z.subschemeι ≫ f.left)).carrier)
          AddCommGrpCat.{u})]
      {d : ℕ} (hZdim : topologicalKrullDim Z.subscheme = d)
      (L : Fin d → X.left.Modules) [∀ j : Fin d, Scheme.Modules.Invertible (L j)],
      AlgebraicGeometry.Scheme.Modules.Intersection.number k Y.hom Z hZdim
          (fun j ↦ (Scheme.Modules.pullback f.left).obj (L j)) =
        if hImageDim :
            topologicalKrullDim (Scheme.Hom.image (Z.subschemeι ≫ f.left)) = d then
          ((Scheme.Hom.toImage (Z.subschemeι ≫ f.left)).inducedFunctionFieldDegree : ℚ) *
            AlgebraicGeometry.Scheme.Modules.Intersection.number
              k X.hom ((Z.subschemeι ≫ f.left).ker) hImageDim L
        else 0)
