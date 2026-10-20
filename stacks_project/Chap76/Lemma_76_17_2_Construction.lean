module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.Deformation.Perturbation.Construction

@[expose] public section

open CategoryTheory Opposite AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open CategoryTheory.Limits

noncomputable section

universe u

/- Lemma 76.17.2: The scheme-chart perturbations glue to an algebraic-space morphism. -/
#check (AlgebraicGeometry.AlgebraicSpace.Hom.Deformation.perturbHom :
  ∀ {S : Scheme.{u}} {B X X' Y Y' : AlgebraicSpace S}
    (iX : X ⟶ X') (iY : Y ⟶ Y') (a : X ⟶ Y) (a' : X' ⟶ Y')
    [IsFirstOrderThickening iX] [IsFirstOrderThickening iY]
    (sqA : CommSq a iX iY a') (p : Y ⟶ B)
    (θ : (Modules.pullback a).obj (Hom.relativeDifferentials p) ⟶ Hom.conormalSheaf iX),
    X' ⟶ Y')
