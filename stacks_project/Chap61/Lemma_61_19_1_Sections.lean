module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.ProEtaleSections

@[expose] public section

open CategoryTheory Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe u

variable {X : Scheme.{u}}
variable [∀ Y : Scheme.{u}, HasSheafify Y.smallEtaleTopology (Type (u + 1))]
variable [∀ (Y Z : Scheme.{u}) (f : Y ⟶ Z),
  ∀ P : Z.Etaleᵒᵖ ⥤ Type (u + 1),
    (smallEtalePullback f).op.HasLeftKanExtension P]

#check (AlgebraicGeometry.Scheme.etalePullbackGamma :
  Sheaf X.smallEtaleTopology (Type (u + 1)) → X.ProEtᵒᵖ ⥤ Type (u + 1))
#check (AlgebraicGeometry.Scheme.etalePullbackGamma_obj :
  ∀ (F : Sheaf X.smallEtaleTopology (Type (u + 1))) (Y : X.ProEt),
    (etalePullbackGamma F).obj (op Y) = etalePullbackGammaObj F Y)
