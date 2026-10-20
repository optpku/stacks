module

public import ReasLib.CategoryTheory.Sites.AbelianSheaf.Derived
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Proetale.Abelian

/-! Typed compatibility checks for abelian pro-étale inverse image. -/

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.Scheme
open CategoryTheory CategoryTheory.Limits

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.ProEt

#check (AlgebraicGeometry.Scheme.ProEt.smallInverseImage :
  ∀ {S T : Scheme.{u}} (f : T ⟶ S)
    [HasSheafify (topology S) AddCommGrpCat.{u + 1}]
    [HasSheafify (topology T) AddCommGrpCat.{u + 1}]
    [∀ P : S.ProEtᵒᵖ ⥤ AddCommGrpCat.{u + 1},
      (smallProetalePullback f).op.HasLeftKanExtension P],
    Sheaf (topology S) AddCommGrpCat.{u + 1} ⥤
      Sheaf (topology T) AddCommGrpCat.{u + 1})

#check (AlgebraicGeometry.Scheme.ProEt.smallInverseImage_eq :
  ∀ {S T : Scheme.{u}} (f : T ⟶ S)
    [HasSheafify (topology S) AddCommGrpCat.{u + 1}]
    [HasSheafify (topology T) AddCommGrpCat.{u + 1}]
    [∀ P : S.ProEtᵒᵖ ⥤ AddCommGrpCat.{u + 1},
      (smallProetalePullback f).op.HasLeftKanExtension P],
    smallInverseImage f =
      (smallProetalePullback f).sheafPullback AddCommGrpCat.{u + 1}
        (topology S) (topology T))

#check (AlgebraicGeometry.Scheme.ProEt.smallInverseImage_preservesFiniteLimits :
  ∀ {S T : Scheme.{u}} (f : T ⟶ S)
    [HasSheafify (topology S) AddCommGrpCat.{u + 1}]
    [HasSheafify (topology T) AddCommGrpCat.{u + 1}]
    [∀ P : S.ProEtᵒᵖ ⥤ AddCommGrpCat.{u + 1},
      (smallProetalePullback f).op.HasLeftKanExtension P],
    PreservesFiniteLimits (smallInverseImage f))

#check (AlgebraicGeometry.Scheme.ProEt.smallInverseImage_preservesFiniteColimits :
  ∀ {S T : Scheme.{u}} (f : T ⟶ S)
    [HasSheafify (topology S) AddCommGrpCat.{u + 1}]
    [HasSheafify (topology T) AddCommGrpCat.{u + 1}]
    [∀ P : S.ProEtᵒᵖ ⥤ AddCommGrpCat.{u + 1},
      (smallProetalePullback f).op.HasLeftKanExtension P],
    PreservesFiniteColimits (smallInverseImage f))

#check (AlgebraicGeometry.Scheme.ProEt.iInverseImage_preservesFiniteLimits :
  ∀ {S T : Scheme.{u}} (f : T ⟶ S)
    [HasSheafify (topology T) AddCommGrpCat.{u + 1}]
    [HasSheafify (proetaleTopology.over S) AddCommGrpCat.{u + 1}],
    PreservesFiniteLimits (iInverseImage f))

#check (AlgebraicGeometry.Scheme.ProEt.iInverseImage_preservesFiniteColimits :
  ∀ {S T : Scheme.{u}} (f : T ⟶ S)
    [HasSheafify (topology T) AddCommGrpCat.{u + 1}]
    [HasSheafify (proetaleTopology.over S) AddCommGrpCat.{u + 1}],
    PreservesFiniteColimits (iInverseImage f))

end AlgebraicGeometry.Scheme.ProEt
