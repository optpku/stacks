module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.GeometricPointSections

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme

universe u

#check (AlgebraicGeometry.Scheme.Etale.stalkFunctor :
  ∀ {S : Scheme.{u}} (s : GeometricPoint S), Sheaf S.smallEtaleTopology (Type u) ⥤ Type u)

#check (AlgebraicGeometry.Scheme.Etale.stalkFunctor_obj :
  ∀ {S : Scheme.{u}} (s : GeometricPoint S) (F : Sheaf S.smallEtaleTopology (Type u)),
    (Etale.stalkFunctor s).obj F = (GeometricPoint.toSmallEtalePoint s).sheafFiber.obj F)

#check (AlgebraicGeometry.Scheme.Etale.stalkFunctor_eq_presheafFiber :
  ∀ {S : Scheme.{u}} (s : GeometricPoint S) (F : Sheaf S.smallEtaleTopology (Type u)),
    (Etale.stalkFunctor s).obj F = Etale.stalk s F.obj)

#check (AlgebraicGeometry.Scheme.Etale.idGeometricPoint :
  ∀ {S : Scheme.{u}} (s : GeometricPoint S), GeometricPoint (Spec (.of s.K)))

#check (AlgebraicGeometry.Scheme.Etale.pullbackThenSections :
  ∀ {S : Scheme.{u}} (s : GeometricPoint S)
    [HasWeakSheafify (Spec (.of s.K)).smallEtaleTopology (Type u)]
    [∀ P : S.Etaleᵒᵖ ⥤ Type u, (smallEtalePullback s.hom).op.HasLeftKanExtension P],
    Sheaf S.smallEtaleTopology (Type u) ⥤ Type u)

#check (AlgebraicGeometry.Scheme.Etale.pullbackThenSections_obj :
  ∀ {S : Scheme.{u}} (s : GeometricPoint S)
    [HasWeakSheafify (Spec (.of s.K)).smallEtaleTopology (Type u)]
    [∀ P : S.Etaleᵒᵖ ⥤ Type u, (smallEtalePullback s.hom).op.HasLeftKanExtension P]
    (F : Sheaf S.smallEtaleTopology (Type u)),
    (Etale.pullbackThenSections s).obj F =
      (((smallEtalePullback s.hom).sheafPullback (Type u)
        S.smallEtaleTopology (Spec (.of s.K)).smallEtaleTopology).obj F).obj.obj
          (Opposite.op (MorphismProperty.Over.mk _ (𝟙 (Spec (.of s.K))) inferInstance :
            (Spec (.of s.K)).Etale)))
