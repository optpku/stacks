module

public import ReasLib.AlgebraicGeometry.Scheme.Etale.StalkGaloisSet

open CategoryTheory Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.Scheme.Etale

@[expose] public section

universe u

#check (AlgebraicGeometry.Scheme.Etale.residueFieldOf :
  ∀ (K : Type u) [Field K] (s : GeometricPoint (Spec (.of K))), Type u)

#check (AlgebraicGeometry.Scheme.Etale.geometricPointHom :
  ∀ (K : Type u) [Field K] (s : GeometricPoint (Spec (.of K))),
    Spec (.of s.separableClosure) ⟶ Spec (.of K))

#check (AlgebraicGeometry.Scheme.Etale.geometricPointGaloisIso :
  ∀ (K : Type u) [Field K] (s : GeometricPoint (Spec (.of K)))
    (σ : s.absoluteGaloisGroup),
    Over.mk (geometricPointHom K s) ≅ Over.mk (geometricPointHom K s))

#check (AlgebraicGeometry.Scheme.FieldValuedPoint.separableClosureOfAlgClosedIsSepClosed :
  ∀ {X : Scheme.{u}} (p : FieldValuedPoint X) (isAlgClosed : IsAlgClosed p.K),
    IsSepClosed (p.separableClosureOfAlgClosed isAlgClosed))

#check (AlgebraicGeometry.Scheme.Etale.etalePoint :
  ∀ (K : Type u) [Field K] (s : GeometricPoint (Spec (.of K))),
    (Spec (.of K)).smallEtaleTopology.Point)

#check (AlgebraicGeometry.Scheme.Etale.stalkGaloisSetObj :
  ∀ (K : Type u) [Field K] (s : GeometricPoint (Spec (.of K)))
    (F : Sheaf (Spec (.of K)).smallEtaleTopology (Type u)),
    DiscreteContAction TopCat s.absoluteGaloisGroup)

#check (AlgebraicGeometry.Scheme.Etale.stalkGaloisSet :
  ∀ (K : Type u) [Field K] (s : GeometricPoint (Spec (.of K))),
    Sheaf (Spec (.of K)).smallEtaleTopology (Type u) ⥤
      DiscreteContAction TopCat s.absoluteGaloisGroup)

#check (AlgebraicGeometry.Scheme.Etale.stalkGaloisSet_obj_carrier :
  ∀ (K : Type u) [Field K] (s : GeometricPoint (Spec (.of K)))
    (F : Sheaf (Spec (.of K)).smallEtaleTopology (Type u)),
    ((stalkGaloisSet K s).obj F).obj.obj.V =
      TopCat.discrete.obj ((etalePoint K s).presheafFiber.obj F.1))

#check (AlgebraicGeometry.Scheme.Etale.stalkGaloisSet_smul_apply :
  ∀ (K : Type u) [Field K] (s : GeometricPoint (Spec (.of K)))
    (F : Sheaf (Spec (.of K)).smallEtaleTopology (Type u))
    (σ : s.absoluteGaloisGroup) (x : (etalePoint K s).presheafFiber.obj F.1),
    ConcreteCategory.hom (((stalkGaloisSet K s).obj F).obj.obj.ρ σ) x =
      stalkGaloisAction (geometricPointHom K s) (geometricPointGaloisIso K s σ) F.1 x)

#check (AlgebraicGeometry.Scheme.Etale.stalkGaloisSet_map_apply :
  ∀ (K : Type u) [Field K] (s : GeometricPoint (Spec (.of K)))
    {F G : Sheaf (Spec (.of K)).smallEtaleTopology (Type u)} (f : F ⟶ G)
    (x : (etalePoint K s).presheafFiber.obj F.1),
    ConcreteCategory.hom (((stalkGaloisSet K s).map f).hom.hom.hom) x =
      (etalePoint K s).presheafFiber.map f.1 x)

#check (AlgebraicGeometry.Scheme.Etale.separableStalkToGeometricStalk :
  ∀ (K : Type u) [Field K] (s : GeometricPoint (Spec (.of K))),
    (etalePoint K s).sheafFiber (A := Type u) ⟶
      (@Scheme.pointSmallEtale _ s.K s.field
        (@IsSepClosed.of_isAlgClosed s.K s.field s.isAlgClosed) s.hom).sheafFiber)

#check (AlgebraicGeometry.Scheme.Etale.separableStalkToGeometricStalk_bijective :
  ∀ (K : Type u) [Field K] (s : GeometricPoint (Spec (.of K)))
    (F : Sheaf (Spec (.of K)).smallEtaleTopology (Type u)),
    Function.Bijective ((separableStalkToGeometricStalk K s).app F))
