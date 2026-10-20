module

public import ReasLib.AlgebraicGeometry.GroupoidsOver.Cohomology
import StacksCheckRecall

/-!
# Objectwise cohomology and restriction

The big-site and small-étale comparisons hold for abelian sheaves and for
modules through their underlying abelian sheaves.
-/

open AlgebraicGeometry CategoryTheory GroupoidsOver

universe u

/- Lemma 96.16.1: objectwise cohomology agrees with cohomology of inverse image
on the big site, and in the étale case with cohomology of small étale restriction.
The final two checks retain the corresponding structure-sheaf module cases. -/
@[stacks 075F]
#check (AlgebraicGeometry.GroupoidsOver.cohomology_isomorphic_pullback :
  ∀ {S : Scheme.{u}} (𝒳 : GroupoidsOver S)
    (τ : StandardTopology) (x : 𝒳.total)
    (F : Sheaf (𝒳.associatedTopology τ) AddCommGrpCat.{u}) (p : ℕ)
    [HasSheafify (𝒳.associatedTopology τ) AddCommGrpCat.{u}]
    [HasSheafify (τ.overTopology (𝒳.p.obj x).left) AddCommGrpCat.{u}]
    [HasExt.{u} (Sheaf (𝒳.associatedTopology τ) AddCommGrpCat.{u})]
    [HasExt.{u} (Sheaf (τ.overTopology (𝒳.p.obj x).left) AddCommGrpCat.{u})],
    IsIsomorphic (F.H' p x)
      ((pullbackSheaf τ x F).H' p (Over.mk (𝟙 (𝒳.p.obj x).left))))

#check (AlgebraicGeometry.GroupoidsOver.cohomology_isomorphic_smallEtale :
  ∀ {S : Scheme.{u}} (𝒳 : GroupoidsOver S) (x : 𝒳.total)
    (F : Sheaf 𝒳.etaleTopology AddCommGrpCat.{u}) (p : ℕ)
    [HasSheafify 𝒳.etaleTopology AddCommGrpCat.{u}]
    [HasSheafify ((𝒳.p.obj x).left.smallEtaleTopology) AddCommGrpCat.{u}]
    [HasExt.{u} (Sheaf 𝒳.etaleTopology AddCommGrpCat.{u})]
    [HasExt.{u} (Sheaf ((𝒳.p.obj x).left.smallEtaleTopology) AddCommGrpCat.{u})],
    IsIsomorphic (F.H' p x)
      ((restrictEtaleSheaf x F).H' p (Scheme.Etale.mk (𝟙 (𝒳.p.obj x).left))))

#check (AlgebraicGeometry.GroupoidsOver.cohomology_isomorphic_pullback_modules :
  ∀ {S : Scheme.{u}} (𝒳 : GroupoidsOver S)
    (τ : StandardTopology) (x : 𝒳.total)
    (F : SheafOfModules.{u} (associatedStructureSheaf 𝒳 τ)) (p : ℕ)
    [HasSheafify (𝒳.associatedTopology τ) AddCommGrpCat.{u}]
    [HasSheafify (τ.overTopology (𝒳.p.obj x).left) AddCommGrpCat.{u}]
    [HasExt.{u} (Sheaf (𝒳.associatedTopology τ) AddCommGrpCat.{u})]
    [HasExt.{u} (Sheaf (τ.overTopology (𝒳.p.obj x).left) AddCommGrpCat.{u})],
    IsIsomorphic
      (((SheafOfModules.toSheaf (associatedStructureSheaf 𝒳 τ)).obj F).H' p x)
      ((pullbackSheaf τ x
          ((SheafOfModules.toSheaf (associatedStructureSheaf 𝒳 τ)).obj F)).H' p
        (Over.mk (𝟙 (𝒳.p.obj x).left))))

#check (AlgebraicGeometry.GroupoidsOver.cohomology_isomorphic_smallEtale_modules :
  ∀ {S : Scheme.{u}} (𝒳 : GroupoidsOver S)
    (x : 𝒳.total) (F : SheafOfModules.{u} (associatedStructureSheaf 𝒳 .etale))
    (p : ℕ)
    [HasSheafify 𝒳.etaleTopology AddCommGrpCat.{u}]
    [HasSheafify ((𝒳.p.obj x).left.smallEtaleTopology) AddCommGrpCat.{u}]
    [HasExt.{u} (Sheaf 𝒳.etaleTopology AddCommGrpCat.{u})]
    [HasExt.{u} (Sheaf ((𝒳.p.obj x).left.smallEtaleTopology) AddCommGrpCat.{u})],
    IsIsomorphic
      (((SheafOfModules.toSheaf (associatedStructureSheaf 𝒳 .etale)).obj F).H' p x)
      ((restrictEtaleSheaf x
          ((SheafOfModules.toSheaf (associatedStructureSheaf 𝒳 .etale)).obj F)).H' p
        (Scheme.Etale.mk (𝟙 (𝒳.p.obj x).left))))
