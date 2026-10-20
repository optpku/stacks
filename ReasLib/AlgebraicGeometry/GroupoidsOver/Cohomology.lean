module

public import ReasLib.AlgebraicGeometry.GroupoidsOver.SheafPullback
public import ReasLib.AlgebraicGeometry.GroupoidsOver.AssociatedStructureSheaf
public import Mathlib.Algebra.Category.ModuleCat.Sheaf
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic

/-!
# Objectwise cohomology on groupoid fibrations

Cohomology at an object agrees with cohomology of the inverse image on the
big standard site of its underlying scheme. In the étale topology it also
agrees with cohomology of the small étale restriction, for both abelian
sheaves and structure-sheaf modules.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory GroupoidsOver

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidsOver

variable {S : Scheme.{u}}

/-- For a category fibred in groupoids `𝒳` over `(Sch/S)_fppf`,
a standard topology `τ`, an object `x` lying over `U = p(x)`, and an abelian
sheaf `F` on `𝒳_τ`, objectwise cohomology `H^p_τ(x, F)` agrees with
cohomology of `x⁻¹ F` on `(Sch/U)_τ`. -/
theorem cohomology_isomorphic_pullback (𝒳 : GroupoidsOver S)
    (τ : StandardTopology) (x : 𝒳.total)
    (F : Sheaf (𝒳.associatedTopology τ) AddCommGrpCat.{u}) (p : ℕ)
    [HasSheafify (𝒳.associatedTopology τ) AddCommGrpCat.{u}]
    [HasSheafify (τ.overTopology (𝒳.p.obj x).left) AddCommGrpCat.{u}]
    [HasExt.{u} (Sheaf (𝒳.associatedTopology τ) AddCommGrpCat.{u})]
    [HasExt.{u} (Sheaf (τ.overTopology (𝒳.p.obj x).left) AddCommGrpCat.{u})] :
    IsIsomorphic (F.H' p x)
      ((pullbackSheaf τ x F).H' p (Over.mk (𝟙 (𝒳.p.obj x).left))) :=
  sorry

/-- For the étale topology, objectwise cohomology `H^p_étale(x, F)`
also agrees with cohomology of `F|_{U_étale}` on the small étale site of
`U = p(x)`. -/
theorem cohomology_isomorphic_smallEtale (𝒳 : GroupoidsOver S) (x : 𝒳.total)
    (F : Sheaf 𝒳.etaleTopology AddCommGrpCat.{u}) (p : ℕ)
    [HasSheafify 𝒳.etaleTopology AddCommGrpCat.{u}]
    [HasSheafify ((𝒳.p.obj x).left.smallEtaleTopology) AddCommGrpCat.{u}]
    [HasExt.{u} (Sheaf 𝒳.etaleTopology AddCommGrpCat.{u})]
    [HasExt.{u} (Sheaf ((𝒳.p.obj x).left.smallEtaleTopology) AddCommGrpCat.{u})] :
    IsIsomorphic (F.H' p x)
      ((restrictEtaleSheaf x F).H' p (Scheme.Etale.mk (𝟙 (𝒳.p.obj x).left))) :=
  sorry

/-- Module-valued form of the big-site comparison: cohomology of an
`𝒪_𝒳`-module at `x` agrees with cohomology of the inverse image of its
underlying abelian sheaf on `(Sch/U)_τ`. -/
theorem cohomology_isomorphic_pullback_modules (𝒳 : GroupoidsOver S)
    (τ : StandardTopology) (x : 𝒳.total)
    (F : SheafOfModules.{u} (associatedStructureSheaf 𝒳 τ)) (p : ℕ)
    [HasSheafify (𝒳.associatedTopology τ) AddCommGrpCat.{u}]
    [HasSheafify (τ.overTopology (𝒳.p.obj x).left) AddCommGrpCat.{u}]
    [HasExt.{u} (Sheaf (𝒳.associatedTopology τ) AddCommGrpCat.{u})]
    [HasExt.{u} (Sheaf (τ.overTopology (𝒳.p.obj x).left) AddCommGrpCat.{u})] :
    IsIsomorphic
      (((SheafOfModules.toSheaf (associatedStructureSheaf 𝒳 τ)).obj F).H' p x)
      ((pullbackSheaf τ x
          ((SheafOfModules.toSheaf (associatedStructureSheaf 𝒳 τ)).obj F)).H' p
        (Over.mk (𝟙 (𝒳.p.obj x).left))) :=
  sorry

/-- Module-valued form of the small-étale comparison: cohomology of an étale
`𝒪_𝒳`-module at `x` agrees with cohomology of the small-étale restriction of
its underlying abelian sheaf. -/
theorem cohomology_isomorphic_smallEtale_modules (𝒳 : GroupoidsOver S)
    (x : 𝒳.total) (F : SheafOfModules.{u} (associatedStructureSheaf 𝒳 .etale))
    (p : ℕ)
    [HasSheafify 𝒳.etaleTopology AddCommGrpCat.{u}]
    [HasSheafify ((𝒳.p.obj x).left.smallEtaleTopology) AddCommGrpCat.{u}]
    [HasExt.{u} (Sheaf 𝒳.etaleTopology AddCommGrpCat.{u})]
    [HasExt.{u} (Sheaf ((𝒳.p.obj x).left.smallEtaleTopology) AddCommGrpCat.{u})] :
    IsIsomorphic
      (((SheafOfModules.toSheaf (associatedStructureSheaf 𝒳 .etale)).obj F).H' p x)
      ((restrictEtaleSheaf x
          ((SheafOfModules.toSheaf (associatedStructureSheaf 𝒳 .etale)).obj F)).H' p
        (Scheme.Etale.mk (𝟙 (𝒳.p.obj x).left))) :=
  sorry


end AlgebraicGeometry.GroupoidsOver
