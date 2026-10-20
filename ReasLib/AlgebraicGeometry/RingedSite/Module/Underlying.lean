module

public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Mathlib.Algebra.Category.Grp.Abelian
public import Mathlib.CategoryTheory.Sites.GlobalSections
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.Stalk.Exact
public import ReasLib.AlgebraicGeometry.RingedSite.Module.Basic
public import ReasLib.CategoryTheory.Sites.AbelianSheaf.Additive
import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Underlying additive sheaves of modules

This is the canonical bridge from sheaves of modules on a ringed site to additive sheaves and
additive presheaves.  It is deliberately independent of chapter files so cohomology, sections,
and direct-image comparisons can share the same forgetful functor.
-/

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe z u v w

namespace RingedSite.Hom

/-- The forgetful functor from `𝒪_X`-modules to underlying additive sheaves. -/
@[stacks 0D6H "underlying additive sheaf"]
abbrev underlyingAbelianSheafFunctor (X : RingedSite.{u, v, w}) :
    ModuleCat.{z} X ⥤ Sheaf X.siteTopology AddCommGrpCat.{z} :=
  SheafOfModules.toSheaf.{z} X.structureSheaf

/-- The composite forgetful functor to underlying additive presheaves. -/
@[stacks 0D6H "underlying additive presheaf"]
abbrev underlyingAbelianPresheafFunctor (X : RingedSite.{u, v, w}) :
    ModuleCat.{z} X ⥤ X.carrierᵒᵖ ⥤ AddCommGrpCat.{z} :=
  underlyingAbelianSheafFunctor.{z} X ⋙
    sheafToPresheaf X.siteTopology AddCommGrpCat.{z}

/-- The bundled exact forgetful functor from module sheaves to additive sheaves. -/
@[stacks 0D6H "exact underlying additive sheaf"]
noncomputable abbrev underlyingAbelianSheafExactFunctor
    (X : RingedSite.{u, v, w})
    [UnivLE.{max u v, z}]
    [HasWeakSheafify X.siteTopology AddCommGrpCat.{z}]
    [X.siteTopology.WEqualsLocallyBijective AddCommGrpCat.{z}] :
    ModuleCat.{z} X ⥤ₑ Sheaf X.siteTopology AddCommGrpCat.{z} :=
  ExactFunctor.of (underlyingAbelianSheafFunctor.{z} X)

/-- The underlying additive presheaf functor is exact when the sheaf-to-presheaf leg preserves
finite colimits.  On a chaotic site this hypothesis is supplied by the equivalence instance in
`ReasLib.CategoryTheory.Sites.Chaotic`. -/
@[stacks 0D6H "underlying presheaf exactness"]
theorem underlyingAbelianPresheafFunctor_exact (X : RingedSite.{u, v, w})
    [UnivLE.{max u v, z}]
    [HasWeakSheafify X.siteTopology AddCommGrpCat.{z}]
    [X.siteTopology.WEqualsLocallyBijective AddCommGrpCat.{z}]
    [PreservesFiniteColimits
      (sheafToPresheaf X.siteTopology AddCommGrpCat.{z})] :
    exactFunctor (ModuleCat.{z} X) (X.carrierᵒᵖ ⥤ AddCommGrpCat.{z})
      (underlyingAbelianPresheafFunctor.{z} X) := sorry

/-- The bundled exact underlying additive presheaf functor. -/
@[stacks 0D6H "bundled underlying presheaf exact functor"]
noncomputable abbrev underlyingAbelianPresheafExactFunctor
    (X : RingedSite.{u, v, w})
    [UnivLE.{max u v, z}]
    [HasWeakSheafify X.siteTopology AddCommGrpCat.{z}]
    [X.siteTopology.WEqualsLocallyBijective AddCommGrpCat.{z}]
    [PreservesFiniteColimits
      (sheafToPresheaf X.siteTopology AddCommGrpCat.{z})] :
    ModuleCat.{z} X ⥤ₑ X.carrierᵒᵖ ⥤ AddCommGrpCat.{z} :=
  ExactFunctor.of (underlyingAbelianPresheafFunctor.{z} X)

end RingedSite.Hom
