module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.ExtensionByZero
public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.CategoryTheory.Sites.Whiskering
public import Mathlib.Data.ZMod.Basic

@[expose] public section

open AlgebraicGeometry CategoryTheory
open AlgebraicGeometry.Scheme

noncomputable section

universe u

namespace AlgebraicGeometry.Etale.TorsionOnCurve

/-- The abelian étale sheaf obtained by extending the underlying abelian sheaf of a
`ZMod ell`-module sheaf by zero along an étale morphism. -/
noncomputable abbrev extensionByZeroZModModule {U X : Scheme.{u}}
    (j : U ⟶ X) [Etale j] {ell : ℕ}
    [∀ G : U.Etaleᵒᵖ ⥤ AddCommGrpCat.{u},
      (etaleRestriction j).op.HasLeftKanExtension G]
    [HasWeakSheafify X.smallEtaleTopology AddCommGrpCat.{u}]
    [U.smallEtaleTopology.HasSheafCompose
      (forget₂ (ModuleCat.{u} (ZMod ell)) AddCommGrpCat.{u})]
    (G : Sheaf U.smallEtaleTopology (ModuleCat.{u} (ZMod ell))) :
    Sheaf X.smallEtaleTopology AddCommGrpCat.{u} :=
  (abelianExtensionByZero j).obj
    ((sheafCompose U.smallEtaleTopology
        (forget₂ (ModuleCat.{u} (ZMod ell)) AddCommGrpCat.{u})).obj G)

/-- Extension by zero of module coefficients is the value of the abelian
extension-by-zero functor after forgetting the module structure. -/
theorem extensionByZeroZModModule_eq {U X : Scheme.{u}}
    (j : U ⟶ X) [Etale j] {ell : ℕ}
    [∀ G : U.Etaleᵒᵖ ⥤ AddCommGrpCat.{u},
      (etaleRestriction j).op.HasLeftKanExtension G]
    [HasWeakSheafify X.smallEtaleTopology AddCommGrpCat.{u}]
    [U.smallEtaleTopology.HasSheafCompose
      (forget₂ (ModuleCat.{u} (ZMod ell)) AddCommGrpCat.{u})]
    (G : Sheaf U.smallEtaleTopology (ModuleCat.{u} (ZMod ell))) :
    extensionByZeroZModModule j G =
      (abelianExtensionByZero j).obj
        ((sheafCompose U.smallEtaleTopology
            (forget₂ (ModuleCat.{u} (ZMod ell)) AddCommGrpCat.{u})).obj G) := rfl

end AlgebraicGeometry.Etale.TorsionOnCurve
