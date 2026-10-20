module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.ExtensionByZero
public import ReasLib.CategoryTheory.Sites.ConstantSheaf.ZMod
public import Mathlib.AlgebraicGeometry.Sites.AffineEtale

@[expose] public section

open AlgebraicGeometry CategoryTheory
open AlgebraicGeometry.Scheme

noncomputable section

universe u

namespace AlgebraicGeometry.Etale.TorsionOnCurve

/-- The abelian étale sheaf obtained by extending the constant sheaf with
coefficients in `ULift (ZMod ell)` by zero along an étale morphism. -/
noncomputable abbrev extensionByZeroConstantZMod {U X : Scheme.{u}}
    (j : U ⟶ X) [Etale j]
    [∀ G : U.Etaleᵒᵖ ⥤ AddCommGrpCat.{u},
      (etaleRestriction j).op.HasLeftKanExtension G]
    [HasWeakSheafify X.smallEtaleTopology AddCommGrpCat.{u}] (ell : ℕ) :
    Sheaf X.smallEtaleTopology AddCommGrpCat.{u} :=
  (abelianExtensionByZero j).obj
    (CategoryTheory.constantZModSheaf.{_, _, u} U.smallEtaleTopology ell)

/-- Extension by zero of constant cyclic coefficients is the value of the
abelian extension-by-zero functor on the constant cyclic sheaf. -/
theorem extensionByZeroConstantZMod_eq {U X : Scheme.{u}}
    (j : U ⟶ X) [Etale j]
    [∀ G : U.Etaleᵒᵖ ⥤ AddCommGrpCat.{u},
      (etaleRestriction j).op.HasLeftKanExtension G]
    [HasWeakSheafify X.smallEtaleTopology AddCommGrpCat.{u}] (ell : ℕ) :
    extensionByZeroConstantZMod j ell =
      (abelianExtensionByZero j).obj
        (CategoryTheory.constantZModSheaf.{_, _, u} U.smallEtaleTopology ell) := rfl

end AlgebraicGeometry.Etale.TorsionOnCurve
