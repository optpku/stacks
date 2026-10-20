module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.BaseChange.Abelian
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Torsion
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.Etale

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Hom

variable [∀ Z : Scheme.{u}, HasSheafify Z.smallEtaleTopology AddCommGrpCat.{u}]

/-- Smooth inverse image commutes with every higher étale direct image along a
quasi-compact, quasi-separated morphism for abelian sheaves whose geometric stalks
are torsion of orders invertible on the base. -/
theorem higherDirectImageBaseChange_isIso_of_smooth
    {X S T Y : Scheme.{u}} (f : X ⟶ S) [Smooth f] (g : T ⟶ S)
    [QuasiCompact g] [QuasiSeparated g] (h : Y ⟶ X) (e : Y ⟶ T)
    (h_cart : IsPullback h e f g)
    {F : Sheaf T.smallEtaleTopology AddCommGrpCat.{u}}
    (hF : IsTorsionWithOrdersInvertibleOn S F) (q : ℕ) :
    IsIso (higherDirectImageBaseChange g f h e h_cart.flip F q) := sorry

/-- The smooth higher-direct-image base-change comparison is canonically an
isomorphism when its cartesian-square and invertible-order torsion hypotheses
are supplied by `Fact`. -/
instance higherDirectImageBaseChange_isIso_of_smooth_of_fact
    {X S T Y : Scheme.{u}} (f : X ⟶ S) [Smooth f] (g : T ⟶ S)
    [QuasiCompact g] [QuasiSeparated g] (h : Y ⟶ X) (e : Y ⟶ T)
    [h_cart : Fact (IsPullback h e f g)]
    {F : Sheaf T.smallEtaleTopology AddCommGrpCat.{u}}
    [hF : Fact (IsTorsionWithOrdersInvertibleOn S F)] (q : ℕ) :
    IsIso (higherDirectImageBaseChange g f h e h_cart.out.flip F q) :=
  higherDirectImageBaseChange_isIso_of_smooth f g h e h_cart.out hF.out q

end AlgebraicGeometry.Scheme.Hom

end
