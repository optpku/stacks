module

public import Mathlib.Data.ZMod.Basic
public import ReasLib.AlgebraicGeometry.Scheme.Frobenius.Absolute
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Cohomology.ConstantPullback

@[expose] public section

open AlgebraicGeometry CategoryTheory AlgebraicGeometry.Scheme.Hom
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme

/-- Absolute Frobenius acts as the identity on constant `ZMod n` small-étale cohomology. -/
theorem absoluteFrobenius_etaleHq_constantZMod_eq_id
    {p : ℕ} [Fact p.Prime] (X : Scheme.{u}) [IsCharP X p] (n j : ℕ) :
    etaleHq_constant_pullback (absoluteFrobenius p X)
        (AddCommGrpCat.of (ULift.{u} (ZMod n))) j =
      𝟙 _ := sorry

/-- Pullback by absolute Frobenius fixes every constant `ZMod n` étale cohomology class. -/
theorem absoluteFrobenius_etaleHq_constantZMod_apply
    {p : ℕ} [Fact p.Prime] (X : Scheme.{u}) [IsCharP X p] (n j : ℕ)
    (ξ : (Sheaf.functorH X.smallEtaleTopology j).obj
      ((constantSheaf X.smallEtaleTopology AddCommGrpCat.{u}).obj
        (AddCommGrpCat.of (ULift.{u} (ZMod n))))) :
    etaleHq_constant_pullback (absoluteFrobenius p X)
        (AddCommGrpCat.of (ULift.{u} (ZMod n))) j ξ =
      ξ := sorry

end AlgebraicGeometry.Scheme
