/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.AlgebraicGeometry.Sites.Etale
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import Mathlib.Data.ZMod.Basic
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.Topology.KrullDimension
public import ReasLib.AlgebraicGeometry.Scheme.Characteristic.Prime
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FiniteType
public import ReasLib.AlgebraicGeometry.Scheme.OverField

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry
namespace Scheme
namespace Etale
namespace Small

/-- An affine scheme of characteristic `p` has vanishing constant `ZMod p` small-etale
cohomology in every degree at least two. -/
theorem constantZModCohomology_isZero_of_isAffine
    {S : Scheme.{u}} (p q : ℕ) [Fact p.Prime] [S.IsCharP p] [IsAffine S]
    [HasSheafify S.smallEtaleTopology AddCommGrpCat.{u}]
    [HasExt.{u} (Sheaf S.smallEtaleTopology AddCommGrpCat.{u})]
    (hq : 2 ≤ q) :
      IsZero ((Sheaf.functorH S.smallEtaleTopology q).obj
      ((constantSheaf S.smallEtaleTopology AddCommGrpCat.{u}).obj
        (AddCommGrpCat.of (ULift.{u} (ZMod p))))) := sorry

/-- A quasi-compact and quasi-separated scheme of dimension `d` and characteristic `p` has vanishing
constant `ZMod p` small-etale cohomology in every degree at least `2 + d`. -/
theorem constantZModCohomology_isZero_of_dimension
    {S : Scheme.{u}} (p d q : ℕ) [Fact p.Prime] [S.IsCharP p]
    [CompactSpace S] [QuasiSeparatedSpace S]
    [HasSheafify S.smallEtaleTopology AddCommGrpCat.{u}]
    [HasExt.{u} (Sheaf S.smallEtaleTopology AddCommGrpCat.{u})]
    (h_dim : topologicalKrullDim S = (d : WithBot ℕ∞)) (hq : 2 + d ≤ q) :
      IsZero ((Sheaf.functorH S.smallEtaleTopology q).obj
      ((constantSheaf S.smallEtaleTopology AddCommGrpCat.{u}).obj
        (AddCommGrpCat.of (ULift.{u} (ZMod p))))) := sorry

/-- A separated scheme of finite type over an algebraically closed field of positive
characteristic `p` has vanishing constant `ZMod p` small-etale cohomology in every
degree strictly above its topological Krull dimension. -/
theorem constantZModCohomology_isZero_of_isAlgClosed
    {k : Type u} [Field k] [IsAlgClosed k]
    (p q : ℕ) [CharP k p] [Fact (0 < p)]
    (X : SchemeOverField k) [Scheme.Hom.FiniteType X.hom]
    [IsSeparated X.hom]
    [HasSheafify X.left.smallEtaleTopology AddCommGrpCat.{u}]
    [HasExt.{u} (Sheaf X.left.smallEtaleTopology AddCommGrpCat.{u})]
    (hq : topologicalKrullDim X.left < (q : WithBot ℕ∞)) :
    IsZero
      ((Sheaf.functorH X.left.smallEtaleTopology q).obj
        ((constantSheaf X.left.smallEtaleTopology AddCommGrpCat.{u}).obj
          (AddCommGrpCat.of (ULift.{u} (ZMod p))))) := sorry

end Small
end Etale
end Scheme
end AlgebraicGeometry

end
