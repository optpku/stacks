/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Mathlib.CategoryTheory.Abelian.RightDerived
public import Mathlib.Topology.Sheaves.AddCommGrpCat
public import Mathlib.Topology.Sheaves.Functors

/-!
# Colimits and higher direct images on schemes

This module records compatibility of higher direct images of abelian sheaves with filtered
colimits along quasi-compact and quasi-separated morphisms of schemes.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe u v

namespace AlgebraicGeometry.Scheme

variable {X S : Scheme.{u}}
variable [HasSheafify (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u}]
variable [HasSheafify (Opens.grothendieckTopology S.carrier) AddCommGrpCat.{u}]
variable [HasInjectiveResolutions (X.carrier.Sheaf AddCommGrpCat.{u})]

/-- For a quasi-compact and quasi-separated morphism of schemes, the canonical comparison from
the filtered colimit of degree-`p` higher direct images of abelian sheaves to the degree-`p`
higher direct image of their filtered colimit is an isomorphism. -/
theorem higherDirectImageColimitComparison_isIso_of_quasiCompact_quasiSeparated
    (f : X ⟶ S) [QuasiCompact f] [QuasiSeparated f]
    {I : Type v} [SmallCategory I] [IsFiltered I]
    [HasColimitsOfShape I (X.carrier.Sheaf AddCommGrpCat.{u})]
    [HasColimitsOfShape I (S.carrier.Sheaf AddCommGrpCat.{u})]
    [(TopCat.Sheaf.pushforward AddCommGrpCat.{u} f.base).Additive]
    (ℱ : I ⥤ X.carrier.Sheaf AddCommGrpCat.{u}) (p : ℕ) :
    IsIso
      (colimit.post ℱ
        ((TopCat.Sheaf.pushforward AddCommGrpCat.{u} f.base).rightDerived p)) := sorry

end AlgebraicGeometry.Scheme
