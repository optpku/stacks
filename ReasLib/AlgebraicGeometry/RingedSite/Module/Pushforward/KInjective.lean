/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Homology.CochainComplex.KInjective.Adjunction
public import ReasLib.AlgebraicGeometry.RingedSite.Module.Flat
public import ReasLib.AlgebraicGeometry.RingedSite.Module.Pushforward.Complex
import Mathlib.Tactic.CrossRefAttribute

/-!
# K-Injectivity and Flat Direct Image

For a flat morphism of ringed sites, module pullback is exact.  Its right adjoint, module direct
image, therefore preserves K-injective cochain complexes.
-/

@[expose] public section

open CategoryTheory ComplexShape

noncomputable section

universe u v w z

namespace RingedSite.Hom.modulePushforwardComplex

variable {X Y : RingedSite.{u, v, w}}
variable [HasSheafify X.siteTopology AddCommGrpCat.{z}]
variable [X.siteTopology.WEqualsLocallyBijective AddCommGrpCat.{z}]
variable [HasSheafify Y.siteTopology AddCommGrpCat.{z}]
variable [Y.siteTopology.WEqualsLocallyBijective AddCommGrpCat.{z}]

/-- Lemma 21.20.10 (093Y): direct image along a flat morphism of ringed sites preserves
K-injective cochain complexes. -/
@[stacks 093Y "flat direct image preserves K-injectives", instance]
theorem isKInjective (f : RingedSite.Hom X Y)
    [(f.modulePushforward.{z}).IsRightAdjoint] [IsFlat.{z} f]
    (I : CochainComplex (ModuleCat.{z} X) ℤ) [I.IsKInjective] :
    CochainComplex.IsKInjective
      ((f.modulePushforwardComplex.{z}).obj I) := sorry

end RingedSite.Hom.modulePushforwardComplex
