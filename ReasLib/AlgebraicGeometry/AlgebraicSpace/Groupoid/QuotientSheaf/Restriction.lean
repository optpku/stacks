/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Groupoid.Saturation
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Groupoid.PreRelation
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.PreRelation.QuotientSheaf.Restriction

/-!
# Saturation criteria for restriction-induced maps of quotient sheaves

Restriction of a groupoid induces an isomorphism of fppf quotient sheaves when
the saturation morphism is surjective as a map of fppf sheaves.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits
open AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidAlgebraicSpace

/-- A restriction of a groupoid induces an isomorphism of fppf quotient sheaves
if its saturation morphism is surjective as a map of fppf sheaves. -/
theorem quotientSheafMap_isIso_of_saturationLocallySurjective {S : Scheme.{u}}
    {B : AlgebraicSpace S} (G : GroupoidAlgebraicSpace B) {U' : Over B}
    (g : U' ⟶ G.U)
    (h_saturation : Presheaf.IsLocallySurjective (Scheme.fppfTopology.over S)
      (G.saturationMap g).left) :
    IsIso (G.toPreRelation.quotientSheafMap g) :=
  sorry

/-- A restriction of a groupoid induces an isomorphism of fppf quotient sheaves
if the singleton family consisting of its saturation morphism is an fppf covering. -/
theorem quotientSheafMap_isIso_of_saturationCovering {S : Scheme.{u}}
    {B : AlgebraicSpace S} (G : GroupoidAlgebraicSpace B) {U' : Over B}
    (g : U' ⟶ G.U)
    [FppfCovering (fun _ : PUnit ↦ (Limits.pullback g G.t).left)
      (fun _ ↦ (G.saturationMap g).left)] :
    IsIso (G.toPreRelation.quotientSheafMap g) :=
  sorry

end AlgebraicGeometry.GroupoidAlgebraicSpace
