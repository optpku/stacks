/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.DescentData.Coproduct

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.DescentData

universe u v

variable {I : Type v} [Small.{u} I] {S : Scheme.{u}} {X : AlgebraicSpace S}
variable (Xᵢ : I → AlgebraicSpace S) (f : ∀ i, Xᵢ i ⟶ X)

#check (AlgebraicGeometry.AlgebraicSpace.DescentData.assembleCoproduct Xᵢ f :
    DescentData Xᵢ f ⥤ DescentData (coproductFamily Xᵢ) (coproductArrow Xᵢ f))

#check (AlgebraicGeometry.AlgebraicSpace.DescentData.restrictCoproduct Xᵢ f :
    DescentData (coproductFamily Xᵢ) (coproductArrow Xᵢ f) ⥤ DescentData Xᵢ f)

#check (AlgebraicGeometry.AlgebraicSpace.DescentData.coproductEquivalence Xᵢ f :
    DescentData Xᵢ f ≌ DescentData (coproductFamily Xᵢ) (coproductArrow Xᵢ f))

#check (AlgebraicGeometry.AlgebraicSpace.DescentData.instIsEquivalenceRestrictCoproduct Xᵢ f :
    (restrictCoproduct Xᵢ f).IsEquivalence)

#check (AlgebraicGeometry.AlgebraicSpace.DescentData.coproductInjection_fac Xᵢ f :
    ∀ i, coproductι Xᵢ i ≫ coproductArrow Xᵢ f PUnit.unit = f i ≫ 𝟙 X)

#check (AlgebraicGeometry.AlgebraicSpace.DescentData.coproductUnitIso Xᵢ f :
    𝟭 (DescentData Xᵢ f) ≅ assembleCoproduct Xᵢ f ⋙ restrictCoproduct Xᵢ f)
