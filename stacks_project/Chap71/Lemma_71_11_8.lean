/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.RelativeProj.FiniteType

/-!
# Lemma 71.11.8

In Situation 71.11.1, if `𝒜` is of finite type as a sheaf of `𝒪_X`-algebras, then a morphism
`π` that is étale-locally the scheme relative `Proj` of a one-and-mul-preserving `Type u`
section model of `𝒜`, via the canonical structure morphism `etaleChartProj`, is of finite type.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.RelativeProj
open SheafOfModules.RingedSite

universe u

namespace AlgebraicGeometry.AlgebraicSpace.RelativeProj

/- Lemma 71.11.8: in Situation 71.11.1, if `𝒜` is of finite type as a sheaf of `𝒪_X`-algebras,
then a morphism `π : P ⟶ X` that is étale-locally the scheme relative `Proj` of a
one-and-mul-preserving `Type u` section model of `𝒜`, via the canonical structure morphism
`etaleChartProj`, is of finite type. -/
@[stacks 084G]
#check (AlgebraicGeometry.AlgebraicSpace.RelativeProj.finiteType_of_finiteTypeAsBase :
    ∀ {S : Scheme.{u}} {X : AlgebraicSpace S}
    (𝒜 : GradedAlgebraSheaf.{u + 1, u} (commStructureSheafLift X))
    [𝒜.IsCommutative] (hqc : 𝒜.IsQuasicoherent)
    {P : AlgebraicSpace S} (π : P ⟶ X)
    (hπ : IsEtaleLocallyProj 𝒜 π)
    (h𝒜 : FiniteTypeAsBaseAlgebra 𝒜), AlgebraicSpace.FiniteType π)

end AlgebraicGeometry.AlgebraicSpace.RelativeProj
