/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Graded.Commutative
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.RelativeProj.Presentation
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Separation

/-!
# Separation of relative projective spectra

The structure morphism of an étale-local relative projective spectrum of a quasicoherent
commutative graded algebra sheaf on an algebraic space is separated.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open SheafOfModules.RingedSite

universe u

namespace AlgebraicGeometry.AlgebraicSpace.RelativeProj

/-- A morphism that is étale-locally the scheme relative `Proj` of a one-and-mul-preserving
`Type u` section model of a quasicoherent commutative graded algebra sheaf, via the canonical
structure morphism `etaleChartProj`, is separated. -/
theorem separated
    {S : Scheme.{u}} {X : AlgebraicSpace S}
    (𝒜 : GradedAlgebraSheaf.{u + 1, u} (commStructureSheafLift X))
    [𝒜.IsCommutative] (hqc : 𝒜.IsQuasicoherent)
    {P : AlgebraicSpace S} (π : P ⟶ X)
    (hπ : IsEtaleLocallyProj 𝒜 π) : Separated π := sorry

end AlgebraicGeometry.AlgebraicSpace.RelativeProj
