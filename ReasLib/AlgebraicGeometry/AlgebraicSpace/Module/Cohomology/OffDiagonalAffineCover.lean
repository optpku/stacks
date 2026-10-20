/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.QuasiCompact.OffDiagonalAffineCover
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Cohomology.VanishingH1

/-!
# Cohomology vanishing from off-diagonal affine covers

Fibre-degree bounds for affine étale covers of off-diagonal free quotients give
uniform bounds on the cohomology of quasi-coherent modules.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- Given an affine étale surjection `f : ofOver U ⟶ X` with
`degreesOfFibresBoundedBy f d`, and for each `p : Fin (d + 1)` a free quotient
`q p : offDiagonal f (p.val + 1) ⟶ Up p` of `offDiagonalPermLift` over `X`
together with an affine étale surjection `g p : ofOver (Vp p) ⟶ Up p` with
`degreesOfFibresBoundedBy (g p) (dp p)`, every quasi-coherent `𝒪_X`-module `F`
satisfies `IsZero (cohomology X F n)` whenever `dp p + p.val ≤ n` for all `p`. -/
@[stacks 072C]
theorem cohomology_isZero_of_offDiagonalAffineCover
    {S : Scheme.{u}} {X : AlgebraicSpace S} {U : Over S}
    [AlgebraicGeometry.IsAffine U.left] (f : ofOver U ⟶ X)
    [Etale f] [Surjective f] [Separated f]
    (d : ℕ) (hd : degreesOfFibresBoundedBy f d)
    (Up : Fin (d + 1) → AlgebraicSpace S)
    (q : ∀ p, offDiagonal f (p.val + 1) ⟶ Up p)
    [∀ p, IsFreeQuotient (offDiagonalPermLift f (p.val + 1)) (q p)]
    (π : ∀ p, Up p ⟶ X) [∀ p, Etale (π p)]
    (hπ : ∀ p, q p ≫ π p = offDiagonalToBase f (p.val + 1))
    (Vp : Fin (d + 1) → Over S) [∀ p, AlgebraicGeometry.IsAffine (Vp p).left]
    (g : ∀ p, ofOver (Vp p) ⟶ Up p) [∀ p, Etale (g p)] [∀ p, Surjective (g p)]
    (dp : Fin (d + 1) → ℕ) (hdp : ∀ p, degreesOfFibresBoundedBy (g p) (dp p))
    (F : X.Modules) [F.IsQuasicoherent] {n : ℕ}
    (hn : ∀ p : Fin (d + 1), dp p + p.val ≤ n)
    [HasSheafify (smallEtaleTopology X) AddCommGrpCat.{u}]
    [HasExt.{u} (Sheaf (smallEtaleTopology X) AddCommGrpCat.{u})] :
    IsZero (cohomology X F n) :=
  sorry

/-- A quasi-compact quasi-separated algebraic space has finite cohomological
dimension for quasi-coherent modules. -/
theorem exists_cohomology_isZero
    {S : Scheme.{u}} {X : AlgebraicSpace S}
    [IsQuasiCompact X] [IsAbsolutelyQuasiSeparated X]
    [HasSheafify (smallEtaleTopology X) AddCommGrpCat.{u}]
    [HasExt.{u} (Sheaf (smallEtaleTopology X) AddCommGrpCat.{u})] :
    ∃ n : ℕ, ∀ (F : X.Modules) [F.IsQuasicoherent] (q : ℕ),
      n ≤ q → IsZero (cohomology X F q) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
