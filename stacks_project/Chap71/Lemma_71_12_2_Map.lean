/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.RelativeProj.Map.Partial

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open SheafOfModules.RingedSite

universe u

/- The open domain and base compatibility of a partial relative-Proj map. -/
#check (AlgebraicGeometry.AlgebraicSpace.RelativeProjMap.spec :
  ∀ {S : Scheme.{u}} {X P Q : AlgebraicSpace S}
    {πP : P ⟶ X} {πQ : Q ⟶ X}
    {𝒜 ℬ : GradedAlgebraSheaf.{u + 1, u} (commStructureSheafLift X)}
    [𝒜.IsQuasicoherent] [ℬ.IsQuasicoherent]
    {twistP : ℤ → P.Modules} {twistQ : ℤ → Q.Modules}
    {φ : GradedAlgebraSheaf.Hom.{u + 1, u} 𝒜 ℬ}
    (r : AlgebraicGeometry.AlgebraicSpace.RelativeProjMap πP πQ 𝒜 ℬ twistP twistQ φ),
    IsOpenImmersion r.domain.ι ∧ r.map ≫ πP = r.domain.ι ≫ πQ)
