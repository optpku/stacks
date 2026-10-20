/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Cohomology.Affine
import StacksCheckRecall

/-!
# Example 85.23.1

Let `S` be a scheme and `X` an algebraic space over `S`. On the ringed site
`C = spacesEtaleSite X` with structure sheaf `spacesStructureSheaf X`
(the sheaf given by `U ↦ Γ(U, O_U)`), let `A_U` be the quasi-coherent
`O_U`-modules. With `B = Ob(C)`, `d_V = 0`, and `Cov_V` the affine covering
families in `spacesEtalePrecoverage`, the assumptions (1), (2), (3) of
section 85.23 hold.
-/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.Modules

universe u

/- Example 85.23.1 (1): restriction along an étale morphism preserves quasi-coherence,
in particular along the underlying morphisms of the spaces-étale site. -/
@[stacks 0DC5] #check
  (AlgebraicGeometry.AlgebraicSpace.Modules.restrict_isQuasicoherent :
    ∀ {S : Scheme.{u}} {Y Z : AlgebraicSpace S} (f : Y ⟶ Z) [Etale f]
      (F : Z.Modules) [F.IsQuasicoherent], (restrict F f).IsQuasicoherent)

/- Example 85.23.1 (2): quasi-coherence is local for every spaces-étale covering family. -/
@[stacks 0DC5] #check
  (AlgebraicGeometry.AlgebraicSpace.Modules.isQuasicoherent_iff_of_spacesEtaleCover :
    ∀ {S : Scheme.{u}} {X : AlgebraicSpace S} {U : spacesEtaleSite X}
      {ι : Type u} [Small.{u} ι] {V : ι → spacesEtaleSite X}
      (f : ∀ i, V i ⟶ U) (hf : Presieve.ofArrows V f ∈ spacesEtalePrecoverage X U)
      (F : U.left.Modules),
      F.IsQuasicoherent ↔ ∀ i, (restrict F (f i).left).IsQuasicoherent)

/- Example 85.23.1 (3): every object admits an affine covering family. -/
@[stacks 0DC5] #check (AlgebraicGeometry.AlgebraicSpace.exists_affineCovering :
  ∀ {S : Scheme.{u}} {X : AlgebraicSpace S} (V : spacesEtaleSite X),
    ∃ (ι : Type u) (_ : Small.{u} ι) (U : ι → spacesEtaleSite X) (f : ∀ i, U i ⟶ V),
      IsAffineCovering U f)

/- Example 85.23.1 (3): affine coverings are cofinal among spaces-étale coverings. -/
@[stacks 0DC5] #check (AlgebraicGeometry.AlgebraicSpace.exists_affineCovering_refinement :
  ∀ {S : Scheme.{u}} {X : AlgebraicSpace S} {V : spacesEtaleSite X}
    {ι : Type u} [Small.{u} ι] {W : ι → spacesEtaleSite X}
    (g : ∀ i, W i ⟶ V) (hg : Presieve.ofArrows W g ∈ spacesEtalePrecoverage X V),
    ∃ (κ : Type u) (_ : Small.{u} κ) (U : κ → spacesEtaleSite X) (f : ∀ k, U k ⟶ V),
      IsAffineCovering U f ∧ (Presieve.ofArrows U f).FactorsThru (Presieve.ofArrows W g))

/- Example 85.23.1 (3): the cohomological bound is zero on every member of an affine
covering, for every quasi-coherent module on the covered object. -/
@[stacks 0DC5] #check
  (AlgebraicGeometry.AlgebraicSpace.affineCovering_higherCohomology_isZero :
    ∀ {S : Scheme.{u}} {X : AlgebraicSpace S} {V : spacesEtaleSite X}
      {ι : Type u} {U : ι → spacesEtaleSite X} {f : ∀ i, U i ⟶ V}
      (h : IsAffineCovering U f) (F : V.left.Modules) [F.IsQuasicoherent] (i : ι)
      (p : ℕ) (hp : 0 < p)
      [HasSheafify (smallEtaleTopology (U i).left) AddCommGrpCat.{u}]
      [HasExt.{u} (Sheaf (smallEtaleTopology (U i).left) AddCommGrpCat.{u})],
      IsZero (cohomology (U i).left (Modules.restrict F (f i).left) p))
