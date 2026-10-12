/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Tactic.CrossRefAttribute
public import stacks_project.Chap85.Example_85_23_1_AffineCover

/-!
# Example 85.23.1

Let `S` be a scheme and `X` an algebraic space over `S`. On the ringed site
`C = spacesEtaleSite X` with structure sheaf `spacesStructureSheaf X`
(the sheaf given by `U ↦ Γ(U, O_U)`), let `A_U` be the quasi-coherent
`O_U`-modules. With `B = Ob(C)`, `d_V = 0`, and `Cov_V` the affine covering
families in `spacesEtalePrecoverage`, the assumptions (1), (2), (3) of
section 85.23 hold.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.Modules

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Modules

/-- Example 85.23.1 (1): restriction of a quasi-coherent module along a morphism of
`C = spacesEtaleSite X` lands in quasi-coherent modules. Identifying `A_U` with
quasi-coherent modules on `U.left`, the restriction `Mod(O_V) ⟶ Mod(O_U)` is
`restrict` along `f.left`. -/
@[stacks 0DC5, instance]
instance restrict_isQuasicoherent {S : Scheme.{u}} {X : AlgebraicSpace S}
    {U V : spacesEtaleSite X} (f : U ⟶ V) (F : V.left.Modules) [F.IsQuasicoherent] :
    (restrict F f.left).IsQuasicoherent :=
  sorry

/-- Example 85.23.1 (2): membership in `A_U` is local on covering families of
`C = spacesEtaleSite X`. A module on `U.left` is quasi-coherent if and only if its
restrictions along a spaces-étale covering are quasi-coherent. -/
@[stacks 0DC5]
theorem isQuasicoherent_iff_of_spacesEtaleCover {S : Scheme.{u}} {X : AlgebraicSpace S}
    {U : spacesEtaleSite X} {ι : Type u} [Small.{u} ι] {V : ι → spacesEtaleSite X}
    (f : ∀ i, V i ⟶ U) (hf : Presieve.ofArrows V f ∈ spacesEtalePrecoverage X U)
    (F : U.left.Modules) :
    F.IsQuasicoherent ↔ ∀ i, (restrict F (f i).left).IsQuasicoherent :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Modules

namespace AlgebraicGeometry.AlgebraicSpace

/-- Example 85.23.1 (3): with `B = Ob(C)`, `d_V = 0`, and `Cov_V` the affine covering
families of `V` in `spacesEtalePrecoverage X`, one has
`IsZero (cohomology (U i).left (Modules.restrict F (f i).left) p)` whenever
`IsAffineCovering U f`, `F` is quasi-coherent on `V.left`, and `0 < p`. -/
@[stacks 0DC5]
theorem affineCovering_higherCohomology_isZero {S : Scheme.{u}} {X : AlgebraicSpace S}
    {V : spacesEtaleSite X} {ι : Type u} {U : ι → spacesEtaleSite X} {f : ∀ i, U i ⟶ V}
    (h : IsAffineCovering U f) (F : V.left.Modules) [F.IsQuasicoherent] (i : ι)
    (p : ℕ) (hp : 0 < p)
    [HasSheafify (smallEtaleTopology (U i).left) AddCommGrpCat.{u}]
    [HasExt.{u} (Sheaf (smallEtaleTopology (U i).left) AddCommGrpCat.{u})] :
    IsZero (cohomology (U i).left (Modules.restrict F (f i).left) p) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
