/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.RingTheory.HopkinsLevitzki
public import ReasLib.Algebra.Category.ModuleCat.GrothendieckGroup.Basic
public import Mathlib.RingTheory.Length

/-!
# Length on the finite-module Grothendieck group

Over an Artinian ring, composition length is additive in short exact sequences and therefore
descends to a homomorphism `K'_0(R) → ℤ`.
-/

@[expose] public section

noncomputable section

universe u v

open CategoryTheory

namespace CategoryTheory.ModuleCat.K0

variable (R : Type u) [Ring R]

/-
API design: `finite`, `finiteOf`, and `finiteClass` already own the carrier and its generators,
so the length map stays in `ModuleCat.K0` with a short leaf name.  The generator functional is
concrete; only the relation-kernel proof is deferred.  Both bundled and unbundled evaluation
theorems are public so downstream code never unfolds the quotient lift or installs an auxiliary
`FGModuleCat` object by hand.
-/

/-- The finite-module Grothendieck relations lie in the kernel of composition length over an
Artinian ring. -/
@[stacks 00JD "length kills finite-module Grothendieck relations"]
theorem finiteLength_relations [IsArtinianRing R] :
    ObjectProperty.GrothendieckGroup.relations (ModuleCat.isFG.{v} R) ≤
      (FreeAbelianGroup.lift
        fun M : FGModuleCat.{v} R ↦ ((Module.length R M.obj).toNat : ℤ)).ker := sorry

/-- Composition length defines an additive map `K'_0(R) → ℤ` for an Artinian ring. -/
@[stacks 00JD "length on the finite-module Grothendieck group"]
def finiteLength [IsArtinianRing R] : finite.{u, v} R →+ ℤ :=
  ObjectProperty.GrothendieckGroup.lift
    (fun M : FGModuleCat.{v} R ↦ ((Module.length R M.obj).toNat : ℤ))
    (finiteLength_relations.{u, v} R)

/-- The length homomorphism evaluates on a bundled finite module by its ordinary composition
length. -/
@[stacks 00JD "length on a bundled finite-module class", simp]
theorem finiteLength_finiteOf [IsArtinianRing R] (M : FGModuleCat.{v} R) :
    finiteLength.{u, v} R (finiteOf R M) =
      ((Module.length R M.obj).toNat : ℤ) := sorry

/-- The length homomorphism evaluates on an unbundled finite module by its ordinary composition
length. -/
@[stacks 00JD "length on an unbundled finite-module class", simp]
theorem finiteLength_finiteClass [IsArtinianRing R]
    (M : Type v) [AddCommGroup M] [Module R M] [Module.Finite R M] :
    finiteLength.{u, v} R (finiteClass R M) =
      ((Module.length R M).toNat : ℤ) := sorry

end CategoryTheory.ModuleCat.K0
