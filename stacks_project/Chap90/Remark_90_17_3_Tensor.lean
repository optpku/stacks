/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Group.TransferInstance
public import Mathlib.Algebra.Module.Submodule.Equiv
public import Mathlib.Algebra.Module.TransferInstance
public import stacks_project.Chap90.Lemma_90_10_6
public import stacks_project.Chap90.Lemma_90_12_2
public import stacks_project.Chap90.Remark_90_17_3_Comparison

/-!
# Tangent-space comparison for residue-fibre lifts along `k[V]`

If `p` satisfies Schlessinger's (S2), then so does the residue slice `F_x0`, the
associated isomorphism-class functor satisfies (H2), and isomorphism classes of
lifts of `x0` along `k[V] ⟶ k` are canonically identified with
`T F_x0 ⊗[k] V` as `k`-vector spaces.
-/

@[expose] public section

noncomputable section

open CategoryTheory
open ArtinianLocalAlgCat
open scoped TensorProduct

universe u v w

variable {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]
variable {F : Type v} [Category.{w} F]

namespace CategoryTheory.Functor

variable (p : F ⥤ ArtinianLocalAlgCat Λ k) [IsFibered.InGroupoids p.op]
variable [HasSchlessingerS2 p] (x0 : p.Fiber (residue Λ k))

/-- If `p` satisfies (S2), then the isomorphism-class functor of the residue slice
`F_x0` satisfies (H2). -/
instance instHasSchlessingerH2_fiberIsoClass_overForget :
    HasSchlessingerH2
      (fiberIsoClassFunctor (Over.forget (Fiber.fiberInclusion.obj x0) ⋙ p)) := sorry

variable (V : FGModuleCat.{u} k)

/-- Additive group structure on `Lift(x0, k[V])`, transported from the slice
isomorphism-class functor. -/
instance instAddCommGroup_liftsSquareZero :
    AddCommGroup (lifts p (squareZeroToResidue Λ k V) x0) :=
  Equiv.addCommGroup (liftsSquareZeroEquivIsoClass p x0 V)

/-- Transport of the `k`-module structure on `F-bar_x0(k[V])` along
`liftsSquareZeroEquivIsoClass`. -/
instance instModule_liftsSquareZero :
    Module k (lifts p (squareZeroToResidue Λ k V) x0) :=
  Equiv.module k (liftsSquareZeroEquivIsoClass p x0 V)

/-- Under (S2), isomorphism classes of lifts of `x0` along `k[V] ⟶ k` are
`k`-linearly equivalent to `T F_x0 ⊗[k] V`. -/
def liftsSquareZeroLinearEquiv :
    lifts p (squareZeroToResidue Λ k V) x0 ≃ₗ[k]
      (fiberIsoClassFunctor (Over.forget (Fiber.fiberInclusion.obj x0) ⋙ p)).obj
          (dualNumber Λ k) ⊗[k] V :=
  (Equiv.linearEquiv k (liftsSquareZeroEquivIsoClass p x0 V)).trans
    (LinearEquiv.ofBijective
        (fiberDualTangentTensor
          (Over.forget (Fiber.fiberInclusion.obj x0) ⋙ p) V)
        (bijective_fiberDualTangentTensor
          (Over.forget (Fiber.fiberInclusion.obj x0) ⋙ p) V)).symm

/-- `liftsSquareZeroLinearEquiv` is `liftsSquareZeroEquivIsoClass`, followed by the
inverse of `fiberDualTangentTensor` on the residue slice. -/
theorem liftsSquareZeroLinearEquiv_spec
    (x : lifts p (squareZeroToResidue Λ k V) x0) :
    liftsSquareZeroLinearEquiv p x0 V x =
      (LinearEquiv.ofBijective
          (fiberDualTangentTensor
            (Over.forget (Fiber.fiberInclusion.obj x0) ⋙ p) V)
          (bijective_fiberDualTangentTensor
            (Over.forget (Fiber.fiberInclusion.obj x0) ⋙ p) V)).symm
        (liftsSquareZeroEquivIsoClass p x0 V x) := sorry

end CategoryTheory.Functor
