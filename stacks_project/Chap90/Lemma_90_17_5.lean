/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap90.Lemma_90_17_5_Action
import Mathlib.Tactic.CrossRefAttribute

/-!
# Free transitive action on lifts along a square-zero kernel

If `p` is a deformation category and `f : A' ⟶ A` is a surjection in `C_Λ`
whose kernel `I` is annihilated by `m_{A'}`, then a nonempty lift set
`lifts p f x` is a torsor under `T F_x0 ⊗[k] I`, identified with
`Lift(x0, k[I])` by `liftsSquareZeroLinearEquiv`.
-/

@[expose] public section

noncomputable section

open CategoryTheory
open Functor Fiber ArtinianLocalAlgCat IsLocalRing
open scoped TensorProduct

universe u v w

variable {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]
variable {F : Type v} [Category.{w} F]
variable {p : F ⥤ ArtinianLocalAlgCat Λ k}
variable {A' A : ArtinianLocalAlgCat Λ k}

namespace CategoryTheory.Functor

/-- Lemma 90.17.5 Let F be a deformation category. Let A' ⟶ A be a surjective
ring map in C_Λ whose kernel I is annihilated by m_{A'}. Let x ∈ Ob(F(A)).
If Lift(x, A') is nonempty, then T F ⊗[k] I acts freely and transitively on
Lift(x, A'). The action is constructed from the composite bijection Φ of
90.17.5.1–3, after identifying Lift(x0, k[I]) with T F_x0 ⊗[k] I by
liftsSquareZeroLinearEquiv. -/
@[stacks 06JI]
abbrev liftsAddTorsor [IsDeformationCategory p]
    (f : A' ⟶ A) (hf : Function.Surjective f.hom)
    (hI : maximalIdeal A'.carrier * RingHom.ker f.hom.toRingHom = ⊥)
    (x : p.Fiber A) {x0 : p.Fiber (residue Λ k)}
    (φ : fiberInclusion.obj x ⟶ fiberInclusion.obj x0)
    [p.IsHomLift (toResidue A) φ] [p.IsStronglyCocartesian (toResidue A) φ]
    [Nonempty (lifts p f x)] :
    AddTorsor (tangentTensor f hI x0) (lifts p f x) :=
  instAddTorsor_lifts f hf hI x φ

/-- The tensor action of `θ` sends `x'` to `x''` if and only if the transported
difference recovers `θ`. -/
theorem liftsAddTorsor_spec [IsDeformationCategory p]
    (f : A' ⟶ A) (hf : Function.Surjective f.hom)
    (hI : maximalIdeal A'.carrier * RingHom.ker f.hom.toRingHom = ⊥)
    (x : p.Fiber A) {x0 : p.Fiber (residue Λ k)}
    (φ : fiberInclusion.obj x ⟶ fiberInclusion.obj x0)
    [p.IsHomLift (toResidue A) φ] [p.IsStronglyCocartesian (toResidue A) φ]
    (θ : tangentTensor f hI x0) (x' x'' : lifts p f x) :
    liftsTensorVAdd f hf hI x φ θ x' = x'' ↔
      liftsTensorVSub f hf hI x φ x'' x' = θ := sorry

end CategoryTheory.Functor
