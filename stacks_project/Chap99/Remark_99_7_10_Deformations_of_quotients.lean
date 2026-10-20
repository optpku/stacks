/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Torsor.Defs
public import stacks_project.Chap99.Remark_99_7_10_Deformations_of_quotients_Action
public import stacks_project.Chap99.Remark_99_7_9_Obstructions_for_quotients

/-!
# Remark 99.7.10 (Deformations of quotients)

In Situation 99.7.1, if `F` is flat over `B` and `T ⊂ T'` is a first-order
thickening of schemes over `B`, the set of lifts of a quotient point `x` to
`Q_{F/X/B}(T')` is a principal homogeneous space under
`Hom_{O_{X_T}}(K, Q ⊗_{O_T} J)` once `o_x(T') = 0`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open CategoryTheory.Abelian (Ext)

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Quot

variable {S : Scheme.{u}} {X B : AlgebraicSpace S}

/-- Remark 99.7.10 (Deformations of quotients): in Situation 99.7.1, assume `F`
is flat over `B` and `T ⊂ T'` is a first-order thickening of schemes over `B`.
If `o_x(T') = 0`, then the set of kernel-identified lifts `x' ∈ Q_{F/X/B}(T')`
is a principal homogeneous space under `Hom_{O_{X_T}}(K, Q ⊗_{O_T} J)`. -/
@[stacks 0CZV]
theorem lifts_addTorsor (f : X ⟶ B) (F : X.Modules) [F.IsQuasicoherent]
    {σ σ' : SchemesOver B} (h : σ ⟶ σ')
    [AlgebraicGeometry.IsFirstOrderThickening h.left.left]
    (hF : Modules.flatOver F f) [HasExt.{u} (fiber f σ).Modules]
    (x : Point f F σ) (hobs : obstruction f F h hF x = 0) :
    Nonempty (AddTorsor (deformationHom f h x) (Lift f F h x)) :=
  sorry

/-- Given a lift of `x` to `Q_{F/X/B}(T')`, the assignment `φ ↦ Q'_φ` is a
bijection between `Hom_{O_{X_T}}(K, Q ⊗_{O_T} J)` and the set of
kernel-identified lifts of `x`. -/
theorem pointOfHom_bijective (f : X ⟶ B) (F : X.Modules) [F.IsQuasicoherent]
    {σ σ' : SchemesOver B} (h : σ ⟶ σ')
    [AlgebraicGeometry.IsFirstOrderThickening h.left.left]
    (hF : Modules.flatOver F f) (x : Point f F σ) (x' : Point f F σ')
    (hx : Rel (x'.pullback h) x) :
    Function.Bijective (fun φ : deformationHom f h x ↦
      Lift.ofHom f F h hF x x' hx φ) :=
  sorry

/-- The Hom-group `Hom_{O_{X_T}}(K, Q ⊗_{O_T} J)` acts simply transitively on
the nonempty type of kernel-identified lifts. The flatness witness is an
explicit parameter, matching Situation 99.7.1, so this is a constructor
rather than a synthesized instance. -/
@[reducible] def addTorsorLift (f : X ⟶ B) (F : X.Modules) [F.IsQuasicoherent]
    {σ σ' : SchemesOver B} (h : σ ⟶ σ')
    [AlgebraicGeometry.IsFirstOrderThickening h.left.left]
    (hF : Modules.flatOver F f) (x : Point f F σ)
    [Nonempty (Lift f F h x)] :
    AddTorsor (deformationHom f h x) (Lift f F h x) where
  vadd := Lift.vadd f F h hF x
  vsub := Lift.vsub f F h hF x
  zero_vadd := sorry
  add_vadd := sorry
  vsub_vadd' := sorry
  vadd_vsub' := sorry

end AlgebraicGeometry.AlgebraicSpace.Quot
