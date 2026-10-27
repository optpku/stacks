/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Quot.Deformation
import StacksCheckRecall

/-! # Remark 99.7.10 (Deformations of quotients)

The Hom-group from the kernel to the base-ideal tensor acts on quotient lifts.
The checks retain the canonical equalizer, cokernel and splitting constructions.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open CategoryTheory.Abelian (Ext)
open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Quot

variable {S : Scheme.{u}} {X B : AlgebraicSpace S}

/- Remark 99.7.10 (Deformations of quotients). -/
@[stacks 0CZV] #check (AlgebraicGeometry.AlgebraicSpace.Quot.lifts_addTorsor :
  ∀ (f : X ⟶ B) (F : X.Modules) [F.IsQuasicoherent]
    {σ σ' : SchemeOver B} (h : σ ⟶ σ')
    [AlgebraicGeometry.IsFirstOrderThickening h.left.left]
    (hF : Modules.flatOver F f)
    [HasExt.{u} (fiber f σ).Modules]
    (x : Point f F σ)
    (hobs : obstruction f F h hF x = 0),
    ∃ t : AddTorsor (deformationHom f h x) (Lift f F h x),
      t.toVAdd.vadd = Lift.vadd f F h hF x ∧
        t.toVSub.vsub = Lift.vsub f F h hF x)

/- Remark 99.7.10 (Deformations of quotients): pointOfHom_bijective. -/
@[stacks 0CZV] #check (AlgebraicGeometry.AlgebraicSpace.Quot.pointOfHom_bijective :
  ∀ (f : X ⟶ B) (F : X.Modules) [F.IsQuasicoherent]
    {σ σ' : SchemeOver B} (h : σ ⟶ σ')
    [AlgebraicGeometry.IsFirstOrderThickening h.left.left]
    (hF : Modules.flatOver F f)
    (x : Point f F σ)
    (x' : Point f F σ')
    (hx : Rel (x'.pullback h) x),
    Function.Bijective (fun φ : deformationHom f h x ↦
      Lift.ofHom f F h hF x x' hx φ))

/- Remark 99.7.10 (Deformations of quotients): addTorsorLift. -/
@[stacks 0CZV] #check (AlgebraicGeometry.AlgebraicSpace.Quot.addTorsorLift :
  ∀ (f : X ⟶ B) (F : X.Modules) [F.IsQuasicoherent]
    {σ σ' : SchemeOver B} (h : σ ⟶ σ')
    [AlgebraicGeometry.IsFirstOrderThickening h.left.left]
    (hF : Modules.flatOver F f)
    (x : Point f F σ)



    [Nonempty (Lift f F h x)],
    AddTorsor (deformationHom f h x) (Lift f F h x))

end AlgebraicGeometry.AlgebraicSpace.Quot
