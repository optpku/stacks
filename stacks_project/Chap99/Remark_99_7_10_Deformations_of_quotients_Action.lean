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
@[stacks 0CZV] #check (AlgebraicGeometry.AlgebraicSpace.Quot.kernelOfHom :
  ∀ (f : X ⟶ B) (F : X.Modules) {σ σ' : SchemeOver B}
    (h : σ ⟶ σ') [AlgebraicGeometry.IsFirstOrderThickening h.left.left]
    (hF : Modules.flatOver F f)
    (x : Point f F σ) (x' : Point f F σ')
    (hx : Rel (x'.pullback h) x)
    (φ : deformationHom f h x),
    (fiber f σ').Modules)

/- Remark 99.7.10 (Deformations of quotients): mem_kernelOfHom. -/
@[stacks 0CZV] #check (AlgebraicGeometry.AlgebraicSpace.Quot.mem_kernelOfHom :
  ∀ (f : X ⟶ B) (F : X.Modules) {σ σ' : SchemeOver B}
    (h : σ ⟶ σ') [AlgebraicGeometry.IsFirstOrderThickening h.left.left]
    (hF : Modules.flatOver F f)
    (x : Point f F σ) (x' : Point f F σ')
    (hx : Rel (x'.pullback h) x)
    (φ : deformationHom f h x)
    {U : (fiber f σ').Modules} (s : U ⟶ fiberF f F σ'),
    (∃ t : U ⟶ kernelOfHom f F h hF x x' hx φ,
        t ≫ kernelOfHom_arrow f F h hF x x' hx φ = s) ↔
      ∃ k : U ⟶ (Modules.pushforward (fiberMap f h)).obj (kernel x.map),
        s ≫ unitToPushforward f F h =
            k ≫ (Modules.pushforward (fiberMap f h)).map (kernel.ι x.map) ∧
          s ≫ x'.map =
            k ≫ (Modules.pushforward (fiberMap f h)).map φ ≫
              tensorIdealToKernelRestrict f F h hF x x' hx ≫
                kernel.ι (restrictQuotient f F h x x' hx))

/- Remark 99.7.10 (Deformations of quotients): pointOfHom. -/
@[stacks 0CZV] #check (AlgebraicGeometry.AlgebraicSpace.Quot.pointOfHom :
  ∀ (f : X ⟶ B) (F : X.Modules) {σ σ' : SchemeOver B}
    (h : σ ⟶ σ') [AlgebraicGeometry.IsFirstOrderThickening h.left.left]
    (hF : Modules.flatOver F f)
    (x : Point f F σ) (x' : Point f F σ')
    (hx : Rel (x'.pullback h) x)
    (φ : deformationHom f h x),
    Point f F σ')

/- Remark 99.7.10 (Deformations of quotients): pointOfHom_spec. -/
@[stacks 0CZV] #check (AlgebraicGeometry.AlgebraicSpace.Quot.pointOfHom_spec :
  ∀ (f : X ⟶ B) (F : X.Modules) {σ σ' : SchemeOver B}
    (h : σ ⟶ σ') [AlgebraicGeometry.IsFirstOrderThickening h.left.left]
    (hF : Modules.flatOver F f)
    (x : Point f F σ) (x' : Point f F σ')
    (hx : Rel (x'.pullback h) x)
    (φ : deformationHom f h x),
    (pointOfHom f F h hF x x' hx φ).module =
        cokernel (@Subobject.mk _ _ _ _ (kernelOfHom_arrow f F h hF x x' hx φ)
        (mono_kernelOfHom_arrow f F h hF x x' hx φ)).arrow ∧
      (pointOfHom f F h hF x x' hx φ).map =
        cokernel.π (@Subobject.mk _ _ _ _ (kernelOfHom_arrow f F h hF x x' hx φ)
        (mono_kernelOfHom_arrow f F h hF x x' hx φ)).arrow)

/- Remark 99.7.10 (Deformations of quotients): pointOfHom_rel. -/
@[stacks 0CZV] #check (AlgebraicGeometry.AlgebraicSpace.Quot.pointOfHom_rel :
  ∀ (f : X ⟶ B) (F : X.Modules) {σ σ' : SchemeOver B}
    (h : σ ⟶ σ') [AlgebraicGeometry.IsFirstOrderThickening h.left.left]
    (hF : Modules.flatOver F f)
    (x : Point f F σ) (x' : Point f F σ')
    (hx : Rel (x'.pullback h) x)
    (φ : deformationHom f h x),
    Rel ((pointOfHom f F h hF x x' hx φ).pullback h) x)

/- Remark 99.7.10 (Deformations of quotients): Lift.mkPoint. -/
@[stacks 0CZV] #check (AlgebraicGeometry.AlgebraicSpace.Quot.Lift.mkPoint :
  ∀ (f : X ⟶ B) (F : X.Modules) [F.IsQuasicoherent]
    {σ σ' : SchemeOver B} (h : σ ⟶ σ') (x : Point f F σ)
    (x' : Point f F σ') (hx : Rel (x'.pullback h) x),
    Lift f F h x)

/- Remark 99.7.10 (Deformations of quotients): Lift.ofHom. -/
@[stacks 0CZV] #check (AlgebraicGeometry.AlgebraicSpace.Quot.Lift.ofHom :
  ∀ (f : X ⟶ B) (F : X.Modules) [F.IsQuasicoherent]
    {σ σ' : SchemeOver B} (h : σ ⟶ σ')
    [AlgebraicGeometry.IsFirstOrderThickening h.left.left]
    (hF : Modules.flatOver F f)
    (x : Point f F σ) (x' : Point f F σ')
    (hx : Rel (x'.pullback h) x)
    (φ : deformationHom f h x),
    Lift f F h x)

/- Remark 99.7.10 (Deformations of quotients): Lift.vadd. -/
@[stacks 0CZV] #check (AlgebraicGeometry.AlgebraicSpace.Quot.Lift.vadd :
  ∀ (f : X ⟶ B) (F : X.Modules) [F.IsQuasicoherent]
    {σ σ' : SchemeOver B} (h : σ ⟶ σ')
    [AlgebraicGeometry.IsFirstOrderThickening h.left.left]
    (hF : Modules.flatOver F f)
    (x : Point f F σ)
    (φ : deformationHom f h x) (L : Lift f F h x),
    Lift f F h x)

/- Remark 99.7.10 (Deformations of quotients): Lift.vsub. -/
@[stacks 0CZV] #check (AlgebraicGeometry.AlgebraicSpace.Quot.Lift.vsub :
  ∀ (f : X ⟶ B) (F : X.Modules) [F.IsQuasicoherent]
    {σ σ' : SchemeOver B} (h : σ ⟶ σ')
    [AlgebraicGeometry.IsFirstOrderThickening h.left.left]
    (hF : Modules.flatOver F f)
    (x : Point f F σ)

    (L₁ L₂ : Lift f F h x),
    deformationHom f h x)

/- Remark 99.7.10 (Deformations of quotients): Lift.vsub_spec. -/
@[stacks 0CZV] #check (AlgebraicGeometry.AlgebraicSpace.Quot.Lift.vsub_spec :
  ∀ (f : X ⟶ B) (F : X.Modules) [F.IsQuasicoherent]
    {σ σ' : SchemeOver B} (h : σ ⟶ σ')
    [AlgebraicGeometry.IsFirstOrderThickening h.left.left]
    (hF : Modules.flatOver F f)
    (x : Point f F σ)



    (L₁ L₂ : Lift f F h x) (φ : deformationHom f h x),
    Lift.vsub f F h hF x L₁ L₂ = φ ↔
      L₁ = Lift.vadd f F h hF x φ L₂)

end AlgebraicGeometry.AlgebraicSpace.Quot
