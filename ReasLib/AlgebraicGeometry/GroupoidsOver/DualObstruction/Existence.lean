/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.GroupoidsOver.DualObstruction.NaiveCotangent
public import ReasLib.AlgebraicGeometry.GroupoidsOver.CanonicalElement

/-!
# Existence of a naive cotangent obstruction class

Connecting-compatible dual obstruction data admit a naive cotangent class
recovering every obstruction and matching the canonical tangent element.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Functor
open AlgebraicGeometry.GroupoidsOver
open scoped NaiveCotangent

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidsOver

variable {S : Scheme.{u}} [IsLocallyNoetherian S]
variable {X : GroupoidsOver S} [HasStrongRimSchlessinger X]

namespace DualObstruction

/-- Dual obstruction data compatible with connecting maps admit a class in
`H¹(K ⊗^L NL{A⁄Λ})` whose extension evaluations recover every obstruction
and whose Kähler evaluation is the image of the canonical tangent element. -/
theorem exists_naiveCotangentClass (𝒟 : DualObstruction X)
    (h : IsConnectingCompatible 𝒟) :
    ∃ ξ : homologyTensorDerived 𝒟.complex 1
        (Algebra.naiveCotangentObject 𝒟.base 𝒟.carrier),
      RecoversObstructions 𝒟 ξ ∧
      ULift.up (𝒟.evalKaehler ξ) =
        𝒟.tangentIso.hom.app 𝒟.kaehler
          (canonicalElement 𝒟.baseHom 𝒟.factor
            (Spectrum.ObjectOverSpec.toFiber 𝒟.toObjectOverSpec) inferInstance) :=
  sorry

end DualObstruction

end AlgebraicGeometry.GroupoidsOver
