/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Blowup.RelativeProj
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Divisor.EffectiveCartier.AssociatedSheaf
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.ClosedImmersion.Complement
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Open.InverseImage
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Pullback.Sections

/-!
# Exceptional divisors of Rees blowups

For a blowup presentation `π`, write `E = exceptionalDivisor π` and
`L(n) = π.reesTwist.twistModule n`. The canonical comparison `L(-1) ≅ 𝒪(E)`
is normalized by the degree-one Rees map and the multiplication of twists.
-/

@[expose] public section

open CategoryTheory CategoryTheory.MonoidalCategory
open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open SheafOfModules.RingedSite

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Blowup

variable {S : Scheme.{u}} {X : AlgebraicSpace S} {I : IdealSubobject X}
  [IsQuasiCoherent I]

/-- The associated divisor sheaf of the exceptional divisor, with explicit evidence that
the exceptional divisor is effective Cartier. -/
def exceptionalAssociatedSheaf (π : Blowup X I)
    (hE : IsEffectiveCartierDivisor (exceptionalDivisor π).ι) : π.space.Modules :=
  @ClosedSubspace.associatedSheaf S π.space (exceptionalDivisor π) hE

/-- The canonical unit morphism from the structure module into the degree-zero twist,
induced by the degree-zero piece of the Rees algebra. -/
def twistZeroUnit (π : Blowup X I) :
    SheafOfModules.unit (structureSheaf π.space) ⟶ π.reesTwist.twistModule 0 :=
  Modules.structureModulePullbackInv π.hom ≫
    (Modules.pullback π.hom).map (reesPowZeroHom I) ≫ π.reesTwist.canonicalHom 0

set_option backward.privateInPublic true in
/-- Evaluation pairs the associated divisor sheaf with the exceptional ideal to give
the structure module. -/
private def exceptionalEvaluation (π : Blowup X I)
    (hE : IsEffectiveCartierDivisor (exceptionalDivisor π).ι) :
    exceptionalAssociatedSheaf π hE ⊗ Hom.idealSheaf (exceptionalDivisor π).ι ⟶
      SheafOfModules.unit (structureSheaf π.space) :=
  (@IdealSubobject.associatedSheafTensorNegIso S π.space
    (Hom.idealSheafSubobject (exceptionalDivisor π).ι) hE.invertibleIdealSheaf).hom ≫
      (Modules.structureModuleIsoTensorUnit π.space).inv

-- The predicate exposes the evaluation equation without making its one-use map public.
set_option backward.privateInPublic true in
/-- A negative-twist comparison is canonical when the degree-one comparison factors the
Rees map through the exceptional ideal and twist multiplication agrees with divisor
evaluation and the canonical degree-zero unit. -/
def IsExceptionalTwistComparison (π : Blowup X I)
    (hE : IsEffectiveCartierDivisor (exceptionalDivisor π).ι)
    (e : π.reesTwist.twistModule (-1) ≅ exceptionalAssociatedSheaf π hE)
    (e1 : Hom.idealSheaf (exceptionalDivisor π).ι ≅ π.reesTwist.twistModule 1) : Prop :=
  π.reesTwist.canonicalHom 1 ≫ e1.inv ≫ Hom.idealSheafι (exceptionalDivisor π).ι =
      (Modules.pullback π.hom).map (I.pow 1).arrow ≫ IdealSubobject.pullbackUnit π.hom ∧
    ((π.reesTwist.twistModuleIso (-1)).hom ⊗ₘ
        (Modules.liftModuleMap e1.hom ≫ (π.reesTwist.twistModuleIso 1).hom)) ≫
        GradedAlgebraSheaf.mulHom π.reesTwist.twistAlgebra (-1) 1 ≫
        eqToHom (congrArg π.reesTwist.twistAlgebra.obj
          (show (-1 : ℤ) + 1 = 0 from by decide)) ≫
        (π.reesTwist.twistModuleIso 0).inv =
      RelativeProj.liftModuleTensorHom (π.reesTwist.twistModule (-1))
          (Hom.idealSheaf (exceptionalDivisor π).ι) ≫
        Modules.liftModuleMap
          ((e.hom ⊗ₘ 𝟙 (Hom.idealSheaf (exceptionalDivisor π).ι)) ≫
            exceptionalEvaluation π hE ≫ twistZeroUnit π)

/-- A Rees blowup is an isomorphism away from its center, its exceptional divisor is
effective Cartier, and its negative first twist has a unique comparison with the
associated divisor sheaf compatible with the canonical Rees map and twist multiplication. -/
theorem properties (π : Blowup X I) :
    IsIso (openInverseImageTo π.hom (closedImmersionComplementι (subschemeι I))) ∧
      ∃ hE : IsEffectiveCartierDivisor (exceptionalDivisor π).ι,
        ∃! e : π.reesTwist.twistModule (-1) ≅ exceptionalAssociatedSheaf π hE,
          ∃ e1 : Hom.idealSheaf (exceptionalDivisor π).ι ≅ π.reesTwist.twistModule 1,
            IsExceptionalTwistComparison π hE e e1 :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Blowup
