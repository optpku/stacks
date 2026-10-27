/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.CycleGroup.FlatPullback.Principal
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Etale.Flat
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Etale.RelativeDimension
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Points.Irreducible
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Separation.Absolute.Relative

/-! # Étale pullback of principal cycles on algebraic spaces -/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open Function Set Topology TopologicalSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Hom

/-- The unweighted pushforward of the principal cycle of a rational unit restricted
to a reduced irreducible component of the source of an étale morphism. -/
def etaleComponentDivisorPushforward {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    [IsLocallyNoetherian X] [IsQuasiSeparated X]
    (f : X ⟶ Y) [Etale f] [IsIntegral Y] (g : (RationalFunction Y)ˣ)
    (η : genericPoints X) : Function.locallyFinsupp (Points X) ℤ :=
  let C := flatComponent (𝟙 X) η
  closedImmersionCyclePushforward C.ι (hClosed := C.isClosedImmersion)
    (@principalCycle S C.X
      (instIsLocallyNoetherian_of_isClosedImmersion C)
      (isIntegral_flatComponent (𝟙 X) η)
      (Units.map
        (rationalFunctionComap
          (preservesDenseOpens_flatComponent (𝟙 X) f 0 η)).toMonoidHom g))

/-- The unweighted component cycle is the closed-immersion pushforward of the
principal cycle of the pulled-back rational unit. -/
theorem etaleComponentDivisorPushforward_eq {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    [IsLocallyNoetherian X] [IsQuasiSeparated X]
    (f : X ⟶ Y) [Etale f] [IsIntegral Y] (g : (RationalFunction Y)ˣ)
    (η : genericPoints X) :
    etaleComponentDivisorPushforward f g η =
      let C := flatComponent (𝟙 X) η
      closedImmersionCyclePushforward C.ι (hClosed := C.isClosedImmersion)
        (@principalCycle S C.X
          (instIsLocallyNoetherian_of_isClosedImmersion C)
          (isIntegral_flatComponent (𝟙 X) η)
          (Units.map
            (rationalFunctionComap
              (preservesDenseOpens_flatComponent (𝟙 X) f 0 η)).toMonoidHom g)) :=
  rfl

/-- For an étale morphism to an integral space, the multiplicity-weighted
component principal cycle equals the unweighted component principal cycle. -/
theorem flatComponentPrincipal_eq_etaleComponentDivisorPushforward
    {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    [IsLocallyNoetherian X] [IsQuasiSeparated X]
    (f : X ⟶ Y) [Etale f] [IsIntegral Y] (g : (RationalFunction Y)ˣ)
    (η : genericPoints X) :
    flatComponentPrincipal (𝟙 X) f 0 g η = etaleComponentDivisorPushforward f g η :=
  sorry

/-- The family of unweighted component principal cycles of an étale morphism
to an integral space is locally finite on the source. -/
theorem locallyFinite_etaleComponentDivisorPushforward
    {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    [IsLocallyNoetherian X] [IsQuasiSeparated X]
    (f : X ⟶ Y) [Etale f] [IsIntegral Y] (g : (RationalFunction Y)ˣ) :
    LocallyFinite fun η : genericPoints X ↦
      (etaleComponentDivisorPushforward f g η).support :=
  sorry

/-- Étale pullback of a principal cycle is the locally finite unweighted sum of
the principal cycles on the reduced irreducible components of the source,
pushed forward along their closed immersions. For good spaces over a universally
catenary base with dimension function, pullback is taken in degree one less than
the dimension of the integral target. -/
theorem etalePullback_principalDivisor {S : Scheme.{u}} {B X Y : AlgebraicSpace S}
    [UniversallyCatenary B] [IsAbsolutelyQuasiSeparated B]
    (pY : Y ⟶ B) [QuasiSeparated pY] [LocallyOfFiniteType pY]
    (pX : X ⟶ B) [QuasiSeparated pX] [LocallyOfFiniteType pX]
    (δ : Points B → ℤ) [IsDimensionFunction δ]
    (f : X ⟶ Y) [Etale f] (hf : f ≫ pY = pX)
    [IsIntegral Y] (g : (RationalFunction Y)ˣ) :
    let n := deltaDimension pY δ (univIrreducibleClosed Y)
    flatPullback pY pX δ f 0 hf (n - 1)
        (@principalCycle S Y (LocallyOfFiniteType.isLocallyNoetherian pY)
          inferInstance g) =
      AlgebraicCycle.locallyFiniteSum
        (fun η : genericPoints X ↦
          @etaleComponentDivisorPushforward S X Y
            (LocallyOfFiniteType.isLocallyNoetherian pX)
            (IsQuasiSeparated.of_quasiSeparated pX) f inferInstance inferInstance g η)
        (@locallyFinite_etaleComponentDivisorPushforward S X Y
          (LocallyOfFiniteType.isLocallyNoetherian pX)
          (IsQuasiSeparated.of_quasiSeparated pX) f inferInstance inferInstance g) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Hom
