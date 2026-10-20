module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.CycleGroup.Principal
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.CycleGroup.ClosedPushforward
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.CycleGroup.FlatPullback
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Point.ClosureIntegral
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Separation.Transfer
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.ClosedSubspace.Noetherian
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.RationalFunction.Pullback

/-! # Flat pullback of principal cycles on algebraic spaces -/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open Function Set Topology TopologicalSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Hom

/-- The reduced closure of a generic point of `X`, regarded as a closed subspace. -/
noncomputable def flatComponent {S : Scheme.{u}} {B X : AlgebraicSpace S}
    [IsQuasiSeparated B] (pX : X ⟶ B) [QuasiSeparated pX]
    (η : genericPoints X) : ClosedSubspace X :=
  let _ := pX
  ClosedSubspace.ofι (PointClosure.ι η.1)

/-- The canonical irreducible component on a generic point is integral. -/
def isIntegral_flatComponent {S : Scheme.{u}} {B X : AlgebraicSpace S}
    [IsQuasiSeparated B] (pX : X ⟶ B) [QuasiSeparated pX]
    (η : genericPoints X) : IsIntegral (flatComponent pX η).X :=
  @PointClosure.integral S X η.1 (IsQuasiSeparated.of_quasiSeparated pX)

/-- The restriction of a flat morphism of good spaces to an irreducible
component of the source preserves dense opens. -/
theorem preservesDenseOpens_flatComponent {S : Scheme.{u}}
    {B X Y : AlgebraicSpace S} [IsQuasiSeparated B]
    (pX : X ⟶ B) [QuasiSeparated pX]
    (f : X ⟶ Y) (r : ℕ) [Flat f] [RelativeDimension f r] [IsIntegral Y]
    (η : genericPoints X) : PreservesDenseOpens ((flatComponent pX η).ι ≫ f) :=
  sorry

/-- The multiplicity-weighted pushforward of the principal cycle of the rational
unit restricted to an irreducible component of the source. -/
noncomputable def flatComponentPrincipal {S : Scheme.{u}}
    {B X Y : AlgebraicSpace S} [IsLocallyNoetherian B] [IsQuasiSeparated B]
    (pX : X ⟶ B) [QuasiSeparated pX] [LocallyOfFiniteType pX]
    (f : X ⟶ Y) (r : ℕ) [Flat f] [RelativeDimension f r] [IsIntegral Y]
    (g : (RationalFunction Y)ˣ) (η : genericPoints X) :
    Function.locallyFinsupp (Points X) ℤ :=
  (@ClosedSubspace.componentMultiplicity S X
      (LocallyOfFiniteType.isLocallyNoetherian pX) (ClosedSubspace.id X) η : ℤ) •
    closedImmersionCyclePushforward (flatComponent pX η).ι
      (hClosed := (flatComponent pX η).isClosedImmersion)
      (@principalCycle S (flatComponent pX η).X
        (@instIsLocallyNoetherian_of_isClosedImmersion S X
          (LocallyOfFiniteType.isLocallyNoetherian pX) (flatComponent pX η))
        (isIntegral_flatComponent pX η)
        (Units.map
          (rationalFunctionComap (preservesDenseOpens_flatComponent pX f r η)).toMonoidHom
          g))

/-- A component principal cycle is the multiplicity-weighted closed-subspace
pushforward of the principal cycle of the pulled-back rational unit. -/
theorem flatComponentPrincipal_eq {S : Scheme.{u}}
    {B X Y : AlgebraicSpace S} [IsLocallyNoetherian B] [IsQuasiSeparated B]
    (pX : X ⟶ B) [QuasiSeparated pX] [LocallyOfFiniteType pX]
    (f : X ⟶ Y) (r : ℕ) [Flat f] [RelativeDimension f r] [IsIntegral Y]
    (g : (RationalFunction Y)ˣ) (η : genericPoints X) :
    flatComponentPrincipal pX f r g η =
      (@ClosedSubspace.componentMultiplicity S X
          (LocallyOfFiniteType.isLocallyNoetherian pX)
          (ClosedSubspace.id X) η : ℤ) •
        closedImmersionCyclePushforward (flatComponent pX η).ι
          (hClosed := (flatComponent pX η).isClosedImmersion)
          (@principalCycle S (flatComponent pX η).X
            (@instIsLocallyNoetherian_of_isClosedImmersion S X
              (LocallyOfFiniteType.isLocallyNoetherian pX) (flatComponent pX η))
            (isIntegral_flatComponent pX η)
            (Units.map
              (rationalFunctionComap
                (preservesDenseOpens_flatComponent pX f r η)).toMonoidHom
              g)) :=
  rfl

/-- The family of multiplicity-weighted component principal cycles is locally
finite on `|X|`. -/
theorem locallyFinite_flatComponentPrincipal {S : Scheme.{u}}
    {B X Y : AlgebraicSpace S} [IsLocallyNoetherian B] [IsQuasiSeparated B]
    (pX : X ⟶ B) [QuasiSeparated pX] [LocallyOfFiniteType pX]
    (f : X ⟶ Y) (r : ℕ) [Flat f] [RelativeDimension f r] [IsIntegral Y]
    (g : (RationalFunction Y)ˣ) :
    LocallyFinite fun η : genericPoints X ↦
      (flatComponentPrincipal pX f r g η).support :=
  sorry

/-- Flat pullback of a principal cycle is the locally finite sum of the principal
cycles on the reduced irreducible components of the source, pushed forward and
weighted by their multiplicities. The target is integral of `δ`-dimension `k`,
and pullback along a flat morphism of relative dimension `r` yields a cycle of
dimension `k + r - 1`. -/
theorem flatPullback_principalDivisor {S : Scheme.{u}}
    {B X Y : AlgebraicSpace S} [UniversallyCatenary B] [IsQuasiSeparated B]
    (pY : Y ⟶ B) [QuasiSeparated pY] [LocallyOfFiniteType pY]
    (pX : X ⟶ B) [QuasiSeparated pX] [LocallyOfFiniteType pX]
    (δ : Points B → ℤ) [IsDimensionFunction δ]
    (f : X ⟶ Y) (r : ℕ) [Flat f] [RelativeDimension f r]
    (hf : f ≫ pY = pX) [IsIntegral Y] (k : ℤ)
    (hY : closedSubspaceDeltaDimension pY δ (ClosedSubspace.id Y) = (k : EInt))
    (g : (RationalFunction Y)ˣ) :
    (flatPullbackHom pY pX δ f r hf (k - 1)
        ⟨@principalCycle S Y (LocallyOfFiniteType.isLocallyNoetherian pY)
          inferInstance g,
          principalCycle_mem pY δ k hY g⟩ :
        Function.locallyFinsupp (Points X) ℤ) =
      AlgebraicCycle.locallyFiniteSum
        (fun η : genericPoints X ↦
          flatComponentPrincipal pX f r g η)
        (locallyFinite_flatComponentPrincipal pX f r g) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Hom
