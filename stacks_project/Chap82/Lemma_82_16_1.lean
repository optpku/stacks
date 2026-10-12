/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Point.ClosureIntegral

public import Mathlib.Topology.LocallyFinite
public import Mathlib.Topology.LocallyFinsupp
public import ReasLib.AlgebraicGeometry.AlgebraicCycle.LocallyFiniteSum
public import stacks_project.Chap67.Definition_67_18_1_Dominant
public import stacks_project.Chap67.Lemma_67_4_9
public import stacks_project.Chap67.Lemma_67_23_5
public import stacks_project.Chap68.Lemma_68_12_8_Decent
public import stacks_project.Chap69.Lemma_69_12_7_Coherent
public import stacks_project.Chap72.Definition_72_6_9_Principal
public import stacks_project.Chap72.Lemma_72_4_7_IntegralClosed
public import stacks_project.Chap72.Lemma_72_6_6
public import stacks_project.Chap82.Lemma_82_10_4_Pullback
public import stacks_project.Chap82.Remark_82_5_1_IrreducibleComponent

/-!
# Flat pullback of principal divisors on algebraic spaces

In Situation 82.2.1, the multiplicity-weighted flat pullback of a principal
divisor along a flat morphism of relative dimension `r` of good algebraic
spaces is the locally finite sum of the pushforwards of the induced principal
divisors on the irreducible components of the source.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open Function Set Topology TopologicalSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

namespace Hom

/-- The canonical irreducible component of `X` on a generic point, as a closed
subspace of `X` via `ClosedSubspace.id`. -/
noncomputable def flatComponent {S : Scheme.{u}} {B X : AlgebraicSpace S}
    [IsQuasiSeparated B] (pX : X ⟶ B) [QuasiSeparated pX]
    (η : genericPoints X) : ClosedSubspace X :=
  let _ := pX
  ClosedSubspace.ofι (PointClosure.ι η.1)

/-- The canonical irreducible component on a generic point is integral. -/
theorem isIntegral_flatComponent {S : Scheme.{u}} {B X : AlgebraicSpace S}
    [IsQuasiSeparated B] (pX : X ⟶ B) [QuasiSeparated pX]
    (η : genericPoints X) : IsIntegral (flatComponent pX η).X := by
  -- Local instance justification (proof-local temporary data): The supplied good structure map pX gives quasi-separatedness of X, so its actual generic point closure is integral.
  letI := IsQuasiSeparated.of_quasiSeparated pX
  exact PointClosure.integral η.1

/-- The restriction of a flat morphism of good spaces to an irreducible
component of the source is dominant. -/
theorem dominant_flatComponent {S : Scheme.{u}} {B X Y : AlgebraicSpace S}
    [IsQuasiSeparated B] (pX : X ⟶ B) [QuasiSeparated pX]
    (f : X ⟶ Y) (r : ℕ) [Flat f] [RelativeDimension f r] [IsIntegral Y]
    (η : genericPoints X) : Dominant ((flatComponent pX η).ι ≫ f) :=
  sorry

/-- The restriction of a flat morphism of good spaces to an irreducible
component of the source preserves dense opens. -/
theorem preservesDenseOpens_flatComponent {S : Scheme.{u}}
    {B X Y : AlgebraicSpace S} [IsQuasiSeparated B]
    (pX : X ⟶ B) [QuasiSeparated pX]
    (f : X ⟶ Y) (r : ℕ) [Flat f] [RelativeDimension f r] [IsIntegral Y]
    (η : genericPoints X) : PreservesDenseOpens ((flatComponent pX η).ι ≫ f) :=
  sorry

/-- An irreducible component of `X` has `δ`-dimension `k + r` when `Y` is
integral of `δ`-dimension `k` and `f` is flat of relative dimension `r`. -/
theorem flatComponent_deltaDimension {S : Scheme.{u}}
    {B X Y : AlgebraicSpace S} [UniversallyCatenary B] [IsQuasiSeparated B]
    (pY : Y ⟶ B) [QuasiSeparated pY] [LocallyOfFiniteType pY]
    (pX : X ⟶ B) [QuasiSeparated pX] [LocallyOfFiniteType pX]
    (δ : Points B → ℤ) [IsDimensionFunction δ]
    (f : X ⟶ Y) (r : ℕ) [Flat f] [RelativeDimension f r]
    (hf : f ≫ pY = pX) [IsIntegral Y] (k : ℤ)
    (hY : closedSubspaceDeltaDimension pY δ (ClosedSubspace.id Y) = (k : EInt))
    (η : genericPoints X) :
    closedSubspaceDeltaDimension pX δ (flatComponent pX η) =
      (k : EInt) + (r : EInt) :=
  sorry

/-- The singleton cycles at generic points of prime divisors in a principal
Weil divisor form a locally finite family. -/
theorem principalCycle_locallyFinite {S : Scheme.{u}} {X : AlgebraicSpace S}
    [IsLocallyNoetherian X] [IsIntegral X] (φ : (RationalFunction X)ˣ) :
    LocallyFinite fun Z : PrimeDivisor X ↦
      (@Function.locallyFinsuppWithin.single (Points X) _ ℤ (Classical.decEq _) _
        Z.genericPoint ((principalWeilDivisor X φ).coeff Z)).support :=
  sorry

/-- The ungraded principal divisor cycle of a rational unit, as the locally
finite sum of coefficient-weighted generic points of prime divisors. -/
noncomputable def principalCycle {S : Scheme.{u}} {X : AlgebraicSpace S}
    [IsLocallyNoetherian X] [IsIntegral X] (φ : (RationalFunction X)ˣ) :
    Function.locallyFinsupp (Points X) ℤ :=
  AlgebraicCycle.locallyFiniteSum
    (fun Z : PrimeDivisor X ↦
      @Function.locallyFinsuppWithin.single (Points X) _ ℤ (Classical.decEq _) _
        Z.genericPoint ((principalWeilDivisor X φ).coeff Z))
    (principalCycle_locallyFinite φ)

/-- The ungraded principal divisor cycle is the locally finite sum of its
prime-divisor singleton cycles. -/
theorem principalCycle_eq {S : Scheme.{u}} {X : AlgebraicSpace S}
    [IsLocallyNoetherian X] [IsIntegral X] (φ : (RationalFunction X)ˣ) :
    principalCycle φ =
      AlgebraicCycle.locallyFiniteSum
        (fun Z : PrimeDivisor X ↦
          @Function.locallyFinsuppWithin.single (Points X) _ ℤ (Classical.decEq _) _
            Z.genericPoint ((principalWeilDivisor X φ).coeff Z))
        (principalCycle_locallyFinite φ) :=
  sorry

/-- If `dim_δ(Y) = k`, then the ungraded principal divisor cycle of `g` is a
`(k - 1)`-cycle on `Y`. -/
theorem principalCycle_mem {S : Scheme.{u}} {B Y : AlgebraicSpace S}
    [UniversallyCatenary B] [IsQuasiSeparated B]
    (pY : Y ⟶ B) [QuasiSeparated pY] [LocallyOfFiniteType pY]
    (δ : Points B → ℤ) [IsDimensionFunction δ] [IsIntegral Y] (k : ℤ)
    (hY : closedSubspaceDeltaDimension pY δ (ClosedSubspace.id Y) = (k : EInt))
    (g : (RationalFunction Y)ˣ) :
    @principalCycle S Y (LocallyOfFiniteType.isLocallyNoetherian pY) inferInstance g ∈
      cycleGroup pY δ (k - 1) :=
  sorry

/-- Weight-1 pushforward along a closed subspace inclusion has locally finite
support. -/
theorem closedSubspacePushforward_locallyFinite {S : Scheme.{u}}
    {X : AlgebraicSpace S} (W : ClosedSubspace X)
    (α : Function.locallyFinsupp (Points W.X) ℤ) :
    LocallyFiniteSupport fun x : Points X ↦
      ∑ᶠ y ∈ Points.map W.ι ⁻¹' {x}, α y :=
  sorry

/-- Weight-1 pushforward of a locally finite cycle along a closed subspace
inclusion. -/
noncomputable def closedSubspacePushforward {S : Scheme.{u}}
    {X : AlgebraicSpace S} (W : ClosedSubspace X)
    (α : Function.locallyFinsupp (Points W.X) ℤ) :
    Function.locallyFinsupp (Points X) ℤ where
  toFun := fun x ↦ ∑ᶠ y ∈ Points.map W.ι ⁻¹' {x}, α y
  supportWithinDomain' := Set.subset_univ _
  supportLocallyFiniteWithinDomain' := fun x _ ↦
    closedSubspacePushforward_locallyFinite W α x

/-- Closed-subspace pushforward evaluates by a weight-1 finsum on the fibre of
`Points.map W.ι`. -/
theorem closedSubspacePushforward_eq {S : Scheme.{u}} {X : AlgebraicSpace S}
    (W : ClosedSubspace X) (α : Function.locallyFinsupp (Points W.X) ℤ)
    (x : Points X) :
    closedSubspacePushforward W α x = ∑ᶠ y ∈ Points.map W.ι ⁻¹' {x}, α y :=
  sorry

/-- The cycle `m_{X',X} (X' → X)_* div_{X'}(g ∘ f|_{X'})` on an irreducible
component of `X` in the sense of Remark 82.5.1. -/
noncomputable def flatComponentPrincipal {S : Scheme.{u}}
    {B X Y : AlgebraicSpace S} [UniversallyCatenary B] [IsQuasiSeparated B]
    (pY : Y ⟶ B) [QuasiSeparated pY] [LocallyOfFiniteType pY]
    (pX : X ⟶ B) [QuasiSeparated pX] [LocallyOfFiniteType pX]
    (δ : Points B → ℤ) [IsDimensionFunction δ]
    (f : X ⟶ Y) (r : ℕ) [Flat f] [RelativeDimension f r]
    (hf : f ≫ pY = pX) [IsIntegral Y] (k : ℤ)
    (hY : closedSubspaceDeltaDimension pY δ (ClosedSubspace.id Y) = (k : EInt))
    (g : (RationalFunction Y)ˣ) (η : genericPoints X) :
    Function.locallyFinsupp (Points X) ℤ :=
  (@ClosedSubspace.componentMultiplicity S X
      (LocallyOfFiniteType.isLocallyNoetherian pX) (ClosedSubspace.id X) η : ℤ) •
    closedSubspacePushforward (flatComponent pX η)
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
    {B X Y : AlgebraicSpace S} [UniversallyCatenary B] [IsQuasiSeparated B]
    (pY : Y ⟶ B) [QuasiSeparated pY] [LocallyOfFiniteType pY]
    (pX : X ⟶ B) [QuasiSeparated pX] [LocallyOfFiniteType pX]
    (δ : Points B → ℤ) [IsDimensionFunction δ]
    (f : X ⟶ Y) (r : ℕ) [Flat f] [RelativeDimension f r]
    (hf : f ≫ pY = pX) [IsIntegral Y] (k : ℤ)
    (hY : closedSubspaceDeltaDimension pY δ (ClosedSubspace.id Y) = (k : EInt))
    (g : (RationalFunction Y)ˣ) (η : genericPoints X) :
    flatComponentPrincipal pY pX δ f r hf k hY g η =
      (@ClosedSubspace.componentMultiplicity S X
          (LocallyOfFiniteType.isLocallyNoetherian pX)
          (ClosedSubspace.id X) η : ℤ) •
        closedSubspacePushforward (flatComponent pX η)
          (@principalCycle S (flatComponent pX η).X
            (@instIsLocallyNoetherian_of_isClosedImmersion S X
              (LocallyOfFiniteType.isLocallyNoetherian pX) (flatComponent pX η))
            (isIntegral_flatComponent pX η)
            (Units.map
              (rationalFunctionComap
                (preservesDenseOpens_flatComponent pX f r η)).toMonoidHom
              g)) :=
  sorry

/-- The family of multiplicity-weighted component principal cycles is locally
finite on `|X|`. -/
theorem locallyFinite_flatComponentPrincipal {S : Scheme.{u}}
    {B X Y : AlgebraicSpace S} [UniversallyCatenary B] [IsQuasiSeparated B]
    (pY : Y ⟶ B) [QuasiSeparated pY] [LocallyOfFiniteType pY]
    (pX : X ⟶ B) [QuasiSeparated pX] [LocallyOfFiniteType pX]
    (δ : Points B → ℤ) [IsDimensionFunction δ]
    (f : X ⟶ Y) (r : ℕ) [Flat f] [RelativeDimension f r]
    (hf : f ≫ pY = pX) [IsIntegral Y] (k : ℤ)
    (hY : closedSubspaceDeltaDimension pY δ (ClosedSubspace.id Y) = (k : EInt))
    (g : (RationalFunction Y)ˣ) :
    LocallyFinite fun η : genericPoints X ↦
      (flatComponentPrincipal pY pX δ f r hf k hY g η).support :=
  sorry

/-- Lemma 82.16.1: In Situation 82.2.1 let `X, Y / B` be good. Assume `Y`
integral with `dim_δ(Y) = k`. Let `f : X ⟶ Y` be a flat morphism of relative
dimension `r`. Then for `g ∈ R(Y)ˣ` we have
`f^* div_Y(g) = ∑ m_{X',X} (X' → X)_* div_{X'}(g ∘ f|_{X'})`
as `(k + r - 1)`-cycles on `X`, where the sum is over the irreducible
components `X'` of `X` and `m_{X',X}` is the multiplicity of `X'` in `X`.
The left-hand side is `flatPullbackHom` of the principal cycle of `g` in
degree `(k - 1) + r`; each summand is the multiplicity-weighted
closed-subspace pushforward of the principal cycle of the units-comap of `g`
along the component restriction. -/
@[stacks 0EQA]
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
          flatComponentPrincipal pY pX δ f r hf k hY g η)
        (locallyFinite_flatComponentPrincipal pY pX δ f r hf k hY g) :=
  sorry

end Hom

end AlgebraicGeometry.AlgebraicSpace
