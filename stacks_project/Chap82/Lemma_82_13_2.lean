module

public import ReasLib.AlgebraicGeometry.AlgebraicCycle.LocallyFiniteSum
public import stacks_project.Chap66.Lemma_66_16_4_Etale
public import stacks_project.Chap67.Definition_67_18_1_Dominant
public import stacks_project.Chap67.Definition_67_33_2_RelativeDimension
public import stacks_project.Chap67.Lemma_67_4_9
public import stacks_project.Chap67.Lemma_67_30_5_Flat
public import stacks_project.Chap69.Lemma_69_12_7_Coherent
public import stacks_project.Chap71.Lemma_71_6_12_Pullback
public import stacks_project.Chap82.Definition_82_15_1_ClosedPushforward
public import stacks_project.Chap82.Definition_82_17_1_Cycle
public import stacks_project.Chap82.Remark_82_5_1_IrreducibleComponent

/-!
# Étale pullback of principal divisors on algebraic spaces

In Situation 82.2.1, the unweighted étale pullback of a principal divisor along
an étale morphism of good algebraic spaces is the sum of the pushforwards of
the induced principal divisors on the irreducible components of the source.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open Function Set Topology TopologicalSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

namespace Hom

/-- The map on rational units induced by a morphism that preserves dense opens. -/
def rationalFunctionUnitsComap {S : Scheme.{u}} {X Y : AlgebraicSpace S} {h : X ⟶ Y}
    (hh : PreservesDenseOpens h) :
    (RationalFunction Y)ˣ →* (RationalFunction X)ˣ :=
  Units.map (rationalFunctionComap hh).toMonoidHom

/-- The underlying rational function of a pulled-back unit is the ring-hom pullback. -/
theorem rationalFunctionUnitsComap_coe {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    {h : X ⟶ Y} (hh : PreservesDenseOpens h) (g : (RationalFunction Y)ˣ) :
    (rationalFunctionUnitsComap hh g : RationalFunction X) =
      rationalFunctionComap hh (g : RationalFunction Y) :=
  sorry

/-- Coefficients of the unweighted étale inverse-image pullback are locally finite. -/
theorem etalePullbackCycle_locallyFiniteSupport {S : Scheme.{u}}
    {X Y : AlgebraicSpace S} (f : X ⟶ Y) [Etale f]
    (α : Function.locallyFinsupp (Points Y) ℤ) :
    LocallyFiniteSupport fun x : Points X ↦
      ∑ᶠ y : Points Y,
        α y *
          @ite ℤ
            (x ∈
              Points.map (((ClosedSubspaceStructure.reduced
                    (Closeds.closure ({y} : Set (Points Y)))).subspace).inverseImage f).ι ''
                genericPoints (((ClosedSubspaceStructure.reduced
                    (Closeds.closure ({y} : Set (Points Y)))).subspace).inverseImage f).X)
            (Classical.propDecidable _) 1 0 :=
  sorry

/-- Multiplicity-1 coefficient form of étale pullback of a cycle, as in
Lemma 82.10.3: the coefficient at `x` is the sum of `α y` over those `y` for
which `x` is the image of a generic point of the étale inverse image of the
reduced closure of `y`. This is not a second Definition 82.10.1 owner. -/
def etalePullbackCycle {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) [Etale f] (α : Function.locallyFinsupp (Points Y) ℤ) :
    Function.locallyFinsupp (Points X) ℤ where
  toFun x :=
    ∑ᶠ y : Points Y,
      α y *
        @ite ℤ
          (x ∈
            Points.map (((ClosedSubspaceStructure.reduced
                    (Closeds.closure ({y} : Set (Points Y)))).subspace).inverseImage f).ι ''
              genericPoints (((ClosedSubspaceStructure.reduced
                    (Closeds.closure ({y} : Set (Points Y)))).subspace).inverseImage f).X)
          (Classical.propDecidable _) 1 0
  supportWithinDomain' := Set.subset_univ _
  supportLocallyFiniteWithinDomain' x _ :=
    etalePullbackCycle_locallyFiniteSupport f α x

/-- Coefficients of the unweighted étale pullback are the inverse-image component
indicator of Lemma 82.10.3, weighted by the input cycle. -/
theorem etalePullbackCycle_apply {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) [Etale f] (α : Function.locallyFinsupp (Points Y) ℤ) (x : Points X) :
    etalePullbackCycle f α x =
      ∑ᶠ y : Points Y,
        α y *
          @ite ℤ
            (x ∈
              Points.map (((ClosedSubspaceStructure.reduced
                    (Closeds.closure ({y} : Set (Points Y)))).subspace).inverseImage f).ι ''
                genericPoints (((ClosedSubspaceStructure.reduced
                    (Closeds.closure ({y} : Set (Points Y)))).subspace).inverseImage f).X)
            (Classical.propDecidable _) 1 0 :=
  sorry

/-- The restriction of an étale morphism of good spaces to an irreducible
component of the source preserves dense opens. -/
theorem preservesDenseOpens_etaleComponent {S : Scheme.{u}}
    {B X Y : AlgebraicSpace S} [IsQuasiSeparated B]
    (pX : X ⟶ B) [QuasiSeparated pX] (f : X ⟶ Y) [Etale f] [IsIntegral Y]
    (η : genericPoints X) :
    PreservesDenseOpens
      ((@ClosedSubspace.irreducibleComponent S X (ClosedSubspace.id X)
          (@instIsDecent_of_isQuasiSeparated S X
            (IsQuasiSeparated.of_quasiSeparated pX)) η).ι ≫ f) :=
  sorry

/-- The restriction of an étale morphism of good spaces to an irreducible
component of the source is dominant. -/
theorem dominant_etaleComponent {S : Scheme.{u}} {B X Y : AlgebraicSpace S}
    [IsQuasiSeparated B] (pX : X ⟶ B) [QuasiSeparated pX]
    (f : X ⟶ Y) [Etale f] [IsIntegral Y] (η : genericPoints X) :
    Dominant
      ((@ClosedSubspace.irreducibleComponent S X (ClosedSubspace.id X)
          (@instIsDecent_of_isQuasiSeparated S X
            (IsQuasiSeparated.of_quasiSeparated pX)) η).ι ≫ f) :=
  sorry

/-- The cycle `(X' → X)_* div_{X'}(g ∘ f|_{X'})` on an irreducible component of
`X` in the sense of Remark 82.5.1. -/
def etaleComponentDivisorPushforward {S : Scheme.{u}} {B X Y : AlgebraicSpace S}
    [UniversallyCatenary B] [IsQuasiSeparated B]
    (pX : X ⟶ B) [QuasiSeparated pX] [LocallyOfFiniteType pX]
    (f : X ⟶ Y) [Etale f] [IsIntegral Y] (g : (RationalFunction Y)ˣ)
    (η : genericPoints X) : Function.locallyFinsupp (Points X) ℤ :=
  let X' :=
    @ClosedSubspace.irreducibleComponent S X (ClosedSubspace.id X)
      (@instIsDecent_of_isQuasiSeparated S X
        (IsQuasiSeparated.of_quasiSeparated pX)) η
  let hInt :=
    (@ClosedSubspace.irreducibleComponent_spec S X (ClosedSubspace.id X)
      (@instIsDecent_of_isQuasiSeparated S X
        (IsQuasiSeparated.of_quasiSeparated pX)) η).1
  closedImmersionPushforwardCycle X'
    (@WeilDivisor.toCycle S X'.X hInt.toIsDecent
      (@WeilDivisor.ofRationalUnit S X'.X
        (@instIsLocallyNoetherian_of_isClosedImmersion S X
          (LocallyOfFiniteType.isLocallyNoetherian pX) X')
        hInt
        (rationalFunctionUnitsComap (preservesDenseOpens_etaleComponent pX f η) g)))

/-- The component pushforward cycle is closed-immersion pushforward of the
principal divisor of the pulled-back rational unit. -/
theorem etaleComponentDivisorPushforward_eq {S : Scheme.{u}}
    {B X Y : AlgebraicSpace S} [UniversallyCatenary B] [IsQuasiSeparated B]
    (pX : X ⟶ B) [QuasiSeparated pX] [LocallyOfFiniteType pX]
    (f : X ⟶ Y) [Etale f] [IsIntegral Y] (g : (RationalFunction Y)ˣ)
    (η : genericPoints X) :
    etaleComponentDivisorPushforward pX f g η =
      let X' :=
        @ClosedSubspace.irreducibleComponent S X (ClosedSubspace.id X)
          (@instIsDecent_of_isQuasiSeparated S X
            (IsQuasiSeparated.of_quasiSeparated pX)) η
      let hInt :=
        (@ClosedSubspace.irreducibleComponent_spec S X (ClosedSubspace.id X)
          (@instIsDecent_of_isQuasiSeparated S X
            (IsQuasiSeparated.of_quasiSeparated pX)) η).1
      closedImmersionPushforwardCycle X'
        (@WeilDivisor.toCycle S X'.X hInt.toIsDecent
          (@WeilDivisor.ofRationalUnit S X'.X
            (@instIsLocallyNoetherian_of_isClosedImmersion S X
              (LocallyOfFiniteType.isLocallyNoetherian pX) X')
            hInt
            (rationalFunctionUnitsComap
              (preservesDenseOpens_etaleComponent pX f η) g))) :=
  sorry

/-- The family of component principal-divisor pushforwards is locally finite on
`|X|`. -/
theorem locallyFinite_etaleComponentDivisorPushforward {S : Scheme.{u}}
    {B X Y : AlgebraicSpace S} [UniversallyCatenary B] [IsQuasiSeparated B]
    (pX : X ⟶ B) [QuasiSeparated pX] [LocallyOfFiniteType pX]
    (f : X ⟶ Y) [Etale f] [IsIntegral Y] (g : (RationalFunction Y)ˣ) :
    LocallyFinite fun η : genericPoints X ↦
      (etaleComponentDivisorPushforward pX f g η).support :=
  sorry

/-- Lemma 82.13.2: In Situation 82.2.1 let `f : X ⟶ Y` be an étale morphism of
good algebraic spaces over `B`. Assume `Y` is integral. Let `g ∈ R(Y)ˣ`. As
cycles on `X` one has
`f^*(div_Y(g)) = ∑_{X'} (X' → X)_* div_{X'}(g ∘ f|_{X'})`,
the sum running over the irreducible components of `X` in the sense of
Remark 82.5.1. The left-hand side is the unweighted étale pullback of the
`(n-1)`-cycle `div_Y(g)` (Definition 82.10.1 with multiplicities `1` by
Lemma 82.10.3); each component restriction is dominant, so the composed
rational units are defined; both sides are `(n-1)`-cycles for `n = dim_δ(Y)`. -/
@[stacks 0EQ2]
theorem etalePullback_principalDivisor {S : Scheme.{u}} {B X Y : AlgebraicSpace S}
    [UniversallyCatenary B] [IsQuasiSeparated B]
    (pY : Y ⟶ B) [QuasiSeparated pY] [LocallyOfFiniteType pY]
    (pX : X ⟶ B) [QuasiSeparated pX] [LocallyOfFiniteType pX]
    (δ : Points B → ℤ) [IsDimensionFunction δ]
    (f : X ⟶ Y) [Etale f] [Flat f] [RelativeDimension f 0]
    (hf : f ≫ pY = pX) [IsIntegral Y] (g : (RationalFunction Y)ˣ) :
    etalePullbackCycle f
        (WeilDivisor.toCycle
          (@WeilDivisor.ofRationalUnit S Y
            (LocallyOfFiniteType.isLocallyNoetherian pY) inferInstance g)) =
      AlgebraicCycle.locallyFiniteSum
        (fun η : genericPoints X ↦ etaleComponentDivisorPushforward pX f g η)
        (locallyFinite_etaleComponentDivisorPushforward pX f g) :=
  sorry

end Hom

end AlgebraicGeometry.AlgebraicSpace
