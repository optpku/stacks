module

public import ReasLib.AlgebraicGeometry.LocalizedChern.DerivedEnvelopeCaps
public import ReasLib.AlgebraicGeometry.BivariantClass.LocalizedExtension
public import ReasLib.AlgebraicGeometry.BivariantClass.GysinAtInfinity
public import ReasLib.AlgebraicGeometry.BivariantClass.Composition
public import ReasLib.AlgebraicGeometry.BivariantClass.ProperPushforward
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.VectorBundle

@[expose] public section

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe u

namespace AlgebraicGeometry.LocalizedChern

/-- A bivariant class on `Z ⟶ X` is obtained by localization on the closed cover of the
infinity fibre by `T` and the inverse image of `Z`, composition with Gysin at infinity,
and proper pushforward from that inverse image to `Z`. -/
def IsCompactificationLocalization
    {S : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    {X : Over S} [LocallyOfFiniteType X.hom] {Z W T : Scheme.{u}}
    (i : Z ⟶ X.left) [IsClosedImmersion i]
    (b : W ⟶ ProjectiveLineFamily.space X) [IsProper b]
    [IsIso (b ∣_ BivariantClass.GysinAtInfinity.affinePart X)]
    (t : T ⟶ (BivariantClass.GysinAtInfinity.infinityFiber X b).left)
    [IsClosedImmersion t] (p : ℤ)
    (ambient : BivariantClass δ
      (𝟙 (BivariantClass.GysinAtInfinity.compactification X b)) p)
    (output : BivariantClass δ
      (Over.homMk i : Over.mk (i ≫ X.hom) ⟶ X) p) : Prop :=
  let infinity := BivariantClass.GysinAtInfinity.infinityToX X b
  let toZ : Over.mk (i ≫ X.hom) ⟶ X := Over.homMk i
  -- Local instance justification (defeq pin): expose the closed immersion underlying `toZ`.
  letI : IsClosedImmersion toZ.left := inferInstanceAs (IsClosedImmersion i)
  let centerToInfinity := pullback.fst infinity toZ
  let centerToZ := pullback.snd infinity toZ
  let baseChangeSquare : IsPullback centerToInfinity centerToZ infinity toZ :=
    IsPullback.of_hasPullback infinity toZ
  let schemeBaseChangeSquare := baseChangeSquare.map (Over.forget S)
  have toZClosed : IsClosedImmersion ((Over.forget S).map toZ) := by
    change IsClosedImmersion i
    infer_instance
  -- Local instance justification (proof-local temporary data): closed immersions are stable under base change.
  letI : IsClosedImmersion centerToInfinity.left :=
    MorphismProperty.of_isPullback schemeBaseChangeSquare.flip toZClosed
  -- Local instance justification (proof-local temporary data): the infinity map is a composite of proper maps.
  letI : IsProper infinity.left := by
    dsimp [infinity, BivariantClass.GysinAtInfinity.infinityToX]
    infer_instance
  have infinityProper : IsProper ((Over.forget S).map infinity) := by
    change IsProper infinity.left
    infer_instance
  -- Local instance justification (proof-local temporary data): proper morphisms are stable under base change.
  letI : IsProper centerToZ.left :=
    MorphismProperty.of_isPullback schemeBaseChangeSquare infinityProper
  let displayedCenter := Over.mk
    (centerToInfinity.left ≫
      (BivariantClass.GysinAtInfinity.infinityFiber X b).hom)
  let displayedToInfinity : displayedCenter ⟶
      BivariantClass.GysinAtInfinity.infinityFiber X b :=
    Over.homMk centerToInfinity.left
  let displayedToZ : displayedCenter ⟶ Over.mk (i ≫ X.hom) :=
    Over.homMk centerToZ.left
      ((Over.w centerToZ).trans (Over.w centerToInfinity).symm)
  -- Local instance justification (defeq pin): expose properness of the pullback projection.
  letI : IsProper displayedToZ.left := inferInstanceAs (IsProper centerToZ.left)
  let displayedToW := displayedToInfinity ≫
    BivariantClass.GysinAtInfinity.infinityInclusion X b
  let ambientOnCenter := BivariantClass.restrict δ displayedToW (𝟙 displayedCenter)
    displayedToW IsPullback.of_id_snd p ambient
  Set.range t.base ∪ Set.range centerToInfinity.left.base = Set.univ ∧
    ∃ localized : BivariantClass δ displayedToInfinity p,
      BivariantClass.IsLocalizedExtension δ
          (BivariantClass.GysinAtInfinity.infinityFiber X b) t
          centerToInfinity.left p ambientOnCenter localized ∧
        output =
          BivariantClass.properPushforward δ displayedToZ toZ p
            (by
              have hcomp : displayedToInfinity ≫ infinity = displayedToZ ≫ toZ := by
                ext
                change centerToInfinity.left ≫ infinity.left = centerToZ.left ≫ toZ.left
                exact congrArg (fun h => h.left) baseChangeSquare.w
              exact hcomp ▸ (Int.add_zero p ▸
                BivariantClass.comp δ displayedToInfinity infinity localized
                  (BivariantClass.gysinAtInfinity δ X b)))

/-- The compactification-localization construction is independent of the eligible closed
part chosen in the infinity fibre. -/
theorem isCompactificationLocalization_unique
    {S : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    {X : Over S} [LocallyOfFiniteType X.hom] {Z W T T' : Scheme.{u}}
    (i : Z ⟶ X.left) [IsClosedImmersion i]
    (b : W ⟶ ProjectiveLineFamily.space X) [IsProper b]
    [IsIso (b ∣_ BivariantClass.GysinAtInfinity.affinePart X)]
    (t : T ⟶ (BivariantClass.GysinAtInfinity.infinityFiber X b).left)
    [IsClosedImmersion t]
    (t' : T' ⟶ (BivariantClass.GysinAtInfinity.infinityFiber X b).left)
    [IsClosedImmersion t'] (p : ℤ)
    (ambient : BivariantClass δ
      (𝟙 (BivariantClass.GysinAtInfinity.compactification X b)) p)
    {output output' : BivariantClass δ
      (Over.homMk i : Over.mk (i ≫ X.hom) ⟶ X) p}
    (houtput : IsCompactificationLocalization δ i b t p ambient output)
    (houtput' : IsCompactificationLocalization δ i b t' p ambient output') :
    output = output' := by
  sorry

/-- A perfect derived module with envelope-defined Chern operations that vanishes on the
specified part of infinity has a canonical localized Newton class on `Z ⟶ X`; its proper
pushforward is the Newton class restricted to the zero fibre. -/
theorem existsNewtonClassAtZero
    {S : Scheme.{u}} [UniversallyCatenary S] {δ : S → ℤ} [IsDimensionFunction δ]
    {X : Over S} [LocallyOfFiniteType X.hom] {Z W T : Scheme.{u}}
    (i : Z ⟶ X.left) [IsClosedImmersion i]
    (b : W ⟶ ProjectiveLineFamily.space X) [IsProper b]
    [IsIso (b ∣_ BivariantClass.GysinAtInfinity.affinePart X)]
    (Q : RingedSpace.ModuleDerived W.toRingedSpace)
    (perfect : RingedSpace.ModuleDerived.IsPerfect Q)
    (defined : ∃ (Y : Scheme.{u}) (f : Y ⟶ W), IsEnvelope f ∧
      RingedSpace.ModuleDerived.HasLocallyBoundedFiniteLocallyFreeRepresentative
        ((RingedSpace.modulePullbackDerived f.toShHom).obj Q))
    (classes : ChernClass.Theory δ
      (BivariantClass.GysinAtInfinity.compactification X b).hom)
    (t : T ⟶ (BivariantClass.GysinAtInfinity.infinityFiber X b).left)
    [IsClosedImmersion t]
    (containsComplement :
      (BivariantClass.GysinAtInfinity.infinityToX X b).left.base ⁻¹'
          (Set.range i.base)ᶜ ⊆ Set.range t.base)
    (p : ℕ)
    (restrictionZero : IsZero
      ((RingedSpace.modulePullbackDerived
        (t ≫ (BivariantClass.GysinAtInfinity.infinityInclusion X b).left).toShHom).obj Q)) :
    ∃ P' : BivariantClass δ
        (Over.homMk i : Over.mk (i ≫ X.hom) ⟶ X) (p : ℤ),
      IsCompactificationLocalization δ i b t (p : ℤ)
          (EnvelopeCaps.derivedClass δ classes Q perfect defined false p) P' ∧
        BivariantClass.properPushforwardToTarget δ
            (Over.homMk i : Over.mk (i ≫ X.hom) ⟶ Over.mk X.hom) (p : ℤ) P' =
          BivariantClass.restrict δ
            (BivariantClass.GysinAtInfinity.zeroSectionLift X b) (𝟙 X)
            (BivariantClass.GysinAtInfinity.zeroSectionLift X b)
            IsPullback.of_id_snd (p : ℤ)
            (EnvelopeCaps.derivedClass δ classes Q perfect defined false p) := by
  sorry

/-- A perfect derived module with envelope-defined Chern operations whose restriction to
the specified part of infinity is a degree-zero vector bundle of rank below `p` has a
canonical localized Chern class on `Z ⟶ X`; its proper pushforward is the Chern class
restricted to the zero fibre. -/
theorem existsChernClassAtZero
    {S : Scheme.{u}} [UniversallyCatenary S] {δ : S → ℤ} [IsDimensionFunction δ]
    {X : Over S} [LocallyOfFiniteType X.hom] {Z W T : Scheme.{u}}
    (i : Z ⟶ X.left) [IsClosedImmersion i]
    (b : W ⟶ ProjectiveLineFamily.space X) [IsProper b]
    [IsIso (b ∣_ BivariantClass.GysinAtInfinity.affinePart X)]
    (Q : RingedSpace.ModuleDerived W.toRingedSpace)
    (perfect : RingedSpace.ModuleDerived.IsPerfect Q)
    (defined : ∃ (Y : Scheme.{u}) (f : Y ⟶ W), IsEnvelope f ∧
      RingedSpace.ModuleDerived.HasLocallyBoundedFiniteLocallyFreeRepresentative
        ((RingedSpace.modulePullbackDerived f.toShHom).obj Q))
    (classes : ChernClass.Theory δ
      (BivariantClass.GysinAtInfinity.compactification X b).hom)
    (t : T ⟶ (BivariantClass.GysinAtInfinity.infinityFiber X b).left)
    [IsClosedImmersion t]
    (containsComplement :
      (BivariantClass.GysinAtInfinity.infinityToX X b).left.base ⁻¹'
          (Set.range i.base)ᶜ ⊆ Set.range t.base)
    (p : ℕ)
    (restrictionRank : Scheme.ModuleDerived.IsVectorBundleOfRankLTInDegree
      ((RingedSpace.modulePullbackDerived
        (t ≫ (BivariantClass.GysinAtInfinity.infinityInclusion X b).left).toShHom).obj Q) 0 p) :
    ∃ c' : BivariantClass δ
        (Over.homMk i : Over.mk (i ≫ X.hom) ⟶ X) (p : ℤ),
      IsCompactificationLocalization δ i b t (p : ℤ)
          (EnvelopeCaps.derivedClass δ classes Q perfect defined true p) c' ∧
        BivariantClass.properPushforwardToTarget δ
            (Over.homMk i : Over.mk (i ≫ X.hom) ⟶ Over.mk X.hom) (p : ℤ) c' =
          BivariantClass.restrict δ
            (BivariantClass.GysinAtInfinity.zeroSectionLift X b) (𝟙 X)
            (BivariantClass.GysinAtInfinity.zeroSectionLift X b)
            IsPullback.of_id_snd (p : ℤ)
            (EnvelopeCaps.derivedClass δ classes Q perfect defined true p) := by
  sorry

end AlgebraicGeometry.LocalizedChern
