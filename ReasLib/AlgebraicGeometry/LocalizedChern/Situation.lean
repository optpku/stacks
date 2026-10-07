module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Perfect
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Pullback
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Representative.LocallyFree
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.VectorBundle
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.ClosedImmersion.Complement
public import ReasLib.AlgebraicGeometry.Scheme.UniversallyCatenary
public import ReasLib.Topology.Specialization.Dimension

@[expose] public section

/-!
# Setups for localized Chern classes

This file records the perfect derived-module setup used to define localized Chern classes.
-/

open CategoryTheory CategoryTheory.Limits TopologicalSpace

noncomputable section

universe u

namespace AlgebraicGeometry.LocalizedChern

/-- The two alternatives for the restriction of a localized-Chern input away from its center. -/
structure RestrictionBehavior where
  /-- Whether the restriction satisfies the pointwise rank bound rather than vanishing. -/
  isRankBound : Bool

namespace RestrictionBehavior

/-- The behavior in which the restriction vanishes. -/
def vanishing : RestrictionBehavior := ⟨false⟩

/-- The behavior in which the restriction has pointwise rank less than the given bound. -/
def rankBound : RestrictionBehavior := ⟨true⟩

end RestrictionBehavior

/-- Derived restriction to the open complement of a closed immersion. -/
def restrictAway {X Z : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]
    (E : RingedSpace.ModuleDerived X.toRingedSpace) :
    RingedSpace.ModuleDerived (closedImmersionComplement i).toScheme.toRingedSpace :=
  (RingedSpace.modulePullbackDerived (closedImmersionComplement i).ι.toShHom).obj E

/-- `restrictAway` is the canonical derived pullback to the open complement. -/
theorem restrictAway_def {X Z : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]
    (E : RingedSpace.ModuleDerived X.toRingedSpace) :
    restrictAway i E =
      (RingedSpace.modulePullbackDerived (closedImmersionComplement i).ι.toShHom).obj E := sorry

/-- The condition imposed on a derived module away from the closed center. -/
def OffCenterCondition {X Z : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]
    (E : RingedSpace.ModuleDerived X.toRingedSpace) (p : ℕ)
    (mode : RestrictionBehavior) : Prop :=
  match mode.isRankBound with
  | false => IsZero (restrictAway i E)
  | true =>
      Scheme.ModuleDerived.IsVectorBundleOfRankLTInDegree (restrictAway i E) 0 p

/-- In the vanishing mode, the off-center condition says that the restriction is zero. -/
theorem offCenterCondition_vanishing_iff {X Z : Scheme.{u}}
    (i : Z ⟶ X) [IsClosedImmersion i]
    (E : RingedSpace.ModuleDerived X.toRingedSpace) (p : ℕ) :
    OffCenterCondition i E p .vanishing ↔ IsZero (restrictAway i E) := sorry

/-- In the rank-bounded mode, the restriction is a finite locally free module of pointwise
rank less than `p`, sitting in cohomological degree zero. -/
theorem offCenterCondition_rankBound_iff {X Z : Scheme.{u}}
    (i : Z ⟶ X) [IsClosedImmersion i]
    (E : RingedSpace.ModuleDerived X.toRingedSpace) (p : ℕ) :
    OffCenterCondition i E p .rankBound ↔
      Scheme.ModuleDerived.IsVectorBundleOfRankLTInDegree (restrictAway i E) 0 p := sorry

/-- The four alternative finiteness hypotheses used in the localized-Chern setup. -/
inductive TechnicalCondition {S : Scheme.{u}} (X : Over S)
    (E : RingedSpace.ModuleDerived X.left.toRingedSpace) : Prop
  /-- The scheme `X` is quasi-compact. -/
  | quasiCompact (compact : CompactSpace X.left)
  /-- Every irreducible component of `X` is quasi-compact. -/
  | quasiCompactComponents
      (compact : ∀ C : irreducibleComponents X.left, IsCompact (C : Set X.left))
  /-- The derived module has a locally bounded finite locally free representative. -/
  | hasRepresentative
      (representative :
        RingedSpace.ModuleDerived.HasLocallyBoundedFiniteLocallyFreeRepresentative E)
  /-- The derived module is pulled back from a perfect object on a scheme locally of finite
  type over `S` whose irreducible components are quasi-compact. -/
  | pullback (X' : Over S) (finiteType : LocallyOfFiniteType X'.hom)
      (g : X ⟶ X') (E' : RingedSpace.ModuleDerived X'.left.toRingedSpace)
      (perfect : RingedSpace.ModuleDerived.IsPerfect E')
      (pullbackIso : IsIsomorphic E ((RingedSpace.modulePullbackDerived g.left.toShHom).obj E'))
      (compactComponents :
        ∀ C : irreducibleComponents X'.left, IsCompact (C : Set X'.left))

/-- `TechnicalCondition X E` is equivalent to the disjunction of its four defining
alternatives. -/
theorem technicalCondition_iff {S : Scheme.{u}} (X : Over S)
    (E : RingedSpace.ModuleDerived X.left.toRingedSpace) :
    TechnicalCondition X E ↔
      CompactSpace X.left ∨
        (∀ C : irreducibleComponents X.left, IsCompact (C : Set X.left)) ∨
        RingedSpace.ModuleDerived.HasLocallyBoundedFiniteLocallyFreeRepresentative E ∨
        ∃ (X' : Over S), LocallyOfFiniteType X'.hom ∧
          ∃ (g : X ⟶ X') (E' : RingedSpace.ModuleDerived X'.left.toRingedSpace),
            RingedSpace.ModuleDerived.IsPerfect E' ∧
              IsIsomorphic E ((RingedSpace.modulePullbackDerived g.left.toShHom).obj E') ∧
              ∀ C : irreducibleComponents X'.left, IsCompact (C : Set X'.left) := sorry

/-- A perfect derived module with one specified behavior off a closed center and one of the
four finiteness hypotheses used for localized Chern classes. -/
structure Situation (S : Scheme.{u}) [UniversallyCatenary S]
    (δ : S → ℤ) [IsDimensionFunction δ]
    (X : Over S) [LocallyOfFiniteType X.hom]
    {Z : Scheme.{u}} (i : Z ⟶ X.left) [IsClosedImmersion i]
    (E : RingedSpace.ModuleDerived X.left.toRingedSpace) (p : ℕ)
    (mode : RestrictionBehavior) : Prop where
  /-- The derived module is perfect. -/
  perfect : RingedSpace.ModuleDerived.IsPerfect E
  /-- The restriction away from the center has the selected behavior. -/
  offCenter : OffCenterCondition i E p mode
  /-- One of the four technical finiteness hypotheses holds. -/
  finiteness : TechnicalCondition X E

namespace Situation

/-- The restriction behavior indexed by a localized-Chern situation. -/
def restrictionBehavior {S : Scheme.{u}} [UniversallyCatenary S]
    {δ : S → ℤ} [IsDimensionFunction δ]
    {X : Over S} [LocallyOfFiniteType X.hom]
    {Z : Scheme.{u}} {i : Z ⟶ X.left} [IsClosedImmersion i]
    {E : RingedSpace.ModuleDerived X.left.toRingedSpace} {p : ℕ}
    {mode : RestrictionBehavior}
    (_ : Situation S δ X i E p mode) : RestrictionBehavior :=
  mode

/-- Construct a localized-Chern situation whose restriction away from the center vanishes. -/
theorem vanishing {S : Scheme.{u}} [UniversallyCatenary S]
    {δ : S → ℤ} [IsDimensionFunction δ]
    {X : Over S} [LocallyOfFiniteType X.hom]
    {Z : Scheme.{u}} {i : Z ⟶ X.left} [IsClosedImmersion i]
    {E : RingedSpace.ModuleDerived X.left.toRingedSpace} {p : ℕ}
    (perfect : RingedSpace.ModuleDerived.IsPerfect E)
    (offCenter : IsZero (restrictAway i E)) (finiteness : TechnicalCondition X E) :
    Situation S δ X i E p .vanishing :=
  { perfect := perfect, offCenter := offCenter, finiteness := finiteness }

/-- Construct a localized-Chern situation whose restriction away from the center is a
pointwise rank-bounded vector bundle in degree zero. -/
theorem rankBound {S : Scheme.{u}} [UniversallyCatenary S]
    {δ : S → ℤ} [IsDimensionFunction δ]
    {X : Over S} [LocallyOfFiniteType X.hom]
    {Z : Scheme.{u}} {i : Z ⟶ X.left} [IsClosedImmersion i]
    {E : RingedSpace.ModuleDerived X.left.toRingedSpace} {p : ℕ}
    (perfect : RingedSpace.ModuleDerived.IsPerfect E)
    (offCenter : Scheme.ModuleDerived.IsVectorBundleOfRankLTInDegree (restrictAway i E) 0 p)
    (finiteness : TechnicalCondition X E) :
    Situation S δ X i E p .rankBound :=
  { perfect := perfect, offCenter := offCenter, finiteness := finiteness }

end Situation

/-- A localized-Chern situation is characterized by perfectness, its selected off-center
condition, and one of the four technical finiteness hypotheses. -/
theorem situation_iff {S : Scheme.{u}} [UniversallyCatenary S]
    {δ : S → ℤ} [IsDimensionFunction δ]
    {X : Over S} [LocallyOfFiniteType X.hom]
    {Z : Scheme.{u}} {i : Z ⟶ X.left} [IsClosedImmersion i]
    {E : RingedSpace.ModuleDerived X.left.toRingedSpace} {p : ℕ}
    {mode : RestrictionBehavior} :
    Situation S δ X i E p mode ↔
      RingedSpace.ModuleDerived.IsPerfect E ∧
        OffCenterCondition i E p mode ∧ TechnicalCondition X E := sorry

end AlgebraicGeometry.LocalizedChern
