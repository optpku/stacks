/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.IntersectionTheory.ZeroSchemeFactor
public import stacks_project.Chap82.Definition_82_18_1_ChernCap
public import Mathlib.Algebra.DirectSum.Ring
public import Mathlib.Topology.LocallyFinsupp
public import ReasLib.AlgebraicGeometry.AlgebraicCycle.LocallyFiniteSum
public import ReasLib.CategoryTheory.Monoidal.Invertible
public import stacks_project.Chap65.Definition_65_13_2_Separation
public import stacks_project.Chap66.Definition_66_29_1_RingedSite
public import stacks_project.Chap67.Definition_67_4_2_Separation
public import stacks_project.Chap67.Definition_67_33_2_RelativeDimension
public import stacks_project.Chap67.Definition_67_40_1_Proper
public import stacks_project.Chap67.Lemma_67_4_9
public import stacks_project.Chap67.Lemma_67_30_5_Flat
public import stacks_project.Chap68.Lemma_68_12_8_Decent
public import stacks_project.Chap70.Lemma_70_5_4_PointClosure
public import stacks_project.Chap71.Definition_71_7_6_ZeroScheme
public import stacks_project.Chap71.Lemma_71_6_12_Pullback
public import stacks_project.Chap72.Definition_72_5_2_ResidueField
public import stacks_project.Chap76.Lemma_76_32_2
public import stacks_project.Chap82.Definition_82_15_1_Chow
public import stacks_project.Chap82.Lemma_82_4_3_Length

/-!
# Chow cohomology of good algebraic spaces

In Situation 82.2.1, the Chow cohomology of a good algebraic space `X / B` is
the graded `ℤ`-algebra `A^*(X)` whose degree-`p` component is the group
`A^p(X ⟶ X)` of bivariant classes of `𝟙 X` acting on Chow groups.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open CategoryTheory.MonoidalCategory
open Function Set Topology
open scoped DirectSum

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

namespace ClosedSubspace

/-- The reduced closure of a point, as a closed subspace. -/
def pointClosure {S : Scheme.{u}} {Y : AlgebraicSpace S} (y : Points Y) :
    ClosedSubspace Y :=
  ofι (PointClosure.ι y)

/-- `pointClosure y` is the closed subspace cut out by `PointClosure.ι y`. -/
theorem pointClosure_eq {S : Scheme.{u}} {Y : AlgebraicSpace S}
    (y : Points Y) :
    pointClosure y = ofι (PointClosure.ι y) :=
  sorry

/-- Multiplicity of an irreducible component of a closed subspace, as the
supremum of étale-chart lengths of `𝒪_Y` at the generic point. -/
noncomputable def componentMultiplicity {S : Scheme.{u}} {X : AlgebraicSpace S}
    [IsLocallyNoetherian X] (Y : ClosedSubspace X) (η : genericPoints Y.X) : ℕ :=
  (sSup (setOf fun d : ENat ↦
      Modules.hasLengthAt
        (SheafOfModules.unit (structureSheaf Y.X) : Y.X.Modules) η.1 d)).toNat

/-- The multiplicity is the supremum of `hasLengthAt` values at the generic
point. -/
theorem componentMultiplicity_eq {S : Scheme.{u}} {X : AlgebraicSpace S}
    [IsLocallyNoetherian X] (Y : ClosedSubspace X) (η : genericPoints Y.X) :
    componentMultiplicity Y η =
      (sSup (setOf fun d : ENat ↦
          Modules.hasLengthAt
            (SheafOfModules.unit (structureSheaf Y.X) : Y.X.Modules)
              η.1 d)).toNat :=
  sorry

/-- The multiplicity-weighted generator of an irreducible component. -/
noncomputable def componentCycle {S : Scheme.{u}} {X : AlgebraicSpace S}
    [IsLocallyNoetherian X] (Y : ClosedSubspace X) (η : genericPoints Y.X) :
    Function.locallyFinsupp (Points X) ℤ :=
  @Function.locallyFinsuppWithin.single (Points X) _ ℤ (Classical.decEq _) _
    (Points.map Y.ι η.1) (componentMultiplicity Y η : ℤ)

/-- Coefficients of the associated cycle of a closed subspace are locally
finite. -/
theorem associatedCycle_locallyFiniteSupport {S : Scheme.{u}}
    {X : AlgebraicSpace S} [IsLocallyNoetherian X] (Y : ClosedSubspace X)
    (d : Points X → ℤ) (k : ℤ) :
    LocallyFiniteSupport fun x : Points X ↦
      ∑ᶠ η : genericPoints Y.X,
        @ite ℤ (d (Points.map Y.ι η.1) = k) (Classical.propDecidable _)
          (componentCycle Y η x) 0 :=
  sorry

/-- Multiplicity-weighted degree-`k` cycle associated to a closed subspace. -/
noncomputable def associatedCycle {S : Scheme.{u}} {X : AlgebraicSpace S}
    [IsLocallyNoetherian X] (Y : ClosedSubspace X) (d : Points X → ℤ) (k : ℤ) :
    Function.locallyFinsupp (Points X) ℤ where
  toFun := fun x ↦
    ∑ᶠ η : genericPoints Y.X,
      @ite ℤ (d (Points.map Y.ι η.1) = k) (Classical.propDecidable _)
        (componentCycle Y η x) 0
  supportWithinDomain' := Set.subset_univ _
  supportLocallyFiniteWithinDomain' := fun x _ ↦
    associatedCycle_locallyFiniteSupport Y d k x

/-- Coefficients of `associatedCycle` are the finite sum of component cycles
in degree `k`. -/
theorem associatedCycle_apply {S : Scheme.{u}} {X : AlgebraicSpace S}
    [IsLocallyNoetherian X] (Y : ClosedSubspace X) (d : Points X → ℤ) (k : ℤ)
    (x : Points X) :
    associatedCycle Y d k x =
      ∑ᶠ η : genericPoints Y.X,
        @ite ℤ (d (Points.map Y.ι η.1) = k) (Classical.propDecidable _)
          (componentCycle Y η x) 0 :=
  sorry

end ClosedSubspace

namespace Hom

variable {S : Scheme.{u}} {B : AlgebraicSpace S}
  [UniversallyCatenary B] [IsQuasiSeparated B]
variable (δ : Points B → ℤ) [IsDimensionFunction δ]

/-- Residue degree of a morphism of good algebraic spaces, using decency of
the source and target induced by the good structure morphisms. -/
noncomputable def residueDegreeAlong {X Y : AlgebraicSpace S}
    (pX : X ⟶ B) [QuasiSeparated pX] (pY : Y ⟶ B) [QuasiSeparated pY]
    (h : X ⟶ Y) (x : Points X) : ℕ :=
  @residueDegree S X Y
    (@instIsDecent_of_isQuasiSeparated S X
      (IsQuasiSeparated.of_quasiSeparated pX))
    (@instIsDecent_of_isQuasiSeparated S Y
      (IsQuasiSeparated.of_quasiSeparated pY))
    h x

/-- Residue degree along a good morphism is the ordinary residue degree. -/
theorem residueDegreeAlong_eq {X Y : AlgebraicSpace S}
    (pX : X ⟶ B) [QuasiSeparated pX] (pY : Y ⟶ B) [QuasiSeparated pY]
    (h : X ⟶ Y) (x : Points X) :
    residueDegreeAlong pX pY h x =
      @residueDegree S X Y
        (@instIsDecent_of_isQuasiSeparated S X
          (IsQuasiSeparated.of_quasiSeparated pX))
        (@instIsDecent_of_isQuasiSeparated S Y
          (IsQuasiSeparated.of_quasiSeparated pY))
        h x :=
  sorry

/-- Fibrewise residue-weighted sums along a proper morphism have locally finite
support. -/
theorem properPushforward_locallyFiniteSupport {X Y : AlgebraicSpace S}
    (pX : X ⟶ B) [QuasiSeparated pX] [LocallyOfFiniteType pX]
    (pY : Y ⟶ B) [QuasiSeparated pY] [LocallyOfFiniteType pY]
    (h : X ⟶ Y) [Proper h] (α : Function.locallyFinsupp (Points X) ℤ) :
    LocallyFiniteSupport fun y : Points Y ↦
      ∑ᶠ x ∈ Points.map h ⁻¹' {y}, (residueDegreeAlong pX pY h x : ℤ) * α x :=
  sorry

/-- Proper pushforward of a cycle, summing residue-weighted fibres of
`Points.map h`. -/
def properPushforwardCycle {X Y : AlgebraicSpace S}
    (pX : X ⟶ B) [QuasiSeparated pX] [LocallyOfFiniteType pX]
    (pY : Y ⟶ B) [QuasiSeparated pY] [LocallyOfFiniteType pY]
    (h : X ⟶ Y) [Proper h] (α : Function.locallyFinsupp (Points X) ℤ) :
    Function.locallyFinsupp (Points Y) ℤ where
  toFun := fun y ↦
    ∑ᶠ x ∈ Points.map h ⁻¹' {y}, (residueDegreeAlong pX pY h x : ℤ) * α x
  supportWithinDomain' := Set.subset_univ _
  supportLocallyFiniteWithinDomain' := fun y _ ↦
    properPushforward_locallyFiniteSupport pX pY h α y

/-- Proper pushforward of cycles evaluates as the residue-weighted fibre sum. -/
theorem properPushforwardCycle_apply {X Y : AlgebraicSpace S}
    (pX : X ⟶ B) [QuasiSeparated pX] [LocallyOfFiniteType pX]
    (pY : Y ⟶ B) [QuasiSeparated pY] [LocallyOfFiniteType pY]
    (h : X ⟶ Y) [Proper h] (α : Function.locallyFinsupp (Points X) ℤ)
    (y : Points Y) :
    properPushforwardCycle pX pY h α y =
      ∑ᶠ x ∈ Points.map h ⁻¹' {y}, (residueDegreeAlong pX pY h x : ℤ) * α x :=
  sorry

/-- Proper pushforward preserves relative degree `k`. -/
theorem properPushforward_mem_cycleGroup {X Y : AlgebraicSpace S}
    (pX : X ⟶ B) [QuasiSeparated pX] [LocallyOfFiniteType pX]
    (pY : Y ⟶ B) [QuasiSeparated pY] [LocallyOfFiniteType pY]
    (h : X ⟶ Y) [Proper h] (hf : h ≫ pY = pX) (k : ℤ)
    (α : Hom.cycleGroup pX δ k) :
    properPushforwardCycle pX pY h (α : Function.locallyFinsupp (Points X) ℤ) ∈
      Hom.cycleGroup pY δ k :=
  sorry

/-- Proper pushforward as an additive map on cycle groups of a fixed relative
degree. -/
def properPushforwardHom {X Y : AlgebraicSpace S}
    (pX : X ⟶ B) [QuasiSeparated pX] [LocallyOfFiniteType pX]
    (pY : Y ⟶ B) [QuasiSeparated pY] [LocallyOfFiniteType pY]
    (h : X ⟶ Y) [Proper h] (hf : h ≫ pY = pX) (k : ℤ) :
    Hom.cycleGroup pX δ k →+ Hom.cycleGroup pY δ k where
  toFun α :=
    ⟨properPushforwardCycle pX pY h (α : Function.locallyFinsupp (Points X) ℤ),
      properPushforward_mem_cycleGroup δ pX pY h hf k α⟩
  map_zero' := sorry
  map_add' := sorry

/-- Proper pushforward of cycles sends rational boundaries to rational
boundaries. -/
theorem properPushforwardHom_mem_boundaries {X Y : AlgebraicSpace S}
    (pX : X ⟶ B) [QuasiSeparated pX] [LocallyOfFiniteType pX]
    (pY : Y ⟶ B) [QuasiSeparated pY] [LocallyOfFiniteType pY]
    (h : X ⟶ Y) [Proper h] (hf : h ≫ pY = pX) (k : ℤ) :
    RationalEquivalence.boundaries pX δ k ≤
      (RationalEquivalence.boundaries pY δ k).comap
        (properPushforwardHom δ pX pY h hf k) :=
  sorry

/-- Proper pushforward of degree-`k` Chow classes. -/
noncomputable def properPushforward {X Y : AlgebraicSpace S}
    (pX : X ⟶ B) [QuasiSeparated pX] [LocallyOfFiniteType pX]
    (pY : Y ⟶ B) [QuasiSeparated pY] [LocallyOfFiniteType pY]
    (h : X ⟶ Y) [Proper h] (hf : h ≫ pY = pX) (k : ℤ) :
    Hom.chowGroup pX δ k →+ Hom.chowGroup pY δ k :=
  QuotientAddGroup.map
    (RationalEquivalence.boundaries pX δ k)
    (RationalEquivalence.boundaries pY δ k)
    (properPushforwardHom δ pX pY h hf k)
    (properPushforwardHom_mem_boundaries δ pX pY h hf k)

/-- Proper pushforward on Chow classes is induced by cycle pushforward. -/
theorem properPushforward_chowMk {X Y : AlgebraicSpace S}
    (pX : X ⟶ B) [QuasiSeparated pX] [LocallyOfFiniteType pX]
    (pY : Y ⟶ B) [QuasiSeparated pY] [LocallyOfFiniteType pY]
    (h : X ⟶ Y) [Proper h] (hf : h ≫ pY = pX) (k : ℤ)
    (α : Hom.cycleGroup pX δ k) :
    properPushforward δ pX pY h hf k (Hom.chowMk pX δ k α) =
      Hom.chowMk pY δ k (properPushforwardHom δ pX pY h hf k α) :=
  sorry

/-- Coefficients of a flat pullback are locally finite on `|X|`. -/
theorem flatPullback_locallyFiniteSupport {X Y : AlgebraicSpace S}
    (pY : Y ⟶ B) [QuasiSeparated pY] [LocallyOfFiniteType pY]
    (pX : X ⟶ B) [QuasiSeparated pX] [LocallyOfFiniteType pX]
    (h : X ⟶ Y) (r : ℕ) [Flat h] [RelativeDimension h r]
    (hf : h ≫ pY = pX) (k : ℤ) (α : Function.locallyFinsupp (Points Y) ℤ) :
    LocallyFiniteSupport fun x : Points X ↦
      ∑ᶠ y : Points Y,
        α y *
          (@ClosedSubspace.associatedCycle S X
            (LocallyOfFiniteType.isLocallyNoetherian pX)
            ((ClosedSubspace.pointClosure y).inverseImage h)
            (Hom.relativeDimensionFunction pX δ) (k + (r : ℤ)) x) :=
  sorry

/-- Flat pullback of a cycle along a morphism of relative dimension `r`. -/
def flatPullback {X Y : AlgebraicSpace S}
    (pY : Y ⟶ B) [QuasiSeparated pY] [LocallyOfFiniteType pY]
    (pX : X ⟶ B) [QuasiSeparated pX] [LocallyOfFiniteType pX]
    (h : X ⟶ Y) (r : ℕ) [Flat h] [RelativeDimension h r]
    (hf : h ≫ pY = pX) (k : ℤ) (α : Function.locallyFinsupp (Points Y) ℤ) :
    Function.locallyFinsupp (Points X) ℤ where
  toFun x :=
    ∑ᶠ y : Points Y,
      α y *
        (@ClosedSubspace.associatedCycle S X
          (LocallyOfFiniteType.isLocallyNoetherian pX)
          ((ClosedSubspace.pointClosure y).inverseImage h)
          (Hom.relativeDimensionFunction pX δ) (k + (r : ℤ)) x)
  supportWithinDomain' := Set.subset_univ _
  supportLocallyFiniteWithinDomain' x _ :=
    flatPullback_locallyFiniteSupport δ pY pX h r hf k α x

/-- The coefficient of a flat pullback is the locally finite sum of input
coefficients times associated cycles of inverse images of point closures. -/
theorem flatPullback_apply {X Y : AlgebraicSpace S}
    (pY : Y ⟶ B) [QuasiSeparated pY] [LocallyOfFiniteType pY]
    (pX : X ⟶ B) [QuasiSeparated pX] [LocallyOfFiniteType pX]
    (h : X ⟶ Y) (r : ℕ) [Flat h] [RelativeDimension h r]
    (hf : h ≫ pY = pX) (k : ℤ) (α : Function.locallyFinsupp (Points Y) ℤ)
    (x : Points X) :
    flatPullback δ pY pX h r hf k α x =
      ∑ᶠ y : Points Y,
        α y *
          (@ClosedSubspace.associatedCycle S X
            (LocallyOfFiniteType.isLocallyNoetherian pX)
            ((ClosedSubspace.pointClosure y).inverseImage h)
            (Hom.relativeDimensionFunction pX δ) (k + (r : ℤ)) x) :=
  sorry

/-- Flat pullback sends `k`-cycles on `Y` to `(k + r)`-cycles on `X`. -/
theorem flatPullback_mem_cycleGroup {X Y : AlgebraicSpace S}
    (pY : Y ⟶ B) [QuasiSeparated pY] [LocallyOfFiniteType pY]
    (pX : X ⟶ B) [QuasiSeparated pX] [LocallyOfFiniteType pX]
    (h : X ⟶ Y) (r : ℕ) [Flat h] [RelativeDimension h r]
    (hf : h ≫ pY = pX) (k : ℤ) {α : Function.locallyFinsupp (Points Y) ℤ}
    (hα : α ∈ Hom.cycleGroup pY δ k) :
    flatPullback δ pY pX h r hf k α ∈ Hom.cycleGroup pX δ (k + (r : ℤ)) :=
  sorry

/-- Flat pullback as an additive map `Z_k(Y) → Z_{k + r}(X)`. -/
def flatPullbackHom {X Y : AlgebraicSpace S}
    (pY : Y ⟶ B) [QuasiSeparated pY] [LocallyOfFiniteType pY]
    (pX : X ⟶ B) [QuasiSeparated pX] [LocallyOfFiniteType pX]
    (h : X ⟶ Y) (r : ℕ) [Flat h] [RelativeDimension h r]
    (hf : h ≫ pY = pX) (k : ℤ) :
    Hom.cycleGroup pY δ k →+ Hom.cycleGroup pX δ (k + (r : ℤ)) where
  toFun α :=
    ⟨flatPullback δ pY pX h r hf k α,
      flatPullback_mem_cycleGroup δ pY pX h r hf k α.property⟩
  map_zero' := sorry
  map_add' := sorry

/-- Flat pullback of cycles sends rational boundaries to rational boundaries. -/
theorem flatPullbackHom_mem_boundaries {X Y : AlgebraicSpace S}
    (pY : Y ⟶ B) [QuasiSeparated pY] [LocallyOfFiniteType pY]
    (pX : X ⟶ B) [QuasiSeparated pX] [LocallyOfFiniteType pX]
    (h : X ⟶ Y) (r : ℕ) [Flat h] [RelativeDimension h r]
    (hf : h ≫ pY = pX) (k : ℤ) :
    RationalEquivalence.boundaries pY δ k ≤
      (RationalEquivalence.boundaries pX δ (k + (r : ℤ))).comap
        (flatPullbackHom δ pY pX h r hf k) :=
  sorry

/-- Flat pullback of degree-`k` Chow classes along a morphism of relative
dimension `r`. -/
noncomputable def chowFlatPullback {X Y : AlgebraicSpace S}
    (pY : Y ⟶ B) [QuasiSeparated pY] [LocallyOfFiniteType pY]
    (pX : X ⟶ B) [QuasiSeparated pX] [LocallyOfFiniteType pX]
    (h : X ⟶ Y) (r : ℕ) [Flat h] [RelativeDimension h r]
    (hf : h ≫ pY = pX) (k : ℤ) :
    Hom.chowGroup pY δ k →+ Hom.chowGroup pX δ (k + (r : ℤ)) :=
  QuotientAddGroup.map
    (RationalEquivalence.boundaries pY δ k)
    (RationalEquivalence.boundaries pX δ (k + (r : ℤ)))
    (flatPullbackHom δ pY pX h r hf k)
    (flatPullbackHom_mem_boundaries δ pY pX h r hf k)

/-- Flat pullback on Chow classes is induced by cycle flat pullback. -/
theorem chowFlatPullback_chowMk {X Y : AlgebraicSpace S}
    (pY : Y ⟶ B) [QuasiSeparated pY] [LocallyOfFiniteType pY]
    (pX : X ⟶ B) [QuasiSeparated pX] [LocallyOfFiniteType pX]
    (h : X ⟶ Y) (r : ℕ) [Flat h] [RelativeDimension h r]
    (hf : h ≫ pY = pX) (k : ℤ) (α : Hom.cycleGroup pY δ k) :
    chowFlatPullback δ pY pX h r hf k (Hom.chowMk pY δ k α) =
      Hom.chowMk pX δ (k + (r : ℤ)) (flatPullbackHom δ pY pX h r hf k α) :=
  sorry

/-- The zero scheme of a section remains quasi-separated over the fixed good
base. -/
instance instQuasiSeparated_zeroScheme_comp {X : AlgebraicSpace S}
    (pX : X ⟶ B) [QuasiSeparated pX] (L : X.Modules) [isInvertibleObject L]
    (s : L.sections) : QuasiSeparated (zeroSchemeι L s ≫ pX) :=
  sorry

/-- The zero scheme of a section remains locally of finite type over the fixed
good base. -/
instance instLocallyOfFiniteType_zeroScheme_comp {X : AlgebraicSpace S}
    (pX : X ⟶ B) [LocallyOfFiniteType pX] (L : X.Modules)
    [isInvertibleObject L] (s : L.sections) :
    LocallyOfFiniteType (zeroSchemeι L s ≫ pX) :=
  sorry

namespace GysinConstruction

variable {X : AlgebraicSpace S}
    (pX : X ⟶ B) [QuasiSeparated pX] [LocallyOfFiniteType pX]
    (L : X.Modules) [isInvertibleObject L] (s : L.sections)

-- Local instance justification (proof-local temporary data): The generator formula uses the reduced point closure over the fixed good base; install its two proved finiteness properties only in this construction.
attribute [local instance] closure_quasiSeparated closure_locallyOfFiniteType

/-- The source's contained branch uses scheme-theoretic vanishing on the
reduced integral point closure, not an assumed map into the zero scheme. -/
abbrev Contained (x : Points X) : Prop :=
  AlgebraicGeometry.AlgebraicSpace.IntersectionTheory.ZeroSchemeFactor.VanishesOn L s (PointClosure.ι x)

/-- The reduced point closure is contained in Z(s) exactly when the restricted
section vanishes. Reducedness rules out a merely nilpotent nonzero restriction. -/
theorem contained_iff_support (x : Points X) :
    Contained L s x ↔
      (ClosedSubspace.pointClosure x).pointsSet ⊆ (zeroScheme L s).pointsSet := by
  sorry

/-- The actual closed inclusion W → Z(s), defined on each test point. -/
def intoZero (x : Points X) (h : Contained L s x) :
    PointClosure.space x ⟶ (zeroScheme L s).X :=
  AlgebraicGeometry.AlgebraicSpace.IntersectionTheory.ZeroSchemeFactor.lift L s (PointClosure.ι x) h

@[simp] theorem intoZero_ι (x : Points X) (h : Contained L s x) :
    intoZero L s x h ≫ zeroSchemeι L s = PointClosure.ι x :=
  AlgebraicGeometry.AlgebraicSpace.IntersectionTheory.ZeroSchemeFactor.lift_ι L s (PointClosure.ι x) h

instance intoZero_isClosedImmersion (x : Points X) (h : Contained L s x) :
    IsClosedImmersion (intoZero L s x h) :=
  AlgebraicGeometry.AlgebraicSpace.IntersectionTheory.ZeroSchemeFactor.lift_isClosedImmersion L s (PointClosure.ι x) h

theorem intoZero_over (x : Points X) (h : Contained L s x) :
    intoZero L s x h ≫ (zeroSchemeι L s ≫ pX) = PointClosure.ι x ≫ pX := by
  rw [← Category.assoc, intoZero_ι]

/-- The relative degree of the same generic point is unchanged by the closed
inclusion. This is a law of the specified point-closure inclusion. -/
theorem generic_degree (k : ℤ) (x : Points X)
    (hx : Hom.relativeDimensionFunction pX δ x = k + 1) :
    Hom.relativeDimensionFunction (PointClosure.ι x ≫ pX) δ (PointClosure.generic x) = k + 1 := by
  sorry

/-- The genuine fundamental cycle of W: coefficient one at its generic point. -/
def fundamental (k : ℤ) (x : Points X)
    (hx : Hom.relativeDimensionFunction pX δ x = k + 1) :
    Hom.cycleGroup (PointClosure.ι x ≫ pX) δ (k + 1) := by
  classical
  exact ⟨Function.locallyFinsuppWithin.single (PointClosure.generic x) 1, by
    intro y hy
    by_cases h : y = PointClosure.generic x
    · simpa only [h] using generic_degree δ pX k x hx
    · simp [Function.locallyFinsuppWithin.single_apply, h] at hy⟩

/-- A representative for c1(L|W) cap [W], using the canonical public Chern owner.
The underlying line is the actual pullback of L; no Chern-family parameter is added. -/
def containedChernCycle (k : ℤ) (x : Points X)
    (hx : Hom.relativeDimensionFunction pX δ x = k + 1) :
    Hom.cycleGroup (PointClosure.ι x ≫ pX) δ k := by
  -- Local instance justification (proof-local temporary data): The contained branch applies c1 to the actual restriction of L to the reduced point closure, with invertibility supplied by its pullback theorem.
  letI := Modules.isInvertibleObject_pullback (PointClosure.ι x) L
  exact ⟨firstChernCycle (PointClosure.ι x ≫ pX) δ
      ((Modules.pullback (PointClosure.ι x)).obj L) k
      (fundamental δ pX k x hx : Function.locallyFinsupp (Points (PointClosure.space x)) ℤ),
    firstChernCycle_mem (PointClosure.ι x ≫ pX) δ
      ((Modules.pullback (PointClosure.ι x)).obj L) k (fundamental δ pX k x hx)⟩

/-- Actual residue-weighted pushforward along W → Z(s) of the restricted Chern cycle. -/
def containedValue (k : ℤ) (x : Points X)
    (hx : Hom.relativeDimensionFunction pX δ x = k + 1) (h : Contained L s x) :
    Hom.cycleGroup (zeroSchemeι L s ≫ pX) δ k :=
  properPushforwardHom δ (PointClosure.ι x ≫ pX) (zeroSchemeι L s ≫ pX)
    (intoZero L s x h) (intoZero_over pX L s x h) k (containedChernCycle δ pX L k x hx)

/-- Its Chow class is precisely the source's i'_* (c1(L|W) cap [W]). -/
theorem containedValue_chowMk (k : ℤ) (x : Points X)
    (hx : Hom.relativeDimensionFunction pX δ x = k + 1) (h : Contained L s x) :
    Hom.chowMk (zeroSchemeι L s ≫ pX) δ k (containedValue δ pX L s k x hx h) =
      @properPushforward S B _ _ δ _ (PointClosure.space x) (zeroScheme L s).X
        (PointClosure.ι x ≫ pX) _ _ (zeroSchemeι L s ≫ pX) _ _
        (intoZero L s x h) _ (intoZero_over pX L s x h) k
        (@firstChernClassCap S B (PointClosure.space x) _ _ (PointClosure.ι x ≫ pX) _ _
          δ _ ((Modules.pullback (PointClosure.ι x)).obj L)
          (Modules.isInvertibleObject_pullback (PointClosure.ι x) L) k (fundamental δ pX k x hx)) := by
  rfl

end GysinConstruction

/-- The two source branches of refined Gysin: restricted first Chern pushed
from W when W is contained in Z(s), and the intersection cycle otherwise. -/
noncomputable def RefinedGysin.gysinGeneratorCycle {X : AlgebraicSpace S}
    (pX : X ⟶ B) [QuasiSeparated pX] [LocallyOfFiniteType pX] (k : ℤ)
    (L : X.Modules) [isInvertibleObject L] (s : L.sections) (x : Points X)
    (hx : Hom.relativeDimensionFunction pX δ x = k + 1) :
    Function.locallyFinsupp (Points (zeroScheme L s).X) ℤ := by
  classical
  exact if h : GysinConstruction.Contained L s x then
    (GysinConstruction.containedValue δ pX L s k x hx h).val
  else
    @ClosedSubspace.associatedCycle S (zeroScheme L s).X
      (LocallyOfFiniteType.isLocallyNoetherian (zeroSchemeι L s ≫ pX))
      ((ClosedSubspace.pointClosure x).inverseImage (zeroSchemeι L s))
      (Hom.relativeDimensionFunction (zeroSchemeι L s ≫ pX) δ) k

/-- The contained branch stated with the original source condition W ⊆ Z(s).
No chosen factor map or extra trivialization is a parameter. -/
theorem gysinGeneratorCycle_of_support_subset {X : AlgebraicSpace S}
    (pX : X ⟶ B) [QuasiSeparated pX] [LocallyOfFiniteType pX] (k : ℤ)
    (L : X.Modules) [isInvertibleObject L] (s : L.sections) (x : Points X)
    (hx : Hom.relativeDimensionFunction pX δ x = k + 1)
    (hW : (ClosedSubspace.pointClosure x).pointsSet ⊆ (zeroScheme L s).pointsSet) :
    RefinedGysin.gysinGeneratorCycle δ pX k L s x hx =
      (GysinConstruction.containedValue δ pX L s k x hx
        ((GysinConstruction.contained_iff_support L s x).mpr hW)).val := by
  classical
  simp only [RefinedGysin.gysinGeneratorCycle, dif_pos ((GysinConstruction.contained_iff_support L s x).mpr hW)]

/-- The other source branch keeps the associated intersection cycle verbatim. -/
theorem gysinGeneratorCycle_of_not_support_subset {X : AlgebraicSpace S}
    (pX : X ⟶ B) [QuasiSeparated pX] [LocallyOfFiniteType pX] (k : ℤ)
    (L : X.Modules) [isInvertibleObject L] (s : L.sections) (x : Points X)
    (hx : Hom.relativeDimensionFunction pX δ x = k + 1)
    (hW : ¬(ClosedSubspace.pointClosure x).pointsSet ⊆ (zeroScheme L s).pointsSet) :
    RefinedGysin.gysinGeneratorCycle δ pX k L s x hx =
      @ClosedSubspace.associatedCycle S (zeroScheme L s).X
        (LocallyOfFiniteType.isLocallyNoetherian (zeroSchemeι L s ≫ pX))
        ((ClosedSubspace.pointClosure x).inverseImage (zeroSchemeι L s))
        (Hom.relativeDimensionFunction (zeroSchemeι L s ≫ pX) δ) k := by
  classical
  have h : ¬GysinConstruction.Contained L s x :=
    fun hc ↦ hW ((GysinConstruction.contained_iff_support L s x).mp hc)
  simp only [RefinedGysin.gysinGeneratorCycle, dif_neg h]

/-- The coefficient-weighted Gysin generator cycles of a locally finite cycle
form a locally finite family on `Z(s)`. -/
theorem RefinedGysin.gysinGeneratorTermsLocallyFinite {X : AlgebraicSpace S}
    (pX : X ⟶ B) [QuasiSeparated pX] [LocallyOfFiniteType pX] (k : ℤ)
    (L : X.Modules) [isInvertibleObject L] (s : L.sections)
    (α : Function.locallyFinsupp (Points X) ℤ) :
    LocallyFinite fun x : Points X ↦
      (if hx : Hom.relativeDimensionFunction pX δ x = k + 1 then
        α x • RefinedGysin.gysinGeneratorCycle δ pX k L s x hx
      else 0).support :=
  sorry

/-- The explicit locally finite Gysin cycle on `Z(s)`. -/
noncomputable def RefinedGysin.gysinCycle {X : AlgebraicSpace S}
    (pX : X ⟶ B) [QuasiSeparated pX] [LocallyOfFiniteType pX] (k : ℤ)
    (L : X.Modules) [isInvertibleObject L] (s : L.sections)
    (α : Function.locallyFinsupp (Points X) ℤ) :
    Function.locallyFinsupp (Points (zeroScheme L s).X) ℤ :=
  AlgebraicCycle.locallyFiniteSum
    (fun x : Points X ↦
      if hx : Hom.relativeDimensionFunction pX δ x = k + 1 then
        α x • RefinedGysin.gysinGeneratorCycle δ pX k L s x hx
      else 0)
    (RefinedGysin.gysinGeneratorTermsLocallyFinite δ pX k L s α)

/-- The Gysin cycle of a `(k + 1)`-cycle is a `k`-cycle on `Z(s)`. -/
theorem RefinedGysin.gysinCycle_mem {X : AlgebraicSpace S}
    (pX : X ⟶ B) [QuasiSeparated pX] [LocallyOfFiniteType pX] (k : ℤ)
    (L : X.Modules) [isInvertibleObject L] (s : L.sections)
    (α : Hom.cycleGroup pX δ (k + 1)) :
    RefinedGysin.gysinCycle δ pX k L s (α : Function.locallyFinsupp (Points X) ℤ) ∈
      Hom.cycleGroup (zeroSchemeι L s ≫ pX) δ k :=
  sorry

/-- Cycle-level Gysin homomorphism `Z_{k + 1}(X) →+ Z_k(Z(s))`. -/
noncomputable def gysinCycleHom {X : AlgebraicSpace S}
    (pX : X ⟶ B) [QuasiSeparated pX] [LocallyOfFiniteType pX] (k : ℤ)
    (L : X.Modules) [isInvertibleObject L] (s : L.sections) :
    Hom.cycleGroup pX δ (k + 1) →+ Hom.cycleGroup (zeroSchemeι L s ≫ pX) δ k where
  toFun α :=
    ⟨RefinedGysin.gysinCycle δ pX k L s (α : Function.locallyFinsupp (Points X) ℤ),
      RefinedGysin.gysinCycle_mem δ pX k L s α⟩
  map_zero' := sorry
  map_add' := sorry

/-- Cycle-level Gysin sends rational boundaries to rational boundaries. -/
theorem gysinCycleHom_mem_boundaries {X : AlgebraicSpace S}
    (pX : X ⟶ B) [QuasiSeparated pX] [LocallyOfFiniteType pX]
    (k : ℤ) (L : X.Modules) [isInvertibleObject L] (s : L.sections) :
    RationalEquivalence.boundaries pX δ (k + 1) ≤
      (RationalEquivalence.boundaries (zeroSchemeι L s ≫ pX) δ k).comap
        (gysinCycleHom δ pX k L s) :=
  sorry

/-- Gysin homomorphism on Chow groups associated to a global section of an
invertible module. -/
noncomputable def chowGysin {X : AlgebraicSpace S}
    (pX : X ⟶ B) [QuasiSeparated pX] [LocallyOfFiniteType pX]
    (L : X.Modules) [isInvertibleObject L] (s : L.sections) (k : ℤ) :
    Hom.chowGroup pX δ (k + 1) →+ Hom.chowGroup (zeroSchemeι L s ≫ pX) δ k :=
  QuotientAddGroup.map
    (RationalEquivalence.boundaries pX δ (k + 1))
    (RationalEquivalence.boundaries (zeroSchemeι L s ≫ pX) δ k)
    (gysinCycleHom δ pX k L s)
    (gysinCycleHom_mem_boundaries δ pX k L s)

/-- Gysin on Chow classes is induced by the cycle-level Gysin map. -/
theorem chowGysin_chowMk {X : AlgebraicSpace S}
    (pX : X ⟶ B) [QuasiSeparated pX] [LocallyOfFiniteType pX]
    (L : X.Modules) [isInvertibleObject L] (s : L.sections) (k : ℤ)
    (α : Hom.cycleGroup pX δ (k + 1)) :
    chowGysin δ pX L s k (Hom.chowMk pX δ (k + 1) α) =
      Hom.chowMk (zeroSchemeι L s ≫ pX) δ k (gysinCycleHom δ pX k L s α) :=
  sorry

end Hom

namespace ChowCohomology

variable {S : Scheme.{u}} {B X : AlgebraicSpace S}
  [UniversallyCatenary B] [IsQuasiSeparated B]
variable (δ : Points B → ℤ) [IsDimensionFunction δ]
variable (f : X ⟶ B) [QuasiSeparated f] [LocallyOfFiniteType f]

/-- Identity cap families `CH_k(Y) →+ CH_{k - p}(Y)` on good morphisms
`Y ⟶ X` over `B`. -/
abbrev CapFamily (p : ℤ) :=
  ∀ {Y : AlgebraicSpace S} (g : Y ⟶ X)
    [QuasiSeparated (g ≫ f)] [LocallyOfFiniteType (g ≫ f)] (k : ℤ),
    Hom.chowGroup (g ≫ f) δ k →+ Hom.chowGroup (g ≫ f) δ (k - p)

/-- Reindex a Chow group along an equality of degrees. -/
def castChowGroup {Y : AlgebraicSpace S} (h : Y ⟶ B)
    [QuasiSeparated h] [LocallyOfFiniteType h] {i j : ℤ} (hij : i = j) :
    Hom.chowGroup h δ i →+ Hom.chowGroup h δ j :=
  hij ▸ AddMonoidHom.id _

/-- Reindexing along a reflexive degree equality is the identity map. -/
theorem castChowGroup_rfl {Y : AlgebraicSpace S} (h : Y ⟶ B)
    [QuasiSeparated h] [LocallyOfFiniteType h] (i : ℤ) :
    castChowGroup δ h (rfl : i = i) = AddMonoidHom.id _ :=
  sorry

/-- Composition of identity caps reindexes along `(k - q) - p = k - (p + q)`. -/
theorem mulCap_degree_eq (k p q : ℤ) : (k - q) - p = k - (p + q) :=
  sorry

/-- Flat pullback reindexes along `k + r - p = k - p + r`. -/
theorem flatPullback_degree_eq (k p : ℤ) (r : ℕ) :
    k + (r : ℤ) - p = k - p + (r : ℤ) :=
  sorry

/-- Gysin reindexes along `k + 1 - p = k - p + 1`. -/
theorem gysin_degree_eq (k p : ℤ) : k + 1 - p = k - p + 1 :=
  sorry

/-- Compatibility of identity cap maps with proper pushforward. -/
def CompatibleWithProperPushforward {p : ℤ} (cap : CapFamily δ f p) : Prop :=
  ∀ {Y Y' : AlgebraicSpace S} (g : Y ⟶ X) (h : Y' ⟶ Y)
    [QuasiSeparated (g ≫ f)] [LocallyOfFiniteType (g ≫ f)]
    [QuasiSeparated (h ≫ g ≫ f)] [LocallyOfFiniteType (h ≫ g ≫ f)]
    [QuasiSeparated ((h ≫ g) ≫ f)] [LocallyOfFiniteType ((h ≫ g) ≫ f)]
    [Proper h]
    (k : ℤ) (α : Hom.chowGroup (h ≫ g ≫ f) δ k),
    cap g k (Hom.properPushforward δ (h ≫ g ≫ f) (g ≫ f) h rfl k α) =
      Hom.properPushforward δ (h ≫ g ≫ f) (g ≫ f) h rfl (k - p)
        (cap (h ≫ g) k α)

/-- Compatibility of identity cap maps with flat pullback of fixed relative
dimension. -/
def CompatibleWithFlatPullback {p : ℤ} (cap : CapFamily δ f p) : Prop :=
  ∀ {Y Y' : AlgebraicSpace S} (g : Y ⟶ X) (h : Y' ⟶ Y)
    [QuasiSeparated (g ≫ f)] [LocallyOfFiniteType (g ≫ f)]
    [QuasiSeparated (h ≫ g ≫ f)] [LocallyOfFiniteType (h ≫ g ≫ f)]
    [QuasiSeparated ((h ≫ g) ≫ f)] [LocallyOfFiniteType ((h ≫ g) ≫ f)]
    (r : ℕ) [Flat h] [RelativeDimension h r]
    (k : ℤ) (α : Hom.chowGroup (g ≫ f) δ k),
    castChowGroup δ (h ≫ g ≫ f) (flatPullback_degree_eq k p r)
        (cap (h ≫ g) (k + (r : ℤ))
          (Hom.chowFlatPullback δ (g ≫ f) (h ≫ g ≫ f) h r rfl k α)) =
      Hom.chowFlatPullback δ (g ≫ f) (h ≫ g ≫ f) h r rfl (k - p)
        (cap g k α)

/-- Compatibility of identity cap maps with Gysin pullback along a zero scheme
of a section of an invertible module. -/
def CompatibleWithCartierGysin {p : ℤ} (cap : CapFamily δ f p) : Prop :=
  ∀ {Y : AlgebraicSpace S} (g : Y ⟶ X)
    [QuasiSeparated (g ≫ f)] [LocallyOfFiniteType (g ≫ f)]
    (L : Y.Modules) [isInvertibleObject L] (s : L.sections)
    [QuasiSeparated ((zeroSchemeι L s ≫ g) ≫ f)]
    [LocallyOfFiniteType ((zeroSchemeι L s ≫ g) ≫ f)]
    (k : ℤ) (α : Hom.chowGroup (g ≫ f) δ (k + 1)),
    cap (zeroSchemeι L s ≫ g) k (Hom.chowGysin δ (g ≫ f) L s k α) =
      Hom.chowGysin δ (g ≫ f) L s (k - p)
        (castChowGroup δ (g ≫ f) (gysin_degree_eq k p) (cap g (k + 1) α))

/-- The degree-`p` group `A^p(X ⟶ X)` of bivariant classes of `𝟙 X` on
Chow groups of good algebraic spaces over `X`. -/
structure degree (p : ℤ) where
  /-- Cap action `CH_k(Y) → CH_{k - p}(Y)` on a good morphism `g : Y ⟶ X`. -/
  cap : CapFamily δ f p
  /-- Compatibility with proper pushforward. -/
  map_proper : CompatibleWithProperPushforward δ f cap
  /-- Compatibility with flat pullback of relative dimension `r`. -/
  pullback_flat : CompatibleWithFlatPullback δ f cap
  /-- Compatibility with Gysin pullback along the zero scheme of a
  section of an invertible module. -/
  gysin_cartier : CompatibleWithCartierGysin δ f cap

/-- Construct a degree-`p` identity class from a cap family and the three
bivariant laws. -/
def ofCap {p : ℤ} (cap : CapFamily δ f p)
    (map_proper : CompatibleWithProperPushforward δ f cap)
    (pullback_flat : CompatibleWithFlatPullback δ f cap)
    (gysin_cartier : CompatibleWithCartierGysin δ f cap) :
    degree δ f p where
  cap := cap
  map_proper := map_proper
  pullback_flat := pullback_flat
  gysin_cartier := gysin_cartier

/-- `ofCap` recovers the supplied cap family. -/
theorem ofCap_cap {p : ℤ} (cap : CapFamily δ f p)
    (map_proper : CompatibleWithProperPushforward δ f cap)
    (pullback_flat : CompatibleWithFlatPullback δ f cap)
    (gysin_cartier : CompatibleWithCartierGysin δ f cap)
    {Y : AlgebraicSpace S} (g : Y ⟶ X)
    [QuasiSeparated (g ≫ f)] [LocallyOfFiniteType (g ≫ f)] (k : ℤ) :
    (ofCap δ f cap map_proper pullback_flat gysin_cartier).cap g k = cap g k :=
  sorry

/-- A degree-`p` identity class is a cap family compatible with proper
pushforward, flat pullback, and Gysin pullback. -/
theorem degree_spec {p : ℤ} (c : degree δ f p) :
    CompatibleWithProperPushforward δ f c.cap ∧
      CompatibleWithFlatPullback δ f c.cap ∧
      CompatibleWithCartierGysin δ f c.cap :=
  sorry

/-- Two identity classes are equal when their cap families agree. -/
theorem cap_ext {p : ℤ} {c d : degree δ f p}
    (h : ∀ {Y : AlgebraicSpace S} (g : Y ⟶ X)
      [QuasiSeparated (g ≫ f)] [LocallyOfFiniteType (g ≫ f)] (k : ℤ),
      c.cap g k = d.cap g k) :
    c = d :=
  sorry

/-- Pointwise zero identity cap family. -/
def zeroCapFamily (p : ℤ) : CapFamily δ f p :=
  fun {Y} (g : Y ⟶ X)
      [QuasiSeparated (g ≫ f)] [LocallyOfFiniteType (g ≫ f)] (k : ℤ) ↦
    (0 : Hom.chowGroup (g ≫ f) δ k →+ Hom.chowGroup (g ≫ f) δ (k - p))

/-- The zero cap family satisfies proper-pushforward compatibility. -/
theorem zeroCapFamily_map_proper (p : ℤ) :
    CompatibleWithProperPushforward δ f (zeroCapFamily δ f p) :=
  sorry

/-- The zero cap family satisfies flat-pullback compatibility. -/
theorem zeroCapFamily_pullback_flat (p : ℤ) :
    CompatibleWithFlatPullback δ f (zeroCapFamily δ f p) :=
  sorry

/-- The zero cap family satisfies Gysin compatibility. -/
theorem zeroCapFamily_gysin_cartier (p : ℤ) :
    CompatibleWithCartierGysin δ f (zeroCapFamily δ f p) :=
  sorry

/-- The zero identity class in degree `p`. -/
def zeroCap (p : ℤ) : degree δ f p :=
  ofCap δ f (zeroCapFamily δ f p)
    (zeroCapFamily_map_proper δ f p)
    (zeroCapFamily_pullback_flat δ f p)
    (zeroCapFamily_gysin_cartier δ f p)

/-- Evaluation of the zero class is the zero additive map. -/
theorem zeroCap_apply (p : ℤ) {Y : AlgebraicSpace S} (g : Y ⟶ X)
    [QuasiSeparated (g ≫ f)] [LocallyOfFiniteType (g ≫ f)] (k : ℤ) :
    (zeroCap δ f p).cap g k = 0 :=
  sorry

/-- Pointwise addition of identity cap families. -/
def addCapFamily {p : ℤ} (c d : degree δ f p) : CapFamily δ f p :=
  fun {Y} (g : Y ⟶ X)
      [QuasiSeparated (g ≫ f)] [LocallyOfFiniteType (g ≫ f)] (k : ℤ) ↦
    c.cap g k + d.cap g k

/-- The sum of two cap families satisfies proper-pushforward compatibility. -/
theorem addCapFamily_map_proper {p : ℤ} (c d : degree δ f p) :
    CompatibleWithProperPushforward δ f (addCapFamily δ f c d) :=
  sorry

/-- The sum of two cap families satisfies flat-pullback compatibility. -/
theorem addCapFamily_pullback_flat {p : ℤ} (c d : degree δ f p) :
    CompatibleWithFlatPullback δ f (addCapFamily δ f c d) :=
  sorry

/-- The sum of two cap families satisfies Gysin compatibility. -/
theorem addCapFamily_gysin_cartier {p : ℤ} (c d : degree δ f p) :
    CompatibleWithCartierGysin δ f (addCapFamily δ f c d) :=
  sorry

/-- Pointwise addition of identity classes. -/
def addCap {p : ℤ} (c d : degree δ f p) : degree δ f p :=
  ofCap δ f (addCapFamily δ f c d)
    (addCapFamily_map_proper δ f c d)
    (addCapFamily_pullback_flat δ f c d)
    (addCapFamily_gysin_cartier δ f c d)

/-- Evaluation of pointwise addition is addition of the evaluated maps. -/
theorem addCap_apply {p : ℤ} (c d : degree δ f p) {Y : AlgebraicSpace S}
    (g : Y ⟶ X) [QuasiSeparated (g ≫ f)] [LocallyOfFiniteType (g ≫ f)]
    (k : ℤ) :
    (addCap δ f c d).cap g k = c.cap g k + d.cap g k :=
  sorry

/-- Pointwise negation of an identity cap family. -/
def negCapFamily {p : ℤ} (c : degree δ f p) : CapFamily δ f p :=
  fun {Y} (g : Y ⟶ X)
      [QuasiSeparated (g ≫ f)] [LocallyOfFiniteType (g ≫ f)] (k : ℤ) ↦
    -c.cap g k

/-- The negation of a cap family satisfies proper-pushforward compatibility. -/
theorem negCapFamily_map_proper {p : ℤ} (c : degree δ f p) :
    CompatibleWithProperPushforward δ f (negCapFamily δ f c) :=
  sorry

/-- The negation of a cap family satisfies flat-pullback compatibility. -/
theorem negCapFamily_pullback_flat {p : ℤ} (c : degree δ f p) :
    CompatibleWithFlatPullback δ f (negCapFamily δ f c) :=
  sorry

/-- The negation of a cap family satisfies Gysin compatibility. -/
theorem negCapFamily_gysin_cartier {p : ℤ} (c : degree δ f p) :
    CompatibleWithCartierGysin δ f (negCapFamily δ f c) :=
  sorry

/-- Pointwise negation of an identity class. -/
def negCap {p : ℤ} (c : degree δ f p) : degree δ f p :=
  ofCap δ f (negCapFamily δ f c)
    (negCapFamily_map_proper δ f c)
    (negCapFamily_pullback_flat δ f c)
    (negCapFamily_gysin_cartier δ f c)

/-- Evaluation of pointwise negation is negation of the evaluated map. -/
theorem negCap_apply {p : ℤ} (c : degree δ f p) {Y : AlgebraicSpace S}
    (g : Y ⟶ X) [QuasiSeparated (g ≫ f)] [LocallyOfFiniteType (g ≫ f)]
    (k : ℤ) :
    (negCap δ f c).cap g k = -c.cap g k :=
  sorry

/-- Natural scalar multiplication of an identity cap family. -/
def nsmulCapFamily {p : ℤ} (n : ℕ) (c : degree δ f p) : CapFamily δ f p :=
  fun {Y} (g : Y ⟶ X)
      [QuasiSeparated (g ≫ f)] [LocallyOfFiniteType (g ≫ f)] (k : ℤ) ↦
    n • c.cap g k

/-- Natural scalar multiplication satisfies proper-pushforward compatibility. -/
theorem nsmulCapFamily_map_proper {p : ℤ} (n : ℕ) (c : degree δ f p) :
    CompatibleWithProperPushforward δ f (nsmulCapFamily δ f n c) :=
  sorry

/-- Natural scalar multiplication satisfies flat-pullback compatibility. -/
theorem nsmulCapFamily_pullback_flat {p : ℤ} (n : ℕ) (c : degree δ f p) :
    CompatibleWithFlatPullback δ f (nsmulCapFamily δ f n c) :=
  sorry

/-- Natural scalar multiplication satisfies Gysin compatibility. -/
theorem nsmulCapFamily_gysin_cartier {p : ℤ} (n : ℕ) (c : degree δ f p) :
    CompatibleWithCartierGysin δ f (nsmulCapFamily δ f n c) :=
  sorry

/-- Natural scalar multiplication of an identity class. -/
def nsmulCap {p : ℤ} (n : ℕ) (c : degree δ f p) : degree δ f p :=
  ofCap δ f (nsmulCapFamily δ f n c)
    (nsmulCapFamily_map_proper δ f n c)
    (nsmulCapFamily_pullback_flat δ f n c)
    (nsmulCapFamily_gysin_cartier δ f n c)

/-- Natural scalar multiplication evaluates pointwise. -/
theorem nsmulCap_apply {p : ℤ} (n : ℕ) (c : degree δ f p)
    {Y : AlgebraicSpace S} (g : Y ⟶ X)
    [QuasiSeparated (g ≫ f)] [LocallyOfFiniteType (g ≫ f)] (k : ℤ) :
    (nsmulCap δ f n c).cap g k = n • c.cap g k :=
  sorry

/-- Integer scalar multiplication of an identity cap family. -/
def zsmulCapFamily {p : ℤ} (z : ℤ) (c : degree δ f p) : CapFamily δ f p :=
  fun {Y} (g : Y ⟶ X)
      [QuasiSeparated (g ≫ f)] [LocallyOfFiniteType (g ≫ f)] (k : ℤ) ↦
    z • c.cap g k

/-- Integer scalar multiplication satisfies proper-pushforward compatibility. -/
theorem zsmulCapFamily_map_proper {p : ℤ} (z : ℤ) (c : degree δ f p) :
    CompatibleWithProperPushforward δ f (zsmulCapFamily δ f z c) :=
  sorry

/-- Integer scalar multiplication satisfies flat-pullback compatibility. -/
theorem zsmulCapFamily_pullback_flat {p : ℤ} (z : ℤ) (c : degree δ f p) :
    CompatibleWithFlatPullback δ f (zsmulCapFamily δ f z c) :=
  sorry

/-- Integer scalar multiplication satisfies Gysin compatibility. -/
theorem zsmulCapFamily_gysin_cartier {p : ℤ} (z : ℤ) (c : degree δ f p) :
    CompatibleWithCartierGysin δ f (zsmulCapFamily δ f z c) :=
  sorry

/-- Integer scalar multiplication of an identity class. -/
def zsmulCap {p : ℤ} (z : ℤ) (c : degree δ f p) : degree δ f p :=
  ofCap δ f (zsmulCapFamily δ f z c)
    (zsmulCapFamily_map_proper δ f z c)
    (zsmulCapFamily_pullback_flat δ f z c)
    (zsmulCapFamily_gysin_cartier δ f z c)

/-- Integer scalar multiplication evaluates pointwise. -/
theorem zsmulCap_apply {p : ℤ} (z : ℤ) (c : degree δ f p)
    {Y : AlgebraicSpace S} (g : Y ⟶ X)
    [QuasiSeparated (g ≫ f)] [LocallyOfFiniteType (g ≫ f)] (k : ℤ) :
    (zsmulCap δ f z c).cap g k = z • c.cap g k :=
  sorry

/-- Every identity bivariant degree is an additive commutative group under
pointwise operations. -/
instance instAddCommGroupDegree (p : ℤ) : AddCommGroup (degree δ f p) where
  zero := zeroCap δ f p
  add := addCap δ f
  neg := negCap δ f
  sub := fun c d ↦ addCap δ f c (negCap δ f d)
  nsmul := nsmulCap δ f
  zsmul := zsmulCap δ f
  zero_add := sorry
  add_zero := sorry
  add_assoc := sorry
  add_comm := sorry
  neg_add_cancel := sorry
  nsmul_zero := sorry
  nsmul_succ := sorry
  zsmul_zero' := sorry
  zsmul_succ' := sorry
  zsmul_neg' := sorry
  sub_eq_add_neg := sorry

/-- The identity cap family in degree zero. -/
def oneCapFamily : CapFamily δ f 0 :=
  fun {Y} (g : Y ⟶ X)
      [QuasiSeparated (g ≫ f)] [LocallyOfFiniteType (g ≫ f)] (k : ℤ) ↦
    castChowGroup δ (g ≫ f) (sub_zero k).symm

/-- The identity cap family satisfies proper-pushforward compatibility. -/
theorem oneCapFamily_map_proper :
    CompatibleWithProperPushforward δ f (oneCapFamily δ f) :=
  sorry

/-- The identity cap family satisfies flat-pullback compatibility. -/
theorem oneCapFamily_pullback_flat :
    CompatibleWithFlatPullback δ f (oneCapFamily δ f) :=
  sorry

/-- The identity cap family satisfies Gysin compatibility. -/
theorem oneCapFamily_gysin_cartier :
    CompatibleWithCartierGysin δ f (oneCapFamily δ f) :=
  sorry

/-- The degree-zero identity class, acting by the identity of Chow groups. -/
def oneCap : degree δ f 0 :=
  ofCap δ f (oneCapFamily δ f)
    (oneCapFamily_map_proper δ f)
    (oneCapFamily_pullback_flat δ f)
    (oneCapFamily_gysin_cartier δ f)

/-- The identity class is the identity on Chow groups, reindexed along
`k - 0 = k`. -/
theorem oneCap_apply {Y : AlgebraicSpace S} (g : Y ⟶ X)
    [QuasiSeparated (g ≫ f)] [LocallyOfFiniteType (g ≫ f)] (k : ℤ) :
    (oneCap δ f).cap g k = castChowGroup δ (g ≫ f) (sub_zero k).symm :=
  sorry

/-- Composition of identity cap families, using the degree-shifted
intermediate operation. -/
def mulCapFamily {p q : ℤ} (c : degree δ f p) (d : degree δ f q) :
    CapFamily δ f (p + q) :=
  fun {Y} (g : Y ⟶ X)
      [QuasiSeparated (g ≫ f)] [LocallyOfFiniteType (g ≫ f)] (k : ℤ) ↦
    (castChowGroup δ (g ≫ f) (mulCap_degree_eq k p q)).comp
      ((c.cap g (k - q)).comp (d.cap g k))

/-- Composed cap families satisfy proper-pushforward compatibility. -/
theorem mulCapFamily_map_proper {p q : ℤ} (c : degree δ f p)
    (d : degree δ f q) :
    CompatibleWithProperPushforward δ f (mulCapFamily δ f c d) :=
  sorry

/-- Composed cap families satisfy flat-pullback compatibility. -/
theorem mulCapFamily_pullback_flat {p q : ℤ} (c : degree δ f p)
    (d : degree δ f q) :
    CompatibleWithFlatPullback δ f (mulCapFamily δ f c d) :=
  sorry

/-- Composed cap families satisfy Gysin compatibility. -/
theorem mulCapFamily_gysin_cartier {p q : ℤ} (c : degree δ f p)
    (d : degree δ f q) :
    CompatibleWithCartierGysin δ f (mulCapFamily δ f c d) :=
  sorry

/-- Homogeneous multiplication is composition of identity bivariant
classes, with the right factor acting first. -/
def mulCap {p q : ℤ} (c : degree δ f p) (d : degree δ f q) :
    degree δ f (p + q) :=
  ofCap δ f (mulCapFamily δ f c d)
    (mulCapFamily_map_proper δ f c d)
    (mulCapFamily_pullback_flat δ f c d)
    (mulCapFamily_gysin_cartier δ f c d)

/-- Cap-family multiplication is composition of the shifted additive maps,
reindexed along `(k - q) - p = k - (p + q)`. -/
theorem mulCap_apply {p q : ℤ} (c : degree δ f p) (d : degree δ f q)
    {Y : AlgebraicSpace S} (g : Y ⟶ X)
    [QuasiSeparated (g ≫ f)] [LocallyOfFiniteType (g ≫ f)] (k : ℤ) :
    (mulCap δ f c d).cap g k =
      (castChowGroup δ (g ≫ f) (mulCap_degree_eq k p q)).comp
        ((c.cap g (k - q)).comp (d.cap g k)) :=
  sorry

/-- Natural-number casts in degree zero, as multiples of the identity class. -/
def natCastCap (n : ℕ) : degree δ f 0 :=
  nsmulCap δ f n (oneCap δ f)

/-- Integer casts in degree zero. -/
def intCastCap (z : ℤ) : degree δ f 0 :=
  zsmulCap δ f z (oneCap δ f)

/-- The Chow cohomology ring `A^*(X)` of a good algebraic space `X / B`. -/
abbrev ring : Type (u + 1) :=
  ⨁ p : ℤ, degree δ f p

/-- Chow cohomology is the external direct sum of the identity bivariant
groups. -/
theorem ring_def : ring δ f = ⨁ p : ℤ, degree δ f p :=
  sorry

/-- Homogeneous multiplication by zero on the right vanishes. -/
theorem mulCap_zero {p q : ℤ} (c : degree δ f p) :
    mulCap δ f c (0 : degree δ f q) = 0 :=
  sorry

/-- Homogeneous multiplication by zero on the left vanishes. -/
theorem zero_mulCap {p q : ℤ} (d : degree δ f q) :
    mulCap δ f (0 : degree δ f p) d = 0 :=
  sorry

/-- Homogeneous multiplication distributes over addition in the right
variable. -/
theorem mulCap_add {p q : ℤ} (c : degree δ f p) (d e : degree δ f q) :
    mulCap δ f c (d + e) = mulCap δ f c d + mulCap δ f c e :=
  sorry

/-- Homogeneous multiplication distributes over addition in the left
variable. -/
theorem add_mulCap {p q : ℤ} (c d : degree δ f p) (e : degree δ f q) :
    mulCap δ f (c + d) e = mulCap δ f c e + mulCap δ f d e :=
  sorry

/-- Natural-number casts send zero to zero. -/
theorem natCastCap_zero : natCastCap δ f 0 = 0 :=
  sorry

/-- Natural-number casts respect successors. -/
theorem natCastCap_succ (n : ℕ) :
    natCastCap δ f (n + 1) = natCastCap δ f n + oneCap δ f :=
  sorry

/-- Integer casts extend natural-number casts. -/
theorem intCastCap_ofNat (n : ℕ) : intCastCap δ f n = natCastCap δ f n :=
  sorry

/-- Integer casts of negative successors are negatives of natural-number
casts. -/
theorem intCastCap_negSucc (n : ℕ) :
    intCastCap δ f (Int.negSucc n) = -(natCastCap δ f (n + 1)) :=
  sorry

/-- Graded ring operations on identity bivariant classes, with real
one/mul/natCast/intCast data and no commutativity claim. -/
instance instGRing : DirectSum.GRing (degree δ f) where
  mul := mulCap δ f
  mul_zero := mulCap_zero δ f
  zero_mul := zero_mulCap δ f
  mul_add := mulCap_add δ f
  add_mul := add_mulCap δ f
  one := oneCap δ f
  one_mul := sorry
  mul_one := sorry
  mul_assoc := sorry
  gnpow_zero' := sorry
  gnpow_succ' := sorry
  natCast := natCastCap δ f
  natCast_zero := natCastCap_zero δ f
  natCast_succ := natCastCap_succ δ f
  intCast := intCastCap δ f
  intCast_ofNat := intCastCap_ofNat δ f
  intCast_negSucc_ofNat := intCastCap_negSucc δ f

/-- The Chow cohomology ring `A^*(X)` carries the ring structure induced by
graded composition of identity bivariant classes. -/
instance instRing : Ring (ring δ f) :=
  inferInstanceAs (Ring (⨁ p : ℤ, degree δ f p))

/-- Embed a homogeneous identity class in the full Chow cohomology ring. -/
def homogeneous (p : ℤ) (c : degree δ f p) : ring δ f :=
  DirectSum.of (degree δ f) p c

/-- `homogeneous p c` is the direct-sum inclusion of the degree-`p` class. -/
theorem homogeneous_eq (p : ℤ) (c : degree δ f p) :
    homogeneous δ f p c = DirectSum.of (degree δ f) p c :=
  sorry

end ChowCohomology

end AlgebraicGeometry.AlgebraicSpace
