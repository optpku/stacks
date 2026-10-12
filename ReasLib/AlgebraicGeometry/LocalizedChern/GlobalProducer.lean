/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Divisor.ComplexChart.GlobalEtaComparison
public import ReasLib.AlgebraicGeometry.LocalizedChern.ClosedCover.Constructed
public import ReasLib.AlgebraicGeometry.LocalizedChern.DerivedEnvelopeCaps
public import ReasLib.AlgebraicGeometry.LocalizedChern.Situation
public import ReasLib.AlgebraicGeometry.BivariantClass.GysinAtInfinity

/-!
# The displayed graph data and localized infinity operation

All geometric objects are obtained from original E and its Situation.
The ambient derived class is the fixed all-envelope cap descent; the infinity
localized class is the fixed closed-cover cap descent. No output Q, W, T,
ambient class, localized class or ClassConstruction witness is a parameter.
-/

@[expose] public section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open Scheme.PerfectGraphAtlas
noncomputable section
universe u

namespace AlgebraicGeometry.LocalizedChern.GlobalProducer

variable {S : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
  (X : Over S) [LocallyOfFiniteType X.hom] {Z : Scheme.{u}}
  (i : Z ⟶ X.left) [IsClosedImmersion i]
  (classes : ChernClass.Theory δ X.hom)
  (E : RingedSpace.ModuleDerived X.left.toRingedSpace) (q : ℕ)
  (mode : RestrictionBehavior) (situation : Situation S δ X i E q mode)

abbrev projection : ProjectiveLineFamily.space X ⟶ X.left :=
  pullback.fst X.hom (ProjectiveSpace.toBase 1 S)

abbrev divisor := BivariantClass.GysinAtInfinity.ambientInfinityDivisor X

def W : Scheme.{u} := globalW E situation.perfect (projection X) (divisor X)

def b : W δ X i E q mode situation ⟶ ProjectiveLineFamily.space X :=
  globalB E situation.perfect (projection X) (divisor X)

def Q : RingedSpace.ModuleDerived (W δ X i E q mode situation).toRingedSpace :=
  globalQ E situation.perfect (projection X) (divisor X)

def T : Scheme.{u} := globalT E situation.perfect (projection X) (divisor X)

abbrev graphDivisor := globalDivisor E situation.perfect (projection X) (divisor X)

instance b_proper : IsProper (b δ X i E q mode situation) := by
  sorry

instance b_affine_iso : IsIso
    (b δ X i E q mode situation ∣_ BivariantClass.GysinAtInfinity.affinePart X) := by
  sorry

/-- The actual quotient inclusion identifying the pullback ideal presentation
with the existing zero-scheme presentation of the infinity divisor. -/
def toInfinity : (graphDivisor δ X i E q mode situation).subscheme ⟶
    (BivariantClass.GysinAtInfinity.infinityFiber X (b δ X i E q mode situation)).left :=
  Scheme.IdealSheafData.inclusion
    (BivariantClass.GysinAtInfinity.infinityDivisor_eq_comap X
      (b δ X i E q mode situation)).le

def t : T δ X i E q mode situation ⟶
    (BivariantClass.GysinAtInfinity.infinityFiber X (b δ X i E q mode situation)).left :=
  globalTToDivisor E situation.perfect (projection X) (divisor X) ≫
    toInfinity δ X i E q mode situation

instance t_closed : IsClosedImmersion (t δ X i E q mode situation) := by
  sorry

def Tprime : Scheme.{u} :=
  if mode.isRankBound then globalTRankLT E situation.perfect (projection X) (divisor X) q
  else globalTVanishing E situation.perfect (projection X) (divisor X)

def tprime : Tprime δ X i E q mode situation ⟶ T δ X i E q mode situation := by
  unfold Tprime
  split
  · exact globalTRankLTInclusion E situation.perfect (projection X) (divisor X) q
  · exact globalTVanishingInclusion E situation.perfect (projection X) (divisor X)

instance tprime_open : IsOpenImmersion (tprime δ X i E q mode situation) := by
  sorry

instance tprime_closed : IsClosedImmersion (tprime δ X i E q mode situation) := by
  sorry

abbrev infinity : Over S :=
  BivariantClass.GysinAtInfinity.infinityFiber X (b δ X i E q mode situation)

abbrev infinityToX : infinity δ X i E q mode situation ⟶ X :=
  BivariantClass.GysinAtInfinity.infinityToX X (b δ X i E q mode situation)

abbrev center : Over S :=
  pullback (infinityToX δ X i E q mode situation) (Over.homMk i : Over.mk (i ≫ X.hom) ⟶ X)

abbrev centerMap : center δ X i E q mode situation ⟶ infinity δ X i E q mode situation :=
  pullback.fst _ _

instance infinity_finiteType : LocallyOfFiniteType (infinity δ X i E q mode situation).hom := by
  infer_instance

instance center_finiteType : LocallyOfFiniteType (center δ X i E q mode situation).hom := by
  sorry

instance center_closed : IsClosedImmersion (centerMap δ X i E q mode situation).left := by
  sorry

def centerInput : RingedSpace.ModuleDerived (center δ X i E q mode situation).left.toRingedSpace :=
  (RingedSpace.modulePullbackDerived
    ((centerMap δ X i E q mode situation).left ≫
      (BivariantClass.GysinAtInfinity.infinityInclusion X (b δ X i E q mode situation)).left).toShHom).obj
    (Q δ X i E q mode situation)

theorem centerInput_perfect : RingedSpace.ModuleDerived.IsPerfect (centerInput δ X i E q mode situation) := by
  sorry

/-- Original technical finiteness gives eligible envelope models for this
specific Q restriction. This proposition is used only to prove surjectivity
of the fixed sum over all actual models; no envelope or Q is selected from it. -/
theorem centerInput_defined :
    ∃ (Y : Scheme.{u}) (f : Y ⟶ (center δ X i E q mode situation).left), IsEnvelope f ∧
      RingedSpace.ModuleDerived.HasLocallyBoundedFiniteLocallyFreeRepresentative
        ((RingedSpace.modulePullbackDerived f.toShHom).obj (centerInput δ X i E q mode situation)) := by
  sorry

/-- The actual ambient class, using the original theory and explicit envelope cap descent. -/
def ambient : BivariantClass δ (𝟙 (center δ X i E q mode situation)) (q : ℤ) :=
  EnvelopeCaps.derivedClass δ (classes.reanchor (center δ X i E q mode situation))
    (centerInput δ X i E q mode situation) (centerInput_perfect δ X i E q mode situation)
    (centerInput_defined δ X i E q mode situation) mode.isRankBound q

abbrev firstMap := tprime δ X i E q mode situation ≫ t δ X i E q mode situation

instance firstMap_closed : IsClosedImmersion (firstMap δ X i E q mode situation) := by
  infer_instance

theorem cover : Set.range (firstMap δ X i E q mode situation) ∪
    Set.range (centerMap δ X i E q mode situation).left = Set.univ := by
  sorry

/-- Repackage the same center carrier over S with the displayed inclusion;
the map is the identity on its underlying scheme, with the existing Over.w. -/
def centerDisplayIso : center δ X i E q mode situation ≅
    Over.mk ((centerMap δ X i E q mode situation).left ≫ (infinity δ X i E q mode situation).hom) :=
  Over.isoMk (Iso.refl _) (by
    exact (Category.id_comp _).trans (centerMap δ X i E q mode situation).w)

def ambientDisplay : BivariantClass δ
    (𝟙 (Over.mk ((centerMap δ X i E q mode situation).left ≫ (infinity δ X i E q mode situation).hom)))
    (q : ℤ) :=
  BivariantClass.restrict δ (centerDisplayIso δ X i E q mode situation).inv
    (𝟙 _) (centerDisplayIso δ X i E q mode situation).inv IsPullback.of_id_snd (q : ℤ)
    (ambient δ X i classes E q mode situation)

theorem intersection_vanishing : Constructed.IntersectionVanishes δ
    (firstMap δ X i E q mode situation) (centerMap δ X i E q mode situation).left
    (q : ℤ) (ambientDisplay δ X i classes E q mode situation) := by
  sorry

/-- The localized infinity class on the displayed copy of the actual center. -/
def infinityLocalizedDisplay : BivariantClass δ
    (Over.homMk (centerMap δ X i E q mode situation).left :
      Over.mk ((centerMap δ X i E q mode situation).left ≫ (infinity δ X i E q mode situation).hom) ⟶
        infinity δ X i E q mode situation) (q : ℤ) :=
  Constructed.localized δ (firstMap δ X i E q mode situation)
    (centerMap δ X i E q mode situation).left (q : ℤ)
    (ambientDisplay δ X i classes E q mode situation) (cover δ X i E q mode situation)
    (intersection_vanishing δ X i classes E q mode situation)

/-- The canonical source-presentation square has the identity underlying maps. -/
theorem centerPresentationSquare : IsPullback (centerDisplayIso δ X i E q mode situation).hom.left
    (centerMap δ X i E q mode situation).left
    (Over.homMk (centerMap δ X i E q mode situation).left :
      Over.mk ((centerMap δ X i E q mode situation).left ≫ (infinity δ X i E q mode situation).hom) ⟶
        infinity δ X i E q mode situation).left
      ((𝟙 (infinity δ X i E q mode situation) :
        infinity δ X i E q mode situation ⟶ infinity δ X i E q mode situation)).left := by
  sorry

/-- The actual localized-infinity output on the original canonical center map. -/
def localizedInfinity : BivariantClass δ (centerMap δ X i E q mode situation) (q : ℤ) :=
  BivariantClass.restrict δ (centerDisplayIso δ X i E q mode situation).hom
    (centerMap δ X i E q mode situation) (𝟙 (infinity δ X i E q mode situation))
    (centerPresentationSquare δ X i E q mode situation) (q : ℤ)
    (infinityLocalizedDisplay δ X i classes E q mode situation)

end AlgebraicGeometry.LocalizedChern.GlobalProducer
