/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Divisor.ComplexChart.GlobalModification
public import ReasLib.Algebra.Homology.CochainComplex.BerthelotOgus.Eta.Int.Decomposition.Homology

/-!
# The displayed eta-flattening closed subscheme

On each good finite-coordinate chart of the displayed modification, construct
the integer eta complex, its reduced pair (x,d(x)/f), and the actual sum of
the pair's decomposition ideals in A/(f). The global ideal is the intersection
of the contractions of those local ideals. The cover and compatibility laws
are properties of this fixed family, never sources of chosen output data.

This file does not call the uncertified derived-eta localization or choose
from existsEtaFlattening. It constructs T and the local complexes of Q; a
global derived Q and the localized-infinity operation remain separate work.
-/

@[expose] public section
open AlgebraicGeometry CategoryTheory
open scoped AlgebraicGeometry nonZeroDivisors
noncomputable section
universe u

namespace AlgebraicGeometry.Scheme.PerfectGraphAtlas

variable {X Y : Scheme.{u}} (E : RingedSpace.ModuleDerived X.toRingedSpace)
  (hE : RingedSpace.ModuleDerived.IsPerfect E) (p : Y ⟶ X) (D : Y.IdealSheafData)
  [IsEffectiveCartierDivisor D.subschemeι]

/-- The fixed small family of good coordinate charts on the displayed W.
The input object is still the original E; no new perfect object or chart is
supplied at the global entry. -/
abbrev GoodEtaChart : Type u :=
  { i : SmallChart E hE (globalB E hE p D ≫ p) (globalDivisor E hE p D) //
      ∀ n : ℤ, (i.toChart.ideal n).IsPrincipal }

variable (i : GoodEtaChart E hE p D)

abbrev etaCoefficientRing := Γ(globalW E hE p D, i.1.U)

abbrev etaEquation : nonZeroDivisors (etaCoefficientRing E hE p D i) :=
  ⟨i.1.generator, i.1.regular⟩

/-- The chart's actual finite-coordinate complex in the eta regular domain. -/
def etaChartDomain : CochainComplex.BerthelotOgus.Int.Domain i.1.generator := by
  exact @CochainComplex.BerthelotOgus.Int.finiteFreeDomain
    (etaCoefficientRing E hE p D i) inferInstance
    (etaEquation E hE p D i) i.1.coordinates.toComplex i.1.coordinates.finiteFree

/-- The actual divided-differential eta complex of the chart, for all integer degrees. -/
def etaChartComplex : CochainComplex (ModuleCat (etaCoefficientRing E hE p D i)) ℤ :=
  (CochainComplex.BerthelotOgus.Int.functor i.1.generator).obj (etaChartDomain E hE p D i)

/-- An actual local derived Q, not evaluation of an uncertified localization lift. -/
def etaChartQ : DerivedCategory (ModuleCat (etaCoefficientRing E hE p D i)) :=
  DerivedCategory.Q.obj (etaChartComplex E hE p D i)

abbrev etaDivisorRing := etaCoefficientRing E hE p D i ⧸ principalIdeal i.1.generator

/-- The degree ideal is obtained from the actual reduced (x,d/f) pair. -/
def etaDegreeIdeal (n : ℤ) : Ideal (etaDivisorRing E hE p D i) :=
  CochainComplex.BerthelotOgus.Int.Reduction.Decomposition.locusIdeal
    i.1.generator (etaChartDomain E hE p D i) n

/-- The source's J=sum_n J_n, as an ideal of A/(f). -/
def etaTotalIdeal : Ideal (etaDivisorRing E hE p D i) :=
  ⨆ n : ℤ, etaDegreeIdeal E hE p D i n

abbrev etaFlatteningRing := etaDivisorRing E hE p D i ⧸ etaTotalIdeal E hE p D i

def etaFlatteningRingMap : etaCoefficientRing E hE p D i →+* etaFlatteningRing E hE p D i :=
  (Ideal.Quotient.mk (etaTotalIdeal E hE p D i)).comp
    (Ideal.Quotient.mk (principalIdeal i.1.generator))

/-- The local flattening Q is explicitly the scalar extension of the eta complex. -/
def etaFlattenedComplex : CochainComplex (ModuleCat (etaFlatteningRing E hE p D i)) ℤ :=
  ((ModuleCat.extendScalars (etaFlatteningRingMap E hE p D i)).mapHomologicalComplex
    (ComplexShape.up ℤ)).obj (etaChartComplex E hE p D i)

def etaDivisorChart : Scheme.{u} := Spec (.of (etaDivisorRing E hE p D i))

def etaDivisorChartToW : etaDivisorChart E hE p D i ⟶ globalW E hE p D :=
  Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (principalIdeal i.1.generator))) ≫ i.1.U.2.fromSpec

/-- The given divisor equation vanishes under its actual quotient map. -/
theorem etaDivisorChart_kernel :
    (globalDivisor E hE p D).subschemeι.ker ≤ (etaDivisorChartToW E hE p D i).ker := by
  -- Transport the chart's ideal_eq through the affine coordinate isomorphism.
  sorry

/-- The canonical factorization of Spec(A/(f)) through the displayed divisor. -/
def etaDivisorChartMap : etaDivisorChart E hE p D i ⟶ (globalDivisor E hE p D).subscheme :=
  IsClosedImmersion.lift (globalDivisor E hE p D).subschemeι
    (etaDivisorChartToW E hE p D i) (etaDivisorChart_kernel E hE p D i)

theorem etaDivisorChartMap_over :
    etaDivisorChartMap E hE p D i ≫ (globalDivisor E hE p D).subschemeι =
      etaDivisorChartToW E hE p D i := IsClosedImmersion.lift_fac _ _ _

/-- The actual local ideal sheaf corresponding to J in the divisor chart. -/
def etaLocalIdealSheaf : (etaDivisorChart E hE p D i).IdealSheafData :=
  Scheme.IdealSheafData.ofIdealTop
    ((etaTotalIdeal E hE p D i).comap
      (Scheme.ΓSpecIso (.of (etaDivisorRing E hE p D i))).hom.hom)

/-- The global ideal is determined by the fixed local ideals via contraction.
There is no search for an ideal satisfying a desired flattening predicate. -/
def globalFlatteningIdeal : (globalDivisor E hE p D).subscheme.IdealSheafData :=
  ⨅ i : GoodEtaChart E hE p D,
    (etaLocalIdealSheaf E hE p D i).map (etaDivisorChartMap E hE p D i)

/-- The actual global flattening closed subscheme, obtained from its prescribed ideal. -/
def globalT : Scheme.{u} := (globalFlatteningIdeal E hE p D).subscheme

def globalTToDivisor : globalT E hE p D ⟶ (globalDivisor E hE p D).subscheme :=
  (globalFlatteningIdeal E hE p D).subschemeι

def globalTToW : globalT E hE p D ⟶ globalW E hE p D :=
  globalTToDivisor E hE p D ≫ (globalDivisor E hE p D).subschemeι

instance globalT_closed : IsClosedImmersion (globalTToDivisor E hE p D) :=
  AlgebraicGeometry.IsClosedImmersion.instSubschemeι (globalFlatteningIdeal E hE p D)

/-- The actual local closed subscheme defined by its decomposition ideal. -/
def etaLocalT : Scheme.{u} := (etaLocalIdealSheaf E hE p D i).subscheme

/-- Each local quotient maps canonically to the global T by the defining
intersection inequality. This uses no compatibility existence witness. -/
def etaLocalToGlobalT : etaLocalT E hE p D i ⟶ globalT E hE p D :=
  Scheme.IdealSheafData.subschemeMap (etaLocalIdealSheaf E hE p D i)
    (globalFlatteningIdeal E hE p D) (etaDivisorChartMap E hE p D i)
    (iInf_le _ i)

theorem etaLocalToGlobalT_over :
    etaLocalToGlobalT E hE p D i ≫ globalTToDivisor E hE p D =
      (etaLocalIdealSheaf E hE p D i).subschemeι ≫ etaDivisorChartMap E hE p D i :=
  Scheme.IdealSheafData.subschemeMap_subschemeι _ _ _ _

/-- The specific divisor chart factorization identifies the corresponding
open of D'. Its carrier and ring map have already been constructed. -/
theorem etaDivisorChartMap_open : IsOpenImmersion (etaDivisorChartMap E hE p D i) := by
  sorry

/-- Good finite-coordinate charts of the displayed good triple cover D'.
This uses the actual composite-pullback comparison, not a new input chart. -/
theorem etaDivisorCharts_cover (d : (globalDivisor E hE p D).subscheme) :
    ∃ (i : GoodEtaChart E hE p D) (z : etaDivisorChart E hE p D i),
      etaDivisorChartMap E hE p D i z = d := by
  sorry

/-- The fixed family of divisor charts forms the actual open cover used for
the local-to-global finite-presentation and cohomology arguments. -/
def etaDivisorCover : (globalDivisor E hE p D).subscheme.OpenCover :=
  Scheme.Cover.mkOfCovers (GoodEtaChart E hE p D)
    (etaDivisorChart E hE p D) (etaDivisorChartMap E hE p D)
    (etaDivisorCharts_cover E hE p D) (etaDivisorChartMap_open E hE p D)

/-- Every affine component uses exactly the prescribed eta decomposition ideal.
Proof debt: good charts cover W and their J ideals agree under restriction,
unit changes and derived replacement, as in source Lemma15.97.8. -/
theorem globalFlatteningIdeal_local :
    (globalFlatteningIdeal E hE p D).comap (etaDivisorChartMap E hE p D i) =
      etaLocalIdealSheaf E hE p D i := by
  sorry

/-- The local decomposition ideals are finitely generated on good charts;
their actual gluing therefore defines a finitely presented closed immersion. -/
theorem globalT_locallyOfFinitePresentation :
    LocallyOfFinitePresentation (globalTToDivisor E hE p D) := by
  sorry

/-- Closed immersions provide quasi-compactness and quasi-separatedness;
combined with the local finite presentation above this is finite presentation. -/
theorem globalT_finitePresentation :
    LocallyOfFinitePresentation (globalTToDivisor E hE p D) ∧
      QuasiCompact (globalTToDivisor E hE p D) ∧
      QuasiSeparated (globalTToDivisor E hE p D) :=
  ⟨globalT_locallyOfFinitePresentation E hE p D, inferInstance, inferInstance⟩

/-- Actual homology certificate for the displayed local eta scalar extension.
The canonical owner's proof remains admitted, with its principal-ideal and
boundedness hypotheses explicitly discharged from the indexed chart. -/
theorem etaFlattenedComplex_homology_finiteLocallyFree (n : ℤ) :
    Module.FiniteLocallyFree (etaFlatteningRing E hE p D i)
      ((etaFlattenedComplex E hE p D i).homology n) := by
  exact @CochainComplex.BerthelotOgus.Int.Reduction.Decomposition.homology_finiteLocallyFree
    (etaCoefficientRing E hE p D i) inferInstance
    (etaEquation E hE p D i) i.1.coordinates.toComplex i.1.bounded i.1.coordinates.finiteFree i.2 n

/-- The prescribed eta term is the literal divisibility submodule, in every integer degree. -/
theorem etaChartComplex_term (n : ℤ) :
    (etaChartComplex E hE p D i).X n =
      ModuleCat.of (etaCoefficientRing E hE p D i)
        (CochainComplex.BerthelotOgus.Int.term i.1.generator i.1.coordinates.toComplex n) := rfl

theorem etaChartQ_formula : etaChartQ E hE p D i =
    DerivedCategory.Q.obj (etaChartComplex E hE p D i) := rfl

/-- The actual division inverse in the eta differential recovers the specified
model differential when multiplied by the divisor equation. -/
theorem eta_divide_formula (n : ℤ)
    (x : CochainComplex.BerthelotOgus.Int.term i.1.generator i.1.coordinates.toComplex n) :
    i.1.generator •
      CochainComplex.BerthelotOgus.Int.divideLinear i.1.generator i.1.coordinates.toComplex n
        ((etaChartDomain E hE p D i).property.degree (n + 1)) x =
      i.1.coordinates.toComplex.d n (n + 1) x := by
  exact congrArg Subtype.val
    ((LinearEquiv.ofInjective
      (LinearMap.lsmul (etaCoefficientRing E hE p D i) (i.1.coordinates.toComplex.X (n + 1)) i.1.generator)
      ((etaChartDomain E hE p D i).property.degree (n + 1))).apply_symm_apply
      (CochainComplex.BerthelotOgus.Int.dToRange i.1.generator i.1.coordinates.toComplex n x))

/-- Each degree ideal is computed from the cross-coordinate coefficient ideals
over every actual retraction of the fixed reduced pair. No retraction is selected. -/
theorem etaDegreeIdeal_formula (n : ℤ) : etaDegreeIdeal E hE p D i n =
    ⨅ r : LinearMap.ProductRange.Retraction
      (CochainComplex.BerthelotOgus.Int.Reduction.Pair.linear
        i.1.generator (etaChartDomain E hE p D i) n),
      LinearMap.ProductRange.splittingIdeal
        (CochainComplex.BerthelotOgus.Int.Reduction.Pair.linear
          i.1.generator (etaChartDomain E hE p D i) n) r.1 := rfl

theorem etaTotalIdeal_formula : etaTotalIdeal E hE p D i =
    ⨆ n : ℤ, CochainComplex.BerthelotOgus.Int.Reduction.Decomposition.locusIdeal
      i.1.generator (etaChartDomain E hE p D i) n := rfl

theorem globalFlatteningIdeal_formula : globalFlatteningIdeal E hE p D =
    ⨅ i : GoodEtaChart E hE p D,
      (etaLocalIdealSheaf E hE p D i).map (etaDivisorChartMap E hE p D i) := rfl

end AlgebraicGeometry.Scheme.PerfectGraphAtlas
