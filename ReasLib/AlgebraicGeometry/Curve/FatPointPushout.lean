/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Algebra.Prod
public import Mathlib.Algebra.CharP.Basic
public import Mathlib.Algebra.DualNumber
public import Mathlib.Algebra.MvPolynomial.Equiv
public import Mathlib.Algebra.Polynomial.AlgebraMap
public import Mathlib.Algebra.Ring.Prod
public import Mathlib.Algebra.Ring.Subring.Basic
public import Mathlib.AlgebraicGeometry.AffineSpace
public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.CategoryTheory.Comma.Over.Pullback
public import Mathlib.CategoryTheory.Endomorphism
public import Mathlib.Data.Finite.Defs
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.RingTheory.DualNumber
public import Mathlib.RingTheory.Ideal.Quotient.Basic
public import Mathlib.RingTheory.Polynomial.Basic
public import ReasLib.AlgebraicGeometry.ProjectiveSpace.Line
public import ReasLib.AlgebraicGeometry.Scheme.Automorphism.UniversalFamily
public import ReasLib.AlgebraicGeometry.Scheme.Pushout.ClosedImmersion
public import ReasLib.CategoryTheory.Limits.Shapes.Equalizer

/-!
# A non-reduced automorphism group of a fat-point pushout

This file records the glued curve obtained by identifying two copies of the projective line along
three double points, together with the dual-number automorphism that shows `Aut` is non-reduced.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open Polynomial
open scoped AlgebraicGeometry DualNumber

noncomputable section

universe u

namespace AlgebraicGeometry.FatPointPushout

variable {k : Type u} [Field k]

/-- The square of the maximal ideal at a `k`-point `a` of the affine line. -/
def doublePointIdeal (a : k) : Ideal (Polynomial k) :=
  Ideal.span ({X - C a} : Set (Polynomial k)) ^ 2

/-- Membership in `doublePointIdeal a` means divisibility by `(X - C a)^2`. -/
theorem mem_doublePointIdeal {a : k} {f : Polynomial k} :
    f ∈ doublePointIdeal a ↔ ∃ g : Polynomial k, f = g * (X - C a) ^ 2 := sorry

/-- The fat point `Spec(k[t] / (t - a)^2)`. -/
abbrev doublePoint (a : k) : Scheme.{u} :=
  Spec (CommRingCat.of (Polynomial k ⧸ doublePointIdeal a))

/-- The coordinate ring of one fat point. -/
abbrev doublePointRing (a : k) : Type u :=
  Polynomial k ⧸ doublePointIdeal a

/-- The closed thickening `T` is the coproduct of the three fat points. -/
def thickening (a b c : k) : Scheme.{u} :=
  doublePoint a ⨿ (doublePoint b ⨿ doublePoint c)

/-- The standard identification of the projective-line affine chart with `Spec(k[t])`. -/
def affineLineIso :
    ProjectiveLine.affineLine k ≅ Spec (CommRingCat.of (Polynomial k)) :=
  AffineSpace.SpecIso (ULift.{u} (Fin 1)) (CommRingCat.of k) ≪≫
    Scheme.Spec.mapIso
      (RingEquiv.toCommRingCatIso
        (MvPolynomial.uniqueAlgEquiv k (ULift.{u} (Fin 1))).toRingEquiv).op.symm

/-- The open immersion `A^1_k ⊂ P^1_k` realized on `Spec(k[t])`. -/
def affineLineι : Spec (CommRingCat.of (Polynomial k)) ⟶ ProjectiveLine.scheme k :=
  affineLineIso.inv ≫ (ProjectiveLine.chartXIso k).inv ≫ (ProjectiveLine.chartX k).ι

/-- The canonical closed immersion of one fat point into the affine line. -/
def doublePointToAffineLine (a : k) :
    doublePoint a ⟶ Spec (CommRingCat.of (Polynomial k)) :=
  Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (doublePointIdeal a)))

/-- The closed immersion of one fat point into `P^1_k` along `A^1_k`. -/
def doublePointToProjectiveLine (a : k) :
    doublePoint a ⟶ ProjectiveLine.scheme k :=
  doublePointToAffineLine a ≫ affineLineι

/-- The closed immersion `T ⟶ P^1_k` of the three fat points. -/
def closedImmersion (a b c : k) (hab : a ≠ b) (hbc : b ≠ c) (hca : c ≠ a) : thickening a b c ⟶ ProjectiveLine.scheme k :=
  coprod.desc (doublePointToProjectiveLine a)
    (coprod.desc (doublePointToProjectiveLine b) (doublePointToProjectiveLine c))

/-- The morphism `T ⟶ P^1_k` is a closed immersion when `a, b, c` are pairwise distinct. -/
theorem closedImmersion_isClosedImmersion [IsAlgClosed k] [CharP k 2]
    (a b c : k) (hab : a ≠ b) (hbc : b ≠ c) (hca : c ≠ a) :
    IsClosedImmersion (closedImmersion a b c hab hbc hca) := sorry

attribute [instance] closedImmersion_isClosedImmersion

/-- The pushout `X` of two copies of `P^1_k` along `closedImmersion`. -/
def scheme [IsAlgClosed k] [CharP k 2] (a b c : k)
    (hab : a ≠ b) (hbc : b ≠ c) (hca : c ≠ a) : Scheme.{u} :=
  pushout (closedImmersion a b c hab hbc hca)
    (closedImmersion a b c hab hbc hca)

/-- The coprojection of the first projective line into the pushout `X`. -/
def leftInclusion [IsAlgClosed k] [CharP k 2] (a b c : k)
    (hab : a ≠ b) (hbc : b ≠ c) (hca : c ≠ a) :
    ProjectiveLine.scheme k ⟶ scheme a b c hab hbc hca :=
  pushout.inl (closedImmersion a b c hab hbc hca)
    (closedImmersion a b c hab hbc hca)

/-- The coprojection of the second projective line into the pushout `X`. -/
def rightInclusion [IsAlgClosed k] [CharP k 2] (a b c : k)
    (hab : a ≠ b) (hbc : b ≠ c) (hca : c ≠ a) :
    ProjectiveLine.scheme k ⟶ scheme a b c hab hbc hca :=
  pushout.inr (closedImmersion a b c hab hbc hca)
    (closedImmersion a b c hab hbc hca)

/-- `scheme a b c hab hbc hca` is the pushout of `closedImmersion` against itself. -/
theorem scheme_isPushout [IsAlgClosed k] [CharP k 2] (a b c : k)
    (hab : a ≠ b) (hbc : b ≠ c) (hca : c ≠ a) :
    IsPushout (closedImmersion a b c hab hbc hca) (closedImmersion a b c hab hbc hca)
      (leftInclusion a b c hab hbc hca) (rightInclusion a b c hab hbc hca) := sorry

/-- The structure morphism of the pushout `X` to `Spec k`. -/
def schemeToSpec [IsAlgClosed k] [CharP k 2] (a b c : k)
    (hab : a ≠ b) (hbc : b ≠ c) (hca : c ≠ a) :
    scheme a b c hab hbc hca ⟶ Spec (CommRingCat.of k) :=
  pushout.desc (ProjectiveLine.toSpec k) (ProjectiveLine.toSpec k) rfl

/-- The pushout `X` as a scheme over `Spec k`. -/
def schemeOver [IsAlgClosed k] [CharP k 2] (a b c : k)
    (hab : a ≠ b) (hbc : b ≠ c) (hca : c ≠ a) : SchemeOverField k :=
  Over.mk (schemeToSpec a b c hab hbc hca)

/-- The coproduct of two affine lines, used as the source of the affine open `U`. -/
def affineCoprod (k : Type u) [Field k] : Scheme.{u} :=
  Spec (CommRingCat.of (Polynomial k)) ⨿ Spec (CommRingCat.of (Polynomial k))

/-- The morphism `A^1_k ⨿ A^1_k ⟶ X` induced by the two affine charts. -/
def affineCoprodToScheme [IsAlgClosed k] [CharP k 2] (a b c : k)
    (hab : a ≠ b) (hbc : b ≠ c) (hca : c ≠ a) :
    affineCoprod k ⟶ scheme a b c hab hbc hca :=
  coprod.desc (affineLineι ≫ leftInclusion a b c hab hbc hca)
    (affineLineι ≫ rightInclusion a b c hab hbc hca)

/-- The pair of infinity points of the two projective-line branches in `X`. -/
def infinityPair [IsAlgClosed k] [CharP k 2] (a b c : k)
    (hab : a ≠ b) (hbc : b ≠ c) (hca : c ≠ a) : Set (scheme a b c hab hbc hca) :=
  {(leftInclusion a b c hab hbc hca).base (ProjectiveLine.infinityPoint k),
    (rightInclusion a b c hab hbc hca).base (ProjectiveLine.infinityPoint k)}

/-- A point lies in `infinityPair` exactly when it is one of the two infinity images. -/
theorem mem_infinityPair [IsAlgClosed k] [CharP k 2] (a b c : k)
    (hab : a ≠ b) (hbc : b ≠ c) (hca : c ≠ a) (x : scheme a b c hab hbc hca) :
    x ∈ infinityPair a b c hab hbc hca ↔
      x = (leftInclusion a b c hab hbc hca).base (ProjectiveLine.infinityPoint k) ∨
        x = (rightInclusion a b c hab hbc hca).base (ProjectiveLine.infinityPoint k) := sorry

/-- The two infinity points form a closed subset of `X`. -/
theorem isClosed_infinityPair [IsAlgClosed k] [CharP k 2] (a b c : k)
    (hab : a ≠ b) (hbc : b ≠ c) (hca : c ≠ a) :
    IsClosed (infinityPair a b c hab hbc hca) := sorry

/-- The affine open `U ⊂ X` is the complement of the two infinity points, i.e. the image of
`A^1_k ⨿ A^1_k`. -/
def affineOpen [IsAlgClosed k] [CharP k 2] (a b c : k)
    (hab : a ≠ b) (hbc : b ≠ c) (hca : c ≠ a) : (scheme a b c hab hbc hca).Opens :=
  ⟨(infinityPair a b c hab hbc hca)ᶜ, (isClosed_infinityPair a b c hab hbc hca).isOpen_compl⟩

/-- As a set, `affineOpen` is the image of `A^1_k ⨿ A^1_k` in `X`. -/
theorem affineOpen_eq_range [IsAlgClosed k] [CharP k 2] (a b c : k)
    (hab : a ≠ b) (hbc : b ≠ c) (hca : c ≠ a) :
    (affineOpen a b c hab hbc hca : Set (scheme a b c hab hbc hca)) =
      Set.range (affineCoprodToScheme a b c hab hbc hca).base := sorry

/-- The complement of the two infinity points is an affine open of `X`. -/
theorem affineOpen_isAffineOpen [IsAlgClosed k] [CharP k 2] (a b c : k)
    (hab : a ≠ b) (hbc : b ≠ c) (hca : c ≠ a) :
    IsAffineOpen (affineOpen a b c hab hbc hca) := sorry

/-- The left affine chart `A^1_k ⟶ X`. -/
def affineChartLeft [IsAlgClosed k] [CharP k 2] (a b c : k)
    (hab : a ≠ b) (hbc : b ≠ c) (hca : c ≠ a) :
    Spec (CommRingCat.of (Polynomial k)) ⟶ scheme a b c hab hbc hca :=
  affineLineι ≫ leftInclusion a b c hab hbc hca

/-- The right affine chart `A^1_k ⟶ X`. -/
def affineChartRight [IsAlgClosed k] [CharP k 2] (a b c : k)
    (hab : a ≠ b) (hbc : b ≠ c) (hca : c ≠ a) :
    Spec (CommRingCat.of (Polynomial k)) ⟶ scheme a b c hab hbc hca :=
  affineLineι ≫ rightInclusion a b c hab hbc hca

/-- The left affine chart lands in the affine open `U`. -/
theorem affineChartLeft_preimage_affineOpen [IsAlgClosed k] [CharP k 2] (a b c : k)
    (hab : a ≠ b) (hbc : b ≠ c) (hca : c ≠ a) :
    ⊤ ≤ affineChartLeft a b c hab hbc hca ⁻¹ᵁ affineOpen a b c hab hbc hca := sorry

/-- The right affine chart lands in the affine open `U`. -/
theorem affineChartRight_preimage_affineOpen [IsAlgClosed k] [CharP k 2] (a b c : k)
    (hab : a ≠ b) (hbc : b ≠ c) (hca : c ≠ a) :
    ⊤ ≤ affineChartRight a b c hab hbc hca ⁻¹ᵁ affineOpen a b c hab hbc hca := sorry

/-- The left parallel arrow of the equalizer, reducing the first factor at `a, b, c`. -/
def equalizerLeft (a b c : k) :
    Polynomial k × Polynomial k →+* doublePointRing a × doublePointRing b × doublePointRing c :=
  RingHom.prod
    ((Ideal.Quotient.mk (doublePointIdeal a)).comp (RingHom.fst (Polynomial k) (Polynomial k)))
    (RingHom.prod
      ((Ideal.Quotient.mk (doublePointIdeal b)).comp (RingHom.fst (Polynomial k) (Polynomial k)))
      ((Ideal.Quotient.mk (doublePointIdeal c)).comp (RingHom.fst (Polynomial k) (Polynomial k))))

/-- The right parallel arrow of the equalizer, reducing the second factor at `a, b, c`. -/
def equalizerRight (a b c : k) :
    Polynomial k × Polynomial k →+* doublePointRing a × doublePointRing b × doublePointRing c :=
  RingHom.prod
    ((Ideal.Quotient.mk (doublePointIdeal a)).comp (RingHom.snd (Polynomial k) (Polynomial k)))
    (RingHom.prod
      ((Ideal.Quotient.mk (doublePointIdeal b)).comp (RingHom.snd (Polynomial k) (Polynomial k)))
      ((Ideal.Quotient.mk (doublePointIdeal c)).comp (RingHom.snd (Polynomial k) (Polynomial k))))

/-- The canonical map on sections `Γ(X, U) ⟶ k[t] × k[t]` induced by the two affine charts. -/
def sectionsToAffineCharts [IsAlgClosed k] [CharP k 2] (a b c : k)
    (hab : a ≠ b) (hbc : b ≠ c) (hca : c ≠ a) :
    Γ(scheme a b c hab hbc hca, affineOpen a b c hab hbc hca) ⟶
      CommRingCat.of (Polynomial k × Polynomial k) :=
  CommRingCat.ofHom
    (RingHom.prod
      ((CommRingCat.Hom.hom (Scheme.ΓSpecIso (CommRingCat.of (Polynomial k))).hom).comp
        (CommRingCat.Hom.hom
          ((affineChartLeft a b c hab hbc hca).appLE (affineOpen a b c hab hbc hca) ⊤
            (affineChartLeft_preimage_affineOpen a b c hab hbc hca))))
      ((CommRingCat.Hom.hom (Scheme.ΓSpecIso (CommRingCat.of (Polynomial k))).hom).comp
        (CommRingCat.Hom.hom
          ((affineChartRight a b c hab hbc hca).appLE (affineOpen a b c hab hbc hca) ⊤
            (affineChartRight_preimage_affineOpen a b c hab hbc hca)))))

/-- The two affine-chart restrictions equalize the parallel arrows `k[t] × k[t] ⇉ ∏ k[t]/(t - p)^2`. -/
theorem sectionsToAffineCharts_equalizes [IsAlgClosed k] [CharP k 2] (a b c : k)
    (hab : a ≠ b) (hbc : b ≠ c) (hca : c ≠ a) :
    sectionsToAffineCharts a b c hab hbc hca ≫ CommRingCat.ofHom (equalizerLeft a b c) =
      sectionsToAffineCharts a b c hab hbc hca ≫
        CommRingCat.ofHom (equalizerRight a b c) := sorry

/-- The square of the principal ideal generated by `X - C (algebraMap k (DualNumber k) a)` in `Polynomial (DualNumber k)`. -/
def doublePointIdealDualNumber (a : k) : Ideal (Polynomial (DualNumber k)) :=
  Ideal.span ({X - C (algebraMap k (DualNumber k) a)} : Set (Polynomial (DualNumber k))) ^ 2

/-- The dual-number coordinate ring of one fat point. -/
abbrev doublePointRingDualNumber (a : k) : Type u :=
  Polynomial (DualNumber k) ⧸ doublePointIdealDualNumber a

/-- The left equalizer leg after base change to the dual numbers. -/
def equalizerLeftDualNumber (a b c : k) :
    Polynomial (DualNumber k) × Polynomial (DualNumber k) →+*
      doublePointRingDualNumber a × doublePointRingDualNumber b × doublePointRingDualNumber c :=
  RingHom.prod
    ((Ideal.Quotient.mk (doublePointIdealDualNumber a)).comp
      (RingHom.fst (Polynomial (DualNumber k)) (Polynomial (DualNumber k))))
    (RingHom.prod
      ((Ideal.Quotient.mk (doublePointIdealDualNumber b)).comp
        (RingHom.fst (Polynomial (DualNumber k)) (Polynomial (DualNumber k))))
      ((Ideal.Quotient.mk (doublePointIdealDualNumber c)).comp
        (RingHom.fst (Polynomial (DualNumber k)) (Polynomial (DualNumber k)))))

/-- The right equalizer leg after base change to the dual numbers. -/
def equalizerRightDualNumber (a b c : k) :
    Polynomial (DualNumber k) × Polynomial (DualNumber k) →+*
      doublePointRingDualNumber a × doublePointRingDualNumber b × doublePointRingDualNumber c :=
  RingHom.prod
    ((Ideal.Quotient.mk (doublePointIdealDualNumber a)).comp
      (RingHom.snd (Polynomial (DualNumber k)) (Polynomial (DualNumber k))))
    (RingHom.prod
      ((Ideal.Quotient.mk (doublePointIdealDualNumber b)).comp
        (RingHom.snd (Polynomial (DualNumber k)) (Polynomial (DualNumber k))))
      ((Ideal.Quotient.mk (doublePointIdealDualNumber c)).comp
        (RingHom.snd (Polynomial (DualNumber k)) (Polynomial (DualNumber k)))))

/-- The product of translations on the two affine charts. -/
def translationProd :
    Polynomial (DualNumber k) × Polynomial (DualNumber k) →ₐ[DualNumber k]
      Polynomial (DualNumber k) × Polynomial (DualNumber k) :=
  AlgHom.prodMap
    (Polynomial.algEquivAevalXAddC (ε : DualNumber k)).toAlgHom
    (Polynomial.algEquivAevalXAddC (ε : DualNumber k)).toAlgHom

/-- In characteristic `2`, translation sends `(t - a)^2` into itself. -/
theorem translation_comp_mk_eq_zero [CharP k 2] (a : k) :
    ∀ p : Polynomial (DualNumber k), p ∈ doublePointIdealDualNumber a →
      ((Ideal.Quotient.mk (doublePointIdealDualNumber a)).comp
          (Polynomial.algEquivAevalXAddC (ε : DualNumber k)).toAlgHom.toRingHom)
        p = 0 := sorry

/-- The automorphism of one fat-point ring induced by `t ↦ t + ε`. -/
def quotientTranslation [CharP k 2] (a : k) :
    doublePointRingDualNumber a →+* doublePointRingDualNumber a :=
  Ideal.Quotient.lift (doublePointIdealDualNumber a)
    ((Ideal.Quotient.mk (doublePointIdealDualNumber a)).comp
      (Polynomial.algEquivAevalXAddC (ε : DualNumber k)).toAlgHom.toRingHom)
    (translation_comp_mk_eq_zero a)

/-- The induced quotient map agrees with translation on representatives. -/
theorem quotientTranslation_comp_mk [CharP k 2] (a : k) :
    (quotientTranslation a).comp (Ideal.Quotient.mk (doublePointIdealDualNumber a)) =
      (Ideal.Quotient.mk (doublePointIdealDualNumber a)).comp
        (Polynomial.algEquivAevalXAddC (ε : DualNumber k)).toAlgHom.toRingHom := sorry

/-- The product of the three descended translations on the fat-point rings. -/
def quotientTranslationProd [CharP k 2] (a b c : k) :
    doublePointRingDualNumber a × doublePointRingDualNumber b × doublePointRingDualNumber c →+*
      doublePointRingDualNumber a × doublePointRingDualNumber b × doublePointRingDualNumber c :=
  RingHom.prodMap (quotientTranslation a)
    (RingHom.prodMap (quotientTranslation b) (quotientTranslation c))

/-- The equalizer of the dual-number parallel pair `A[t] × A[t] ⇉ ∏ A[t]/(t - p)^2`. -/
def equalizerDualNumber (a b c : k) :
    Subring (Polynomial (DualNumber k) × Polynomial (DualNumber k)) :=
  (equalizerLeftDualNumber a b c).eqLocus (equalizerRightDualNumber a b c)

/-- Membership in the dual-number equalizer is equality of the two parallel arrows. -/
theorem mem_equalizerDualNumber (a b c : k)
    {x : Polynomial (DualNumber k) × Polynomial (DualNumber k)} :
    x ∈ equalizerDualNumber a b c ↔
      equalizerLeftDualNumber a b c x = equalizerRightDualNumber a b c x := sorry

/-- In characteristic `2`, translation preserves the dual-number equalizer. -/
theorem translationProd_mem_equalizerDualNumber [CharP k 2] (a b c : k)
    {x : Polynomial (DualNumber k) × Polynomial (DualNumber k)}
    (hx : x ∈ equalizerDualNumber a b c) :
    translationProd x ∈ equalizerDualNumber a b c := sorry

/-- The endomorphism of the dual-number equalizer induced by `t ↦ t + ε`. -/
def translationEqualizer [CharP k 2] (a b c : k) :
    equalizerDualNumber a b c →+* equalizerDualNumber a b c :=
  RingHom.restrict translationProd.toRingHom (equalizerDualNumber a b c)
    (equalizerDualNumber a b c) fun _ hx ↦
      translationProd_mem_equalizerDualNumber a b c hx

/-- The induced equalizer map is restriction of `translationProd`. -/
theorem translationEqualizer_subtype [CharP k 2] (a b c : k) :
    (equalizerDualNumber a b c).subtype.comp (translationEqualizer a b c) =
      translationProd.toRingHom.comp (equalizerDualNumber a b c).subtype := sorry

/-- Base change of the affine line from `k` to `DualNumber k`. -/
def polynomialBaseChange :
    Spec (CommRingCat.of (Polynomial (DualNumber k))) ⟶
      Spec (CommRingCat.of (Polynomial k)) :=
  Spec.map (CommRingCat.ofHom (mapRingHom (algebraMap k (DualNumber k))))

/-- The scheme morphism `Spec(A[t]) ⟶ Spec(A[t])` associated to translation `t ↦ t + ε`. -/
def translationSpec :
    Spec (CommRingCat.of (Polynomial (DualNumber k))) ⟶
      Spec (CommRingCat.of (Polynomial (DualNumber k))) :=
  Spec.map (CommRingCat.ofHom
    (Polynomial.algEquivAevalXAddC (ε : DualNumber k)).toAlgHom.toRingHom)

/-- The pushout `X`, base-changed to the dual numbers, as a scheme over `Spec (DualNumber k)`. -/
def schemeOverDualNumber [IsAlgClosed k] [CharP k 2] (a b c : k)
    (hab : a ≠ b) (hbc : b ≠ c) (hca : c ≠ a) :
    Over (Spec (CommRingCat.of (DualNumber k))) :=
  (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap k (DualNumber k))))).obj
    (schemeOver a b c hab hbc hca)

/-- Restriction of automorphisms of `X` over `k` along `Spec (DualNumber k) ⟶ Spec k`. -/
def autRestriction [IsAlgClosed k] [CharP k 2] (a b c : k)
    (hab : a ≠ b) (hbc : b ≠ c) (hca : c ≠ a) :
    Aut (schemeOver a b c hab hbc hca) →*
      Aut (schemeOverDualNumber a b c hab hbc hca) :=
  (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap k (DualNumber k))))).mapAut
    (schemeOver a b c hab hbc hca)

/-- The left affine chart over `DualNumber k` commutes with the two projections of the
base-change pullback. -/
theorem affineChartLeftDualNumber_comm [IsAlgClosed k] [CharP k 2] (a b c : k)
    (hab : a ≠ b) (hbc : b ≠ c) (hca : c ≠ a) :
    (polynomialBaseChange ≫ affineChartLeft a b c hab hbc hca) ≫
        schemeToSpec a b c hab hbc hca =
      Spec.map (CommRingCat.ofHom (algebraMap (DualNumber k) (Polynomial (DualNumber k)))) ≫
        Spec.map (CommRingCat.ofHom (algebraMap k (DualNumber k))) := sorry

/-- The right affine chart over `DualNumber k` commutes with the two projections of the
base-change pullback. -/
theorem affineChartRightDualNumber_comm [IsAlgClosed k] [CharP k 2] (a b c : k)
    (hab : a ≠ b) (hbc : b ≠ c) (hca : c ≠ a) :
    (polynomialBaseChange ≫ affineChartRight a b c hab hbc hca) ≫
        schemeToSpec a b c hab hbc hca =
      Spec.map (CommRingCat.ofHom (algebraMap (DualNumber k) (Polynomial (DualNumber k)))) ≫
        Spec.map (CommRingCat.ofHom (algebraMap k (DualNumber k))) := sorry

/-- The left affine chart of `X` after base change to the dual numbers. -/
def affineChartLeftDualNumber [IsAlgClosed k] [CharP k 2] (a b c : k)
    (hab : a ≠ b) (hbc : b ≠ c) (hca : c ≠ a) :
    Spec (CommRingCat.of (Polynomial (DualNumber k))) ⟶
      (schemeOverDualNumber a b c hab hbc hca).left :=
  pullback.lift
    (polynomialBaseChange ≫ affineChartLeft a b c hab hbc hca)
    (Spec.map (CommRingCat.ofHom (algebraMap (DualNumber k) (Polynomial (DualNumber k)))))
    (affineChartLeftDualNumber_comm a b c hab hbc hca)

/-- The right affine chart of `X` after base change to the dual numbers. -/
def affineChartRightDualNumber [IsAlgClosed k] [CharP k 2] (a b c : k)
    (hab : a ≠ b) (hbc : b ≠ c) (hca : c ≠ a) :
    Spec (CommRingCat.of (Polynomial (DualNumber k))) ⟶
      (schemeOverDualNumber a b c hab hbc hca).left :=
  pullback.lift
    (polynomialBaseChange ≫ affineChartRight a b c hab hbc hca)
    (Spec.map (CommRingCat.ofHom (algebraMap (DualNumber k) (Polynomial (DualNumber k)))))
    (affineChartRightDualNumber_comm a b c hab hbc hca)

/-- Sections on the affine open form the equalizer of the two fat-point restriction maps. -/
theorem sectionsToAffineCharts_isEqualizer [IsAlgClosed k] [CharP k 2] (a b c : k)
    (hab : a ≠ b) (hbc : b ≠ c) (hca : c ≠ a) :
    IsEqualizer (sectionsToAffineCharts a b c hab hbc hca)
      (CommRingCat.ofHom (equalizerLeft a b c))
      (CommRingCat.ofHom (equalizerRight a b c))
      (sectionsToAffineCharts_equalizes a b c hab hbc hca) := sorry

/-- Simultaneous dual-number translation on both affine branches extends to an automorphism of the curve. -/
theorem existsAutOverDualNumber [IsAlgClosed k] [CharP k 2] (a b c : k)
    (hab : a ≠ b) (hbc : b ≠ c) (hca : c ≠ a) :
    ∃ φ : Aut (schemeOverDualNumber a b c hab hbc hca),
      affineChartLeftDualNumber a b c hab hbc hca ≫ φ.hom.left =
          translationSpec ≫ affineChartLeftDualNumber a b c hab hbc hca ∧
        affineChartRightDualNumber a b c hab hbc hca ≫ φ.hom.left =
          translationSpec ≫ affineChartRightDualNumber a b c hab hbc hca := sorry

/-- The automorphism group of the glued curve over its algebraically closed base field is finite. -/
theorem autFinite [IsAlgClosed k] [CharP k 2] (a b c : k)
    (hab : a ≠ b) (hbc : b ≠ c) (hca : c ≠ a) :
    Finite (Aut (schemeOver a b c hab hbc hca)) := sorry

attribute [instance] autFinite

/-- Base change to the dual numbers does not surject onto the automorphisms of the glued curve. -/
theorem autRestriction_not_surjective [IsAlgClosed k] [CharP k 2] (a b c : k)
    (hab : a ≠ b) (hbc : b ≠ c) (hca : c ≠ a) :
    ¬ Function.Surjective (autRestriction a b c hab hbc hca) := sorry

/-- Dual-number translation is not the identity on the polynomial ring. -/
theorem translation_ne_id [CharP k 2] :
    (Polynomial.algEquivAevalXAddC (ε : DualNumber k)).toAlgHom ≠
      AlgHom.id (DualNumber k) (Polynomial (DualNumber k)) := sorry

/-- Dual-number translation is an involution in characteristic two. -/
theorem translation_comp_self [CharP k 2] :
    (Polynomial.algEquivAevalXAddC (ε : DualNumber k)).toAlgHom.comp
        (Polynomial.algEquivAevalXAddC (ε : DualNumber k)).toAlgHom =
      AlgHom.id (DualNumber k) (Polynomial (DualNumber k)) := sorry

/-- Simultaneous translation on the three double-point coordinate rings is an involution. -/
theorem quotientTranslationProd_comp_self [CharP k 2] (a b c : k) :
    (quotientTranslationProd a b c).comp (quotientTranslationProd a b c) =
      RingHom.id (doublePointRingDualNumber a × doublePointRingDualNumber b ×
        doublePointRingDualNumber c) := sorry

/-- Simultaneous translation commutes with restriction from the first affine branch. -/
theorem equalizerLeftDualNumber_comp_translationProd [CharP k 2] (a b c : k) :
    (equalizerLeftDualNumber a b c).comp translationProd.toRingHom =
      (quotientTranslationProd a b c).comp (equalizerLeftDualNumber a b c) := sorry

/-- Simultaneous translation commutes with restriction from the second affine branch. -/
theorem equalizerRightDualNumber_comp_translationProd [CharP k 2] (a b c : k) :
    (equalizerRightDualNumber a b c).comp translationProd.toRingHom =
      (quotientTranslationProd a b c).comp (equalizerRightDualNumber a b c) := sorry

/-- Translation restricted to the equalizer ring is an involution. -/
theorem translationEqualizer_comp_self [CharP k 2] (a b c : k) :
    (translationEqualizer a b c).comp (translationEqualizer a b c) =
      RingHom.id (equalizerDualNumber a b c) := sorry

/-- Translation restricted to the equalizer ring is not the identity. -/
theorem translationEqualizer_ne_id [CharP k 2] (a b c : k) :
    translationEqualizer a b c ≠ RingHom.id (equalizerDualNumber a b c) := sorry

/-- The automorphisms of the curve glued along three double points are represented by a
non-reduced scheme carrying a universal automorphism family. -/
theorem existsNonreducedAutScheme [IsAlgClosed k] [CharP k 2] (a b c : k)
    (hab : a ≠ b) (hbc : b ≠ c) (hca : c ≠ a) :
    ∃ (G : SchemeOverField k)
      (α : Aut ((Over.pullback G.hom).obj (schemeOver a b c hab hbc hca))),
      SchemeOverField.Automorphism.IsUniversalFamily (schemeOver a b c hab hbc hca) α ∧
        ¬ IsReduced G.left := sorry

end AlgebraicGeometry.FatPointPushout
