/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.RelativeProj.Functor
public import Mathlib.AlgebraicGeometry.Gluing
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# A common degree for a quasi-compact test scheme

Pull back the complete positive-degree cover, choose an actual finite subcover,
and take the product of its degrees. The canonical degree transitions put every
selected piece in that single common chart. No quasi-compactness assumption is
placed on the base or on the whole relative projective spectrum.
-/

@[expose] public section

open CategoryTheory Opposite
open scoped BigOperators AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.RelativeProjFunctor

variable {S : Scheme.{u}} {𝒜 : SheafOfModules.RingedSite.GradedAlgebraSheaf.{u, u} S.sheaf}

/-- Representability of each specified positive-degree chart. -/
instance degreeRepresentable (F : RelativeProjFunctor S 𝒜) (d : {n : ℕ // 1 ≤ n}) :
    (F.degreeFunctor d).toFunctor.IsRepresentable := F.degreeFunctor_isRepresentable d

/-- The scheme representing a positive-degree chart. -/
def degreeScheme (F : RelativeProjFunctor S 𝒜) (d : {n : ℕ // 1 ≤ n}) : Scheme.{u} :=
  (F.degreeFunctor d).toFunctor.reprX

/-- The represented chart inclusion evaluated at its actual universal point. -/
def degreeMap [F : RelativeProjFunctor S 𝒜] (d : {n : ℕ // 1 ≤ n}) :
    F.degreeScheme d ⟶ F.toFunctor.reprX :=
  (F.toFunctor.reprW.app (op (F.degreeScheme d))).inv
    ((F.degreeToFunctor d).app (op (F.degreeScheme d)) (F.degreeFunctor d).toFunctor.reprx)

/-- The represented chart inclusions are open immersions. -/
instance degreeMap_isOpenImmersion [F : RelativeProjFunctor S 𝒜]
    (d : {n : ℕ // 1 ≤ n}) : IsOpenImmersion (degreeMap (F := F) d) := sorry

/-- A chart transition is represented by the explicit tensor/restriction
transition on the universal point of the source chart. -/
def degreeTransitionMap (F : RelativeProjFunctor S 𝒜)
    (d e : {n : ℕ // 1 ≤ n}) (h : d.1 ∣ e.1) : F.degreeScheme d ⟶ F.degreeScheme e :=
  ((F.degreeFunctor e).toFunctor.reprW.app (op (F.degreeScheme d))).inv
    (((F.degreeAssociated d).transition (F.degreeAssociated e) h).app
      (op (F.degreeScheme d)) (F.degreeFunctor d).toFunctor.reprx)

/-- Canonical degree transitions commute with the chart inclusions. -/
theorem degreeTransitionMap_comp [F : RelativeProjFunctor S 𝒜]
    (d e : {n : ℕ // 1 ≤ n}) (h : d.1 ∣ e.1) :
    degreeTransitionMap F d e h ≫ degreeMap (F := F) e = degreeMap (F := F) d := sorry

/-- A degree chart lies in every canonically divisible degree chart. -/
theorem degreeMap_range_mono [F : RelativeProjFunctor S 𝒜]
    (d e : {n : ℕ // 1 ≤ n}) (h : d.1 ∣ e.1) :
    Set.range (degreeMap (F := F) d) ⊆ Set.range (degreeMap (F := F) e) := sorry

/-- The complete positive-degree cover of the representing scheme. -/
def degreeCover [F : RelativeProjFunctor S 𝒜] :
    Scheme.OpenCover.{0} F.toFunctor.reprX :=
  Scheme.Cover.mkOfCovers {n : ℕ // 1 ≤ n} (degreeScheme F)
    (degreeMap (F := F)) sorry (degreeMap_isOpenImmersion (F := F))

/-- The whole degree cover pulled back to the test scheme. -/
def testCover [F : RelativeProjFunctor S 𝒜] {T : Scheme.{u}}
    (φ : T ⟶ F.toFunctor.reprX) : Scheme.OpenCover T :=
  (degreeCover (F := F)).pullback₁ φ

/-- A genuine finite subcover of the test scheme. -/
def finiteTestCover [F : RelativeProjFunctor S 𝒜] {T : Scheme.{u}} [CompactSpace T]
    (φ : T ⟶ F.toFunctor.reprX) : Scheme.OpenCover T :=
  (testCover φ).finiteSubcover

/-- The finite subcover has its canonical finite index set. -/
instance finiteTestCover_fintype [F : RelativeProjFunctor S 𝒜]
    {T : Scheme.{u}} [CompactSpace T] (φ : T ⟶ F.toFunctor.reprX) :
    Fintype (finiteTestCover φ).I₀ :=
  inferInstanceAs (Fintype (testCover φ).finiteSubcover.I₀)

/-- The original positive degree attached to one selected cover piece. -/
def finiteTestDegree [F : RelativeProjFunctor S 𝒜] {T : Scheme.{u}} [CompactSpace T]
    (φ : T ⟶ F.toFunctor.reprX) (i : (finiteTestCover φ).I₀) : {n : ℕ // 1 ≤ n} :=
  (testCover φ).idx i.1

/-- Product of the finitely many selected positive degrees; the empty product is1. -/
def commonDegreeNat [F : RelativeProjFunctor S 𝒜] {T : Scheme.{u}} [CompactSpace T]
    (φ : T ⟶ F.toFunctor.reprX) : ℕ :=
  ∏ i : (finiteTestCover φ).I₀, (finiteTestDegree φ i).1

/-- The product of the selected positive degrees is positive, also for an empty test scheme. -/
theorem commonDegreeNat_positive [F : RelativeProjFunctor S 𝒜]
    {T : Scheme.{u}} [CompactSpace T] (φ : T ⟶ F.toFunctor.reprX) :
    1 ≤ commonDegreeNat φ := sorry

/-- Each selected degree divides their product. -/
theorem finiteTestDegree_dvd [F : RelativeProjFunctor S 𝒜]
    {T : Scheme.{u}} [CompactSpace T] (φ : T ⟶ F.toFunctor.reprX)
    (i : (finiteTestCover φ).I₀) : (finiteTestDegree φ i).1 ∣ commonDegreeNat φ := sorry

/-- A common positive degree for the actual finite pullback cover. -/
def commonDegree [F : RelativeProjFunctor S 𝒜] {T : Scheme.{u}} [CompactSpace T]
    (φ : T ⟶ F.toFunctor.reprX) : {n : ℕ // 1 ≤ n} :=
  ⟨commonDegreeNat φ, commonDegreeNat_positive φ⟩

/-- Every point of the test scheme maps into its finite-cover common-degree chart. -/
theorem range_subset_commonDegree [F : RelativeProjFunctor S 𝒜]
    {T : Scheme.{u}} [CompactSpace T] (φ : T ⟶ F.toFunctor.reprX) :
    Set.range φ ⊆ Set.range (degreeMap (F := F) (commonDegree φ)) := sorry

/-- The full test morphism lifted to the canonically chosen common-degree chart. -/
def toCommonDegree [F : RelativeProjFunctor S 𝒜]
    {T : Scheme.{u}} [CompactSpace T] (φ : T ⟶ F.toFunctor.reprX) :
    T ⟶ F.degreeScheme (commonDegree φ) :=
  IsOpenImmersion.lift (degreeMap (F := F) (commonDegree φ)) φ
    (range_subset_commonDegree φ)

/-- The common-degree lift recovers the original morphism into the relative Proj. -/
theorem toCommonDegree_comp [F : RelativeProjFunctor S 𝒜]
    {T : Scheme.{u}} [CompactSpace T] (φ : T ⟶ F.toFunctor.reprX) :
    toCommonDegree φ ≫ degreeMap (F := F) (commonDegree φ) = φ := sorry

end AlgebraicGeometry.RelativeProjFunctor
