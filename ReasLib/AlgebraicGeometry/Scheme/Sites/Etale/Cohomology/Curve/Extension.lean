/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Sites.AbelianSheaf.Torsion.Primary
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Cohomology.Pullback
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Constructible
public import ReasLib.AlgebraicGeometry.Scheme.OverField
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FiniteType
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.Topology.KrullDimension

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open CategoryTheory.Sheaf

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Etale.CurveCohomology

variable {k : Type u} [Field k]
variable [∀ Y : Scheme.{u}, HasSheafify Y.smallEtaleTopology AddCommGrpCat.{u}]
variable [∀ Y : Scheme.{u}, HasExt.{u} (Sheaf Y.smallEtaleTopology AddCommGrpCat.{u})]
variable [∀ (Y : Scheme.{u}) (U : Y.Etale),
  HasWeakSheafify (Y.smallEtaleTopology.over U) AddCommGrpCat.{u}]
variable [∀ {S T : Scheme.{u}} (f : T ⟶ S),
  ((smallEtalePullback f).sheafPushforwardContinuous AddCommGrpCat.{u}
    S.smallEtaleTopology T.smallEtaleTopology).IsRightAdjoint]

/-- Global étale cohomology vanishes in every degree greater than two. -/
def Vanishing (X : SchemeOverField k)
    (F : Sheaf X.left.smallEtaleTopology AddCommGrpCat.{u}) : Prop :=
  ∀ degree : ℕ, 2 < degree → IsZero (F.H' degree (globalEtale X.left))

/-- Global étale cohomology on an affine scheme vanishes in degrees greater than one. -/
def AffineVanishing (X : SchemeOverField k)
    (F : Sheaf X.left.smallEtaleTopology AddCommGrpCat.{u}) : Prop :=
  IsAffine X.left → ∀ degree : ℕ, 1 < degree → IsZero (F.H' degree (globalEtale X.left))

/-- In positive characteristic `p`, locally `p`-power torsion coefficients have vanishing
global étale cohomology in degrees greater than one. -/
def PrimaryVanishing (X : SchemeOverField k)
    (F : Sheaf X.left.smallEtaleTopology AddCommGrpCat.{u}) : Prop :=
  ∀ characteristic : ℕ, 0 < characteristic → ringChar k = characteristic →
    IsLocallyPPowerTorsion characteristic F →
      ∀ degree : ℕ, 1 < degree → IsZero (F.H' degree (globalEtale X.left))

/-- Constructible coefficients locally of torsion prime to the field characteristic
have finite global étale cohomology in every degree. Constructibility uses the canonical
inverse image and finite locally constant abelian sheaves on each stratum. -/
def PrimeToCharFiniteness (X : SchemeOverField k)
    (F : Sheaf X.left.smallEtaleTopology AddCommGrpCat.{u}) : Prop :=
  IsConstructibleEtale
    (fun {Y} inclusion G ↦
      ((smallEtalePullback inclusion).sheafPullback AddCommGrpCat.{u}
        X.left.smallEtaleTopology Y.smallEtaleTopology).obj G)
    (fun {Y} G ↦ IsFiniteLocallyConstantAddCommGrp G) F →
      IsLocallyPrimeToCharTorsion k F →
        ∀ degree : ℕ, Finite (F.H' degree (globalEtale X.left))

/-- Constructible coefficients on a proper scheme have finite global étale cohomology
in every degree. Constructibility uses canonical inverse images and finite locally
constant abelian sheaves. -/
def ProperFiniteness (X : SchemeOverField k)
    (F : Sheaf X.left.smallEtaleTopology AddCommGrpCat.{u}) : Prop :=
  IsProper X.hom →
    IsConstructibleEtale
      (fun {Y} inclusion G ↦
        ((smallEtalePullback inclusion).sheafPullback AddCommGrpCat.{u}
          X.left.smallEtaleTopology Y.smallEtaleTopology).obj G)
      (fun {Y} G ↦ IsFiniteLocallyConstantAddCommGrp G) F →
        ∀ degree : ℕ, Finite (F.H' degree (globalEtale X.left))

/-- Étale cohomology with locally prime-to-characteristic torsion coefficients is
invariant under every extension of algebraically closed ground fields, via the canonical
pullback map for any cartesian base-change square. -/
def PrimeToCharBaseChange (X : SchemeOverField k)
    (F : Sheaf X.left.smallEtaleTopology AddCommGrpCat.{u}) : Prop :=
  IsLocallyPrimeToCharTorsion k F →
    ∀ {extensionField : Type u} [Field extensionField] [IsAlgClosed extensionField]
      [Algebra k extensionField] (Y : SchemeOverField extensionField)
      (projection : Y.left ⟶ X.left),
      IsPullback projection Y.hom X.hom
        (Spec.map (CommRingCat.ofHom (algebraMap k extensionField))) →
          ∀ degree : ℕ, IsIso (cohomologyPullback projection F degree)

/-- On a proper scheme, étale cohomology is invariant under every extension of
algebraically closed ground fields, via the canonical pullback map for any cartesian
base-change square. -/
def ProperBaseChange (X : SchemeOverField k)
    (F : Sheaf X.left.smallEtaleTopology AddCommGrpCat.{u}) : Prop :=
  IsProper X.hom →
    ∀ {extensionField : Type u} [Field extensionField] [IsAlgClosed extensionField]
      [Algebra k extensionField] (Y : SchemeOverField extensionField)
      (projection : Y.left ⟶ X.left),
      IsPullback projection Y.hom X.hom
        (Spec.map (CommRingCat.ofHom (algebraMap k extensionField))) →
          ∀ degree : ℕ, IsIso (cohomologyPullback projection F degree)

/-- Canonical restriction of degree-two étale cohomology to every open subscheme
is an epimorphism of abelian groups. -/
def OpenRestrictionSurjective (X : SchemeOverField k)
    (F : Sheaf X.left.smallEtaleTopology AddCommGrpCat.{u}) : Prop :=
  ∀ {U : Scheme.{u}} (inclusion : U ⟶ X.left) [IsOpenImmersion inclusion],
    Epi (cohomologyPullback inclusion F 2)

/-- The simultaneous vanishing, affine vanishing, positive-characteristic primary
vanishing, prime-to-characteristic finiteness, proper finiteness, prime-to-characteristic
base change, proper base change, and surjective open restriction conditions for an
abelian sheaf on a scheme over a field. -/
def Properties (X : SchemeOverField k)
    (F : Sheaf X.left.smallEtaleTopology AddCommGrpCat.{u}) : Prop :=
  Vanishing X F ∧ AffineVanishing X F ∧ PrimaryVanishing X F ∧
    PrimeToCharFiniteness X F ∧ ProperFiniteness X F ∧ PrimeToCharBaseChange X F ∧
      ProperBaseChange X F ∧ OpenRestrictionSurjective X F

end AlgebraicGeometry.Scheme.Etale.CurveCohomology

open AlgebraicGeometry.Scheme.Etale.CurveCohomology

/-- On a separated finite-type scheme of dimension at most one over an algebraically
closed field, the eight étale cohomological properties of locally torsion abelian sheaves
are closed under short exact extensions. -/
theorem AlgebraicGeometry.Scheme.Etale.CurveCohomology.Properties.ofShortExact
    {k : Type u} [Field k] [IsAlgClosed k]
    [∀ Y : Scheme.{u}, HasSheafify Y.smallEtaleTopology AddCommGrpCat.{u}]
    [∀ Y : Scheme.{u}, HasExt.{u} (Sheaf Y.smallEtaleTopology AddCommGrpCat.{u})]
    [∀ (Y : Scheme.{u}) (U : Y.Etale),
      HasWeakSheafify (Y.smallEtaleTopology.over U) AddCommGrpCat.{u}]
    [∀ {S T : Scheme.{u}} (f : T ⟶ S),
      ((smallEtalePullback f).sheafPushforwardContinuous AddCommGrpCat.{u}
        S.smallEtaleTopology T.smallEtaleTopology).IsRightAdjoint]
    (X : SchemeOverField k) [Scheme.Hom.FiniteType X.hom] [IsSeparated X.hom]
    (h_dim : topologicalKrullDim X.left ≤ 1)
    (sequence : ShortComplex (Sheaf X.left.smallEtaleTopology AddCommGrpCat.{u}))
    (h_exact : sequence.ShortExact)
    (h_left_torsion : IsLocallyTorsion sequence.X₁)
    (h_middle_torsion : IsLocallyTorsion sequence.X₂)
    (h_right_torsion : IsLocallyTorsion sequence.X₃)
    (h_left : Properties X sequence.X₁) (h_right : Properties X sequence.X₃) :
    Properties X sequence.X₂ := sorry
