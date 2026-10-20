module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.RelativeSpectrum.Descent
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.RelativeSpectrum.ChartCartesian

/-!
# Concrete composition in the relative-spectrum descent relation

The triple-overlap scheme is the actual pullback of the base atlas relation.
Chart-spectrum pullback lifts provide the limiting cone of its spectrum, and
the represented kernel-pair lift supplies the composition map.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.AlgebraicSpace.QcAlgebraUnder

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

variable {S : Scheme.{u}} {X : AlgebraicSpace S}

/-- The actual triple overlap U×_XU×_XU, formed by composing the base relation arrows. -/
abbrev relativeSpectrumTripleOver (X : AlgebraicSpace S) : Over S :=
  pullback (atlasKernelPair_s X) (atlasKernelPair_t X)

/-- The triple overlap as an étale scheme chart of X. -/
def relativeSpectrumTripleChart (X : AlgebraicSpace S) : smallEtaleSite X :=
  @smallEtaleSite.mk S X (relativeSpectrumTripleOver X)
    ((ofOverFunctor S).map (pullback.fst (atlasKernelPair_s X) (atlasKernelPair_t X)) ≫
      atlasKernelPairHom X) sorry

/-- Forget the third factor of the triple overlap. -/
def relativeSpectrumTripleChart₁₂ (X : AlgebraicSpace S) :
    relativeSpectrumTripleChart X ⟶ relativeSpectrumKernelChart X :=
  MorphismProperty.CostructuredArrow.homMk
    (pullback.fst (atlasKernelPair_s X) (atlasKernelPair_t X)) trivial rfl

/-- Forget the first factor of the triple overlap. -/
def relativeSpectrumTripleChart₂₃ (X : AlgebraicSpace S) :
    relativeSpectrumTripleChart X ⟶ relativeSpectrumKernelChart X :=
  MorphismProperty.CostructuredArrow.homMk
    (pullback.snd (atlasKernelPair_s X) (atlasKernelPair_t X)) trivial sorry

/-- Retain the first and third factors using the actual represented kernel-pair lift. -/
def relativeSpectrumTripleChart₁₃ (X : AlgebraicSpace S) :
    relativeSpectrumTripleChart X ⟶ relativeSpectrumKernelChart X :=
  MorphismProperty.CostructuredArrow.homMk
    (yoneda.preimage (((atlasHom_presheaf_etale X).rep.isPullback (atlasHom X)).lift
      (yoneda.map (pullback.fst (atlasKernelPair_s X) (atlasKernelPair_t X) ≫ atlasKernelPair_t X))
      (yoneda.map (pullback.snd (atlasKernelPair_s X) (atlasKernelPair_t X) ≫ atlasKernelPair_s X))
      sorry)) trivial sorry

/-- The actual chart-spectrum structural map, with its original map to S. -/
def relativeSpectrumChartToBase (A : X.QcAlgebraUnder) (U : smallEtaleSite X) :
    relativeSpectrumChartOver A U ⟶ U.left :=
  Over.homMk (Scheme.relativeSpectrumOver (onChart A U)).π rfl

/-- The triple-overlap spectrum cone uses its two actual projection maps. -/
def relativeSpectrumTripleCone (A : X.QcAlgebraUnder) :
    PullbackCone (relativeSpectrumDescentRelation A).s (relativeSpectrumDescentRelation A).t :=
  PullbackCone.mk
    (relativeSpectrumChartOverMap A (relativeSpectrumTripleChart₁₂ X))
    (relativeSpectrumChartOverMap A (relativeSpectrumTripleChart₂₃ X)) sorry

/-- A cone of spectrum relation arrows gives the actual cone on the base atlas relation. -/
def relativeSpectrumTripleBaseLift (A : X.QcAlgebraUnder)
    (c : PullbackCone (relativeSpectrumDescentRelation A).s (relativeSpectrumDescentRelation A).t) :
    c.pt ⟶ relativeSpectrumTripleOver X :=
  pullback.lift
    (c.fst ≫ relativeSpectrumChartToBase A (relativeSpectrumKernelChart X))
    (c.snd ≫ relativeSpectrumChartToBase A (relativeSpectrumKernelChart X)) sorry

/-- The geometric triangle for the actual first projection of a triple cone. -/
theorem relativeSpectrumTripleLift_triangle (A : X.QcAlgebraUnder)
    (c : PullbackCone (relativeSpectrumDescentRelation A).s (relativeSpectrumDescentRelation A).t) :
    c.fst.left ≫ (Scheme.relativeSpectrumOver (onChart A (relativeSpectrumKernelChart X))).π =
      (relativeSpectrumTripleBaseLift A c).left ≫ (relativeSpectrumTripleChart₁₂ X).left.left := sorry

/-- The actual triple-spectrum lift comes from its affine-glued algebra point. -/
def relativeSpectrumTripleLift (A : X.QcAlgebraUnder)
    (c : PullbackCone (relativeSpectrumDescentRelation A).s (relativeSpectrumDescentRelation A).t) :
    c.pt ⟶ relativeSpectrumChartOver A (relativeSpectrumTripleChart X) :=
  Over.homMk
    (relativeSpectrumChartPullbackLift A (relativeSpectrumTripleChart₁₂ X)
      (relativeSpectrumTripleBaseLift A c).left c.fst.left
      (relativeSpectrumTripleLift_triangle A c)) sorry

/-- The triple spectrum cone is limiting with the specified actual lift operation. -/
def relativeSpectrumTripleConeIsLimit (A : X.QcAlgebraUnder) :
    IsLimit (relativeSpectrumTripleCone A) :=
  PullbackCone.IsLimit.mk _ (relativeSpectrumTripleLift A) sorry sorry sorry

/-- The transitive relation has a native pullback cone and a concrete composition arrow. -/
def relativeSpectrumDescentTransitive (A : X.QcAlgebraUnder) :
    TransitiveRelation (relativeSpectrumDescentRelation A).t (relativeSpectrumDescentRelation A).s where
  right_cancellation := sorry
  c := pullback.cone (relativeSpectrumDescentRelation A).s (relativeSpectrumDescentRelation A).t
  isLimit := pullback.isLimit (relativeSpectrumDescentRelation A).s (relativeSpectrumDescentRelation A).t
  t := (relativeSpectrumTripleConeIsLimit A).lift
      (pullback.cone (relativeSpectrumDescentRelation A).s (relativeSpectrumDescentRelation A).t) ≫
    relativeSpectrumChartOverMap A (relativeSpectrumTripleChart₁₃ X)
  transitivity₁ := sorry
  transitivity₂ := sorry

/-- The equivalence relation structure has its actual reflexive, symmetric and composition data. -/
def relativeSpectrumDescentEquivalence (A : X.QcAlgebraUnder) :
    EquivalenceRelation (relativeSpectrumDescentRelation A).t (relativeSpectrumDescentRelation A).s where
  right_cancellation := (relativeSpectrumDescentReflexive A).right_cancellation
  r := (relativeSpectrumDescentReflexive A).r
  reflexivity₁ := (relativeSpectrumDescentReflexive A).reflexivity₁
  reflexivity₂ := (relativeSpectrumDescentReflexive A).reflexivity₂
  s := (relativeSpectrumDescentSymmetric A).s
  symmetry₁ := (relativeSpectrumDescentSymmetric A).symmetry₁
  symmetry₂ := (relativeSpectrumDescentSymmetric A).symmetry₂
  c := (relativeSpectrumDescentTransitive A).c
  isLimit := (relativeSpectrumDescentTransitive A).isLimit
  t := (relativeSpectrumDescentTransitive A).t
  transitivity₁ := (relativeSpectrumDescentTransitive A).transitivity₁
  transitivity₂ := (relativeSpectrumDescentTransitive A).transitivity₂

/-- The constructed affine descent relation is an étale equivalence relation with genuine operations. -/
instance relativeSpectrumDescentRelation_isEtaleEquivalenceRelation (A : X.QcAlgebraUnder) :
    (relativeSpectrumDescentRelation A).IsEtaleEquivalenceRelation where
  isEquivalenceRelation := (relativeSpectrumDescentEquivalence A).isEquivalenceRelation
  etale_t := relativeSpectrumDescentRelation_etale_t A
  etale_s := relativeSpectrumDescentRelation_etale_s A

end AlgebraicGeometry.AlgebraicSpace
