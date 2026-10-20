/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExactSequences
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.HasExt
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
public import Mathlib.Topology.Sheaves.Abelian
public import Mathlib.Topology.Sheaves.Functors
public import ReasLib.CategoryTheory.Sites.AbelianSheaf.Grothendieck
public import ReasLib.Topology.Category.TopCat.Subset
public import ReasLib.Topology.Sheaf.Cohomology.ClosedEmbedding
public import ReasLib.Topology.Sheaf.GlobalSections.ConstantInteger
public import ReasLib.Topology.Sheaves.Abelian.Sheafification

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopCat TopologicalSpace Opposite

universe u

noncomputable section

namespace TopCat.Sheaf.ClosedUnion

variable {X : TopCat.{u}}

/-- The inclusion of subspaces induced by an inclusion of subsets. -/
def subsetInclusionOfLe {A B : Set X} (h : A ⊆ B) :
    subsetSpace A ⟶ subsetSpace B :=
  ofHom (ContinuousMap.inclusion h)

/-- Subspace inclusion of `A ⊆ B` followed by the inclusion of `B` into `X` is the inclusion of
`A`. -/
theorem subsetInclusionOfLe_comp_subsetInclusion {A B : Set X} (h : A ⊆ B) :
    subsetInclusionOfLe h ≫ subsetInclusion B = subsetInclusion A :=
  sorry

/-- Direct image of the constant integer sheaf along a subset inclusion. -/
abbrev integerPushforward (S : Set X) : X.Sheaf AddCommGrpCat.{u} :=
  (pushforward AddCommGrpCat.{u} (subsetInclusion S)).obj
    (constantIntegerSheaf (subsetSpace S))

/-- The canonical map from the constant integer sheaf on the target to the pushforward of the
constant integer sheaf on the source, determined by the distinguished global section `1`. -/
def toPushforward {Y : TopCat.{u}} (f : Y ⟶ X) :
    constantIntegerSheaf X ⟶
      (pushforward AddCommGrpCat.{u} f).obj (constantIntegerSheaf Y) :=
  (constantIntegerHomEquivTopSection X
      ((pushforward AddCommGrpCat.{u} f).obj (constantIntegerSheaf Y))).symm
    (CategoryTheory.Sheaf.constantIntegerSheafOne
      (Opens.grothendieckTopology Y) (op (⊤ : Opens Y)))

/-- `toPushforward f` is the unique morphism sending the distinguished global section `1` on `X`
to the distinguished global section `1` of the pushforward. -/
theorem toPushforward_app_top {Y : TopCat.{u}} (f : Y ⟶ X) :
    constantIntegerHomEquivTopSection X
        ((pushforward AddCommGrpCat.{u} f).obj (constantIntegerSheaf Y))
        (toPushforward f) =
      CategoryTheory.Sheaf.constantIntegerSheafOne
        (Opens.grothendieckTopology Y) (op (⊤ : Opens Y)) :=
  sorry

/-- The first map of the closed-union sequence, sending the constant integer sheaf on `X` into
the biproduct of the two closed-subset pushforwards. -/
def toSum (Y Z : Set X) :
    constantIntegerSheaf X ⟶ integerPushforward Y ⊞ integerPushforward Z :=
  biprod.lift (toPushforward (subsetInclusion Y)) (toPushforward (subsetInclusion Z))

/-- The first projection of `toSum` is the unit map toward `Y`. -/
theorem toSum_fst (Y Z : Set X) :
    toSum Y Z ≫ biprod.fst = toPushforward (subsetInclusion Y) :=
  sorry

/-- The second projection of `toSum` is the unit map toward `Z`. -/
theorem toSum_snd (Y Z : Set X) :
    toSum Y Z ≫ biprod.snd = toPushforward (subsetInclusion Z) :=
  sorry

/-- Restriction of pushed-forward constant integer sheaves along an inclusion of subsets. -/
def restrictIntegerPushforward {A B : Set X} (h : A ⊆ B) :
    integerPushforward B ⟶ integerPushforward A :=
  (pushforward AddCommGrpCat.{u} (subsetInclusion B)).map
    (toPushforward (subsetInclusionOfLe h))

/-- The second map of the closed-union sequence, the difference of the two restrictions to
`Y ∩ Z`. -/
def fromSum (Y Z : Set X) :
    integerPushforward Y ⊞ integerPushforward Z ⟶ integerPushforward (Y ∩ Z) :=
  biprod.desc (restrictIntegerPushforward (Set.inter_subset_left : Y ∩ Z ⊆ Y))
    (-restrictIntegerPushforward (Set.inter_subset_right : Y ∩ Z ⊆ Z))

/-- Precomposing `fromSum` with the first inclusion is restriction from `Y` to `Y ∩ Z`. -/
theorem fromSum_inl (Y Z : Set X) :
    biprod.inl ≫ fromSum Y Z =
      restrictIntegerPushforward (Set.inter_subset_left : Y ∩ Z ⊆ Y) :=
  sorry

/-- Precomposing `fromSum` with the second inclusion is minus restriction from `Z` to `Y ∩ Z`. -/
theorem fromSum_inr (Y Z : Set X) :
    biprod.inr ≫ fromSum Y Z =
      -restrictIntegerPushforward (Set.inter_subset_right : Y ∩ Z ⊆ Z) :=
  sorry

/-- The two maps of the closed-union sequence compose to zero. -/
theorem toSum_comp_fromSum (Y Z : Set X) :
    toSum Y Z ≫ fromSum Y Z = 0 :=
  sorry

/-- The short complex of abelian sheaves on `X` associated to a pair of subsets. -/
def shortComplex (Y Z : Set X) : ShortComplex (X.Sheaf AddCommGrpCat.{u}) :=
  ShortComplex.mk (toSum Y Z) (fromSum Y Z) (toSum_comp_fromSum Y Z)

/-- If `X = Y ∪ Z` with `Y` and `Z` closed, then the sequence
`0 ⟶ constantIntegerSheaf X ⟶ i_* constantIntegerSheaf Y ⊞ j_* constantIntegerSheaf Z ⟶
k_* constantIntegerSheaf (Y ∩ Z) ⟶ 0` of abelian sheaves on `X` is short exact, where
`i`, `j`, and `k` are the subset inclusions of `Y`, `Z`, and `Y ∩ Z`. -/
theorem shortExact {Y Z : Set X} (hY : IsClosed Y) (hZ : IsClosed Z)
    (hcover : Y ∪ Z = Set.univ) :
    (shortComplex Y Z).ShortExact :=
  sorry

/-- Integer cohomology of a space in degree `n`, as objectwise cohomology of the constant
integer sheaf on the top open. -/
abbrev integerCohomology (Y : TopCat.{u}) (n : ℕ)
    [HasExt.{u} (Y.Sheaf AddCommGrpCat.{u})] : AddCommGrpCat.{u} :=
  (constantIntegerSheaf Y).H' n (⊤ : Opens Y)

/-- The canonical comparison from cohomology of a subset pushforward on `X` to integer
cohomology of the subset. -/
def integerPushforward_cohomologyMap (S : Set X)
    [HasExt.{u} (X.Sheaf AddCommGrpCat.{u})]
    [HasExt.{u} ((subsetSpace S).Sheaf AddCommGrpCat.{u})] (n : ℕ) :
    (integerPushforward S).H' n (⊤ : Opens X) ⟶
      integerCohomology (subsetSpace S) n :=
  CategoryTheory.Sheaf.pushforwardCohomologyMap (subsetInclusion S)
    (constantIntegerSheaf (subsetSpace S)) n (⊤ : Opens X)

/-- For a closed subset, the comparison `H^n(X, i_* ℤ) ⟶ H^n(Y, ℤ)` is an isomorphism. -/
theorem integerPushforward_cohomologyMap_isIso {Y : Set X} (hY : IsClosed Y)
    [HasExt.{u} (X.Sheaf AddCommGrpCat.{u})]
    [HasExt.{u} ((subsetSpace Y).Sheaf AddCommGrpCat.{u})] (n : ℕ) :
    IsIso (integerPushforward_cohomologyMap Y n) :=
  CategoryTheory.Sheaf.ClosedEmbedding.comparison_isIso (subsetInclusion Y)
    hY.isClosedEmbedding_subtypeVal (constantIntegerSheaf (subsetSpace Y)) n ⊤

/-- The map on integer cohomology of `X` induced by `toSum`. -/
def toSum_cohomology (Y Z : Set X)
    [HasExt.{u} (X.Sheaf AddCommGrpCat.{u})] (n : ℕ) :
    integerCohomology X n ⟶
      (integerPushforward Y ⊞ integerPushforward Z).H' n (⊤ : Opens X) :=
  CategoryTheory.Sheaf.cohomologyMap (toSum Y Z) n ⊤

/-- The map on integer cohomology of `X` induced by `fromSum`. -/
def fromSum_cohomology (Y Z : Set X)
    [HasExt.{u} (X.Sheaf AddCommGrpCat.{u})] (n : ℕ) :
    (integerPushforward Y ⊞ integerPushforward Z).H' n (⊤ : Opens X) ⟶
      (integerPushforward (Y ∩ Z)).H' n (⊤ : Opens X) :=
  CategoryTheory.Sheaf.cohomologyMap (fromSum Y Z) n ⊤

/-- Comparison from cohomology of a biproduct of sheaves on the top open to the biproduct of
their cohomologies. -/
def integerPushforwardBiprod_cohomologyComparison (Y Z : Set X)
    [HasExt.{u} (X.Sheaf AddCommGrpCat.{u})] (n : ℕ) :
    (integerPushforward Y ⊞ integerPushforward Z).H' n (⊤ : Opens X) ⟶
      (integerPushforward Y).H' n (⊤ : Opens X) ⊞
        (integerPushforward Z).H' n (⊤ : Opens X) :=
  biprod.lift (CategoryTheory.Sheaf.cohomologyMap biprod.fst n ⊤)
    (CategoryTheory.Sheaf.cohomologyMap biprod.snd n ⊤)

/-- The biproduct comparison on `H' n ⊤` is an isomorphism. -/
theorem integerPushforwardBiprod_cohomologyComparison_isIso (Y Z : Set X)
    [HasExt.{u} (X.Sheaf AddCommGrpCat.{u})] (n : ℕ) :
    IsIso (integerPushforwardBiprod_cohomologyComparison Y Z n) :=
  -- Local instance justification (search instability): mathlib's bridge from finite to
  -- binary biproduct preservation is a lemma, not a registered instance.
  haveI := preservesBinaryBiproducts_of_preservesBiproducts
    (CategoryTheory.Abelian.extFunctorObj (GrothendieckTopology.FreeAbelianYoneda.obj
      (Opens.grothendieckTopology X) ⊤) n)
  ((CategoryTheory.Abelian.extFunctorObj (GrothendieckTopology.FreeAbelianYoneda.obj
    (Opens.grothendieckTopology X) ⊤) n).mapBiprod
      (integerPushforward Y) (integerPushforward Z)).isIso_hom

/-- Composite comparison from cohomology of `i_* ℤ_Y ⊞ j_* ℤ_Z` on `X` to
integer cohomology of `Y` and `Z`. -/
def toIntegerCohomologyBiprod (Y Z : Set X)
    [HasExt.{u} (X.Sheaf AddCommGrpCat.{u})]
    [HasExt.{u} ((subsetSpace Y).Sheaf AddCommGrpCat.{u})]
    [HasExt.{u} ((subsetSpace Z).Sheaf AddCommGrpCat.{u})] (n : ℕ) :
    (integerPushforward Y ⊞ integerPushforward Z).H' n (⊤ : Opens X) ⟶
      integerCohomology (subsetSpace Y) n ⊞ integerCohomology (subsetSpace Z) n :=
  integerPushforwardBiprod_cohomologyComparison Y Z n ≫
    biprod.map (integerPushforward_cohomologyMap Y n) (integerPushforward_cohomologyMap Z n)

/-- Closed-embedding cohomology comparisons, together with additivity of Ext, identify
cohomology of the sum of the two direct images with the sum of their integer cohomologies. -/
def toIntegerCohomologyBiprodIso {Y Z : Set X} (hY : IsClosed Y) (hZ : IsClosed Z)
    [HasExt.{u} (X.Sheaf AddCommGrpCat.{u})]
    [HasExt.{u} ((subsetSpace Y).Sheaf AddCommGrpCat.{u})]
    [HasExt.{u} ((subsetSpace Z).Sheaf AddCommGrpCat.{u})] (n : ℕ) :
    (integerPushforward Y ⊞ integerPushforward Z).H' n (⊤ : Opens X) ≅
      integerCohomology (subsetSpace Y) n ⊞ integerCohomology (subsetSpace Z) n :=
  -- Local instance justification (search instability): the canonical additive functor
  -- preserves finite biproducts; mathlib exposes the binary bridge only as a lemma.
  haveI := preservesBinaryBiproducts_of_preservesBiproducts
    (CategoryTheory.Abelian.extFunctorObj (GrothendieckTopology.FreeAbelianYoneda.obj
      (Opens.grothendieckTopology X) ⊤) n)
  (CategoryTheory.Abelian.extFunctorObj (GrothendieckTopology.FreeAbelianYoneda.obj
    (Opens.grothendieckTopology X) ⊤) n).mapBiprod _ _ ≪≫
    biprod.mapIso
      (CategoryTheory.Sheaf.ClosedEmbedding.comparisonIso (subsetInclusion Y)
        hY.isClosedEmbedding_subtypeVal (constantIntegerSheaf (subsetSpace Y)) n ⊤)
      (CategoryTheory.Sheaf.ClosedEmbedding.comparisonIso (subsetInclusion Z)
        hZ.isClosedEmbedding_subtypeVal (constantIntegerSheaf (subsetSpace Z)) n ⊤)

/-- The forward map of the biproduct identification is the composite comparison. -/
@[simp]
theorem toIntegerCohomologyBiprodIso_hom {Y Z : Set X} (hY : IsClosed Y) (hZ : IsClosed Z)
    [HasExt.{u} (X.Sheaf AddCommGrpCat.{u})]
    [HasExt.{u} ((subsetSpace Y).Sheaf AddCommGrpCat.{u})]
    [HasExt.{u} ((subsetSpace Z).Sheaf AddCommGrpCat.{u})] (n : ℕ) :
    (toIntegerCohomologyBiprodIso hY hZ n).hom = toIntegerCohomologyBiprod Y Z n := rfl

/-- For closed subsets, the composite comparison to integer cohomology of `Y` and `Z` is an
isomorphism. -/
theorem toIntegerCohomologyBiprod_isIso {Y Z : Set X} (hY : IsClosed Y) (hZ : IsClosed Z)
    [HasExt.{u} (X.Sheaf AddCommGrpCat.{u})]
    [HasExt.{u} ((subsetSpace Y).Sheaf AddCommGrpCat.{u})]
    [HasExt.{u} ((subsetSpace Z).Sheaf AddCommGrpCat.{u})] (n : ℕ) :
    IsIso (toIntegerCohomologyBiprod Y Z n) :=
  (toIntegerCohomologyBiprodIso hY hZ n).isIso_hom

/-- Connecting map of the closed-union sequence on objectwise cohomology of the top open. -/
def connecting {Y Z : Set X} (hS : (shortComplex Y Z).ShortExact)
    [HasExt.{u} (X.Sheaf AddCommGrpCat.{u})] (n : ℕ) :
    (integerPushforward (Y ∩ Z)).H' n (⊤ : Opens X) ⟶ integerCohomology X (n + 1) :=
  AddCommGrpCat.ofHom (hS.extClass.postcomp _ rfl)

/-- The map on integer cohomology induced by `toSum`, after identifying the biproduct of
pushforward cohomologies with `integerCohomology` of `Y` and of `Z`. -/
def toSum_integerCohomology (Y Z : Set X)
    [HasExt.{u} (X.Sheaf AddCommGrpCat.{u})]
    [HasExt.{u} ((subsetSpace Y).Sheaf AddCommGrpCat.{u})]
    [HasExt.{u} ((subsetSpace Z).Sheaf AddCommGrpCat.{u})] (n : ℕ) :
    integerCohomology X n ⟶
      integerCohomology (subsetSpace Y) n ⊞ integerCohomology (subsetSpace Z) n :=
  toSum_cohomology Y Z n ≫ toIntegerCohomologyBiprod Y Z n

/-- The map on integer cohomology induced by `fromSum`, after identifying the middle and right
terms with `integerCohomology` of `Y` and `Z`, and of `Y ∩ Z`. -/
def fromSum_integerCohomology {Y Z : Set X} (hY : IsClosed Y) (hZ : IsClosed Z)
    [HasExt.{u} (X.Sheaf AddCommGrpCat.{u})]
    [HasExt.{u} ((subsetSpace Y).Sheaf AddCommGrpCat.{u})]
    [HasExt.{u} ((subsetSpace Z).Sheaf AddCommGrpCat.{u})]
    [HasExt.{u} ((subsetSpace (Y ∩ Z)).Sheaf AddCommGrpCat.{u})] (n : ℕ) :
    integerCohomology (subsetSpace Y) n ⊞ integerCohomology (subsetSpace Z) n ⟶
      integerCohomology (subsetSpace (Y ∩ Z)) n :=
  (toIntegerCohomologyBiprodIso hY hZ n).inv ≫
    fromSum_cohomology Y Z n ≫ integerPushforward_cohomologyMap (Y ∩ Z) n

/-- Connecting map of the closed-union sequence on integer cohomology of `Y ∩ Z` and of `X`. -/
def connecting_integerCohomology {Y Z : Set X} (hY : IsClosed Y) (hZ : IsClosed Z)
    (hS : (shortComplex Y Z).ShortExact)
    [HasExt.{u} (X.Sheaf AddCommGrpCat.{u})]
    [HasExt.{u} ((subsetSpace (Y ∩ Z)).Sheaf AddCommGrpCat.{u})] (n : ℕ) :
    integerCohomology (subsetSpace (Y ∩ Z)) n ⟶ integerCohomology X (n + 1) :=
  (CategoryTheory.Sheaf.ClosedEmbedding.comparisonIso (subsetInclusion (Y ∩ Z))
    (hY.inter hZ).isClosedEmbedding_subtypeVal
    (constantIntegerSheaf (subsetSpace (Y ∩ Z))) n ⊤).inv ≫
    connecting hS n

/-- The six-term sequence of objectwise cohomology of the closed-union short complex, on the
top open of `X`. -/
def cohomologySequence {Y Z : Set X} (hS : (shortComplex Y Z).ShortExact)
    [HasExt.{u} (X.Sheaf AddCommGrpCat.{u})] (n : ℕ) :
    ComposableArrows AddCommGrpCat.{u} 5 :=
  ComposableArrows.mk₅ (toSum_cohomology Y Z n) (fromSum_cohomology Y Z n) (connecting hS n)
    (toSum_cohomology Y Z (n + 1)) (fromSum_cohomology Y Z (n + 1))

/-- The six-term sequence of objectwise cohomology of the closed-union short complex, on the
top open of `X`, is exact. -/
theorem cohomologySequence_exact {Y Z : Set X} (hY : IsClosed Y) (hZ : IsClosed Z)
    (hcover : Y ∪ Z = Set.univ)
    [HasExt.{u} (X.Sheaf AddCommGrpCat.{u})] (n : ℕ) :
    (cohomologySequence (shortExact hY hZ hcover) n).Exact :=
  sorry

/-- The six-term sequence of integer cohomology of `X`, of `Y` and `Z`, and of `W = Y ∩ Z`,
obtained by conjugating `cohomologySequence` along `toIntegerCohomologyBiprod` and
`integerPushforward_cohomologyMap (Y ∩ Z)`. -/
def integerCohomologySequence {Y Z : Set X} (hY : IsClosed Y) (hZ : IsClosed Z)
    (hS : (shortComplex Y Z).ShortExact)
    [HasExt.{u} (X.Sheaf AddCommGrpCat.{u})]
    [HasExt.{u} ((subsetSpace Y).Sheaf AddCommGrpCat.{u})]
    [HasExt.{u} ((subsetSpace Z).Sheaf AddCommGrpCat.{u})]
    [HasExt.{u} ((subsetSpace (Y ∩ Z)).Sheaf AddCommGrpCat.{u})] (n : ℕ) :
    ComposableArrows AddCommGrpCat.{u} 5 :=
  ComposableArrows.mk₅ (toSum_integerCohomology Y Z n) (fromSum_integerCohomology hY hZ n)
    (connecting_integerCohomology hY hZ hS n) (toSum_integerCohomology Y Z (n + 1))
    (fromSum_integerCohomology hY hZ (n + 1))

/-- For `X = Y ∪ Z` with `Y` and `Z` closed, then for every `n` the
six-term sequence on `integerCohomology X n`,
`integerCohomology (subsetSpace Y) n ⊞ integerCohomology (subsetSpace Z) n`,
`integerCohomology (subsetSpace (Y ∩ Z)) n`, and the three degree-`(n + 1)` copies, is exact.
The arrows are `toSum_cohomology`, `fromSum_cohomology`, and `connecting`, conjugated by
`toIntegerCohomologyBiprod` and `integerPushforward_cohomologyMap (Y ∩ Z)`. -/
theorem integerCohomologySequence_exact {Y Z : Set X} (hY : IsClosed Y) (hZ : IsClosed Z)
    (hcover : Y ∪ Z = Set.univ)
    [HasExt.{u} (X.Sheaf AddCommGrpCat.{u})]
    [HasExt.{u} ((subsetSpace Y).Sheaf AddCommGrpCat.{u})]
    [HasExt.{u} ((subsetSpace Z).Sheaf AddCommGrpCat.{u})]
    [HasExt.{u} ((subsetSpace (Y ∩ Z)).Sheaf AddCommGrpCat.{u})] (n : ℕ) :
    (integerCohomologySequence hY hZ (shortExact hY hZ hcover) n).Exact :=
  sorry

/-- The degree-zero map
`integerCohomology X 0 ⟶ integerCohomology (subsetSpace Y) 0 ⊞ integerCohomology (subsetSpace Z) 0`
is a monomorphism. `ComposableArrows.Exact` does not see the initial spot of the six-term
sequence. -/
theorem toSum_integerCohomology_zero_mono {Y Z : Set X} (hY : IsClosed Y) (hZ : IsClosed Z)
    (hcover : Y ∪ Z = Set.univ)
    [HasExt.{u} (X.Sheaf AddCommGrpCat.{u})]
    [HasExt.{u} ((subsetSpace Y).Sheaf AddCommGrpCat.{u})]
    [HasExt.{u} ((subsetSpace Z).Sheaf AddCommGrpCat.{u})]
    [HasExt.{u} ((subsetSpace (Y ∩ Z)).Sheaf AddCommGrpCat.{u})] :
    Mono ((integerCohomologySequence hY hZ (shortExact hY hZ hcover) 0).map' 0 1) :=
  sorry

end TopCat.Sheaf.ClosedUnion

end
