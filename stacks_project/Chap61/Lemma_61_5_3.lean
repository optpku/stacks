module

public import ReasLib.Algebra.WLocalHull.Properties
public import ReasLib.AlgebraicGeometry.WLocalHull.Properties
import StacksCheckRecall

@[expose] public section

universe u

/- Lemma 61.5.3 (1): A → A_w is ind-Zariski and faithfully flat. -/
@[stacks 0975] #check (Algebra.WLocalHull.algebraMap_indZariski :
  ∀ (A : Type u) [CommRing A],
    (algebraMap A (Algebra.WLocalHull.wLocalization A)).IndZariski)
@[stacks 0975] #check (Algebra.WLocalHull.algebraMap_faithfullyFlat :
  ∀ (A : Type u) [CommRing A],
    (algebraMap A (Algebra.WLocalHull.wLocalization A)).FaithfullyFlat)

/- Lemma 61.5.3 (2): X_w → X induces a bijection Z → X. -/
@[stacks 0975] #check (AlgebraicGeometry.WLocal.Construction.bijective_closedToSpec :
  ∀ (A : Type u) [CommRing A],
    Function.Bijective (AlgebraicGeometry.WLocal.Construction.closedToSpec A))

/- Lemma 61.5.3 (3): Z is the set of closed points of X_w. -/
@[stacks 0975] #check (AlgebraicGeometry.WLocal.Construction.range_closedι_eq_closedPoints :
  ∀ (A : Type u) [CommRing A],
    Set.range (AlgebraicGeometry.WLocal.Construction.closedι A) =
      closedPoints (AlgebraicGeometry.WLocal.Construction.scheme A))

/- Lemma 61.5.3 (4): Z is a reduced scheme. -/
@[stacks 0975] #check (AlgebraicGeometry.WLocal.Construction.instIsReduced_closedSubscheme :
  ∀ (A : Type u) [CommRing A],
    AlgebraicGeometry.IsReduced (AlgebraicGeometry.WLocal.Construction.closedSubscheme A))

/- Lemma 61.5.3 (5): every point of X_w specializes to a unique point of Z. -/
@[stacks 0975] #check (AlgebraicGeometry.WLocal.Construction.existsUnique_specializes_mem_range_closedι :
  ∀ (A : Type u) [CommRing A] (x : AlgebraicGeometry.WLocal.Construction.scheme A),
    ∃! y, y ∈ Set.range (AlgebraicGeometry.WLocal.Construction.closedι A) ∧ x ⤳ y)

/- Lemma 61.5.3 (6): in particular X_w is w-local. -/
@[stacks 0975] #check (AlgebraicGeometry.WLocal.Construction.instWLocalSpace :
  ∀ (A : Type u) [CommRing A],
    WLocalSpace (AlgebraicGeometry.WLocal.Construction.scheme A))
