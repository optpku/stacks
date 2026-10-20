module

public import ReasLib.CategoryTheory.Sites.BeckChevalley
public import ReasLib.CategoryTheory.Sites.AbelianSheaf.LowerShriek
public import ReasLib.AlgebraicGeometry.RingedSite.Module.BaseChange.OfSites
public import ReasLib.CategoryTheory.DerivedCategory.Functor.TotalRightDerived.Homotopy.Naturality
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 21.37.6

The source item is a derived statement about a square of ringed topoi presented by site functors
`u : 𝒞 ⥤ 𝒟`, `u' : 𝒞' ⥤ 𝒟'`, `v : 𝒟' ⥤ 𝒟`, and `v' : 𝒞' ⥤ 𝒞`.  The source assumptions are:

* `u` and `u'` are cocontinuous, while `v` and `v'` are continuous and cocontinuous;
* the square is 2-commutative, `u' ⋙ v = v' ⋙ u` up to the displayed `CatCommSq` isomorphism;
* for every `V' : 𝒟'`, the corresponding structured-arrow functor is final;
* the inverse-image structure sheaves are identified with the displayed structure sheaves; and
* the abelian lower-shriek functor along `v'` is exact.

These are deliberately not replaced by a bundled `RingedSite.Hom` plus flatness hypotheses: a
continuous site functor need not be representably flat, and exactness of a module pullback alone
does not make an arbitrary mate invertible.  The reusable construction is layered instead:

1. `CatCommSq.BeckChevalley.comparison` and its finality theorem own the site-level comparison;
2. `Functor.AbelianLowerShriek` owns the exactness criteria for the abelian lower-shriek; and
3. `Functor.RightDerived.natIsoOfIso` / `isIsomorphic_of_isIsomorphic` transport an explicit
   comparison through any specified total right-derived models.

The module-level and ringed-topos-level bridges are supplied by `FinalSquare.ModuleLift`; this
chapter file is a recall block so that it does not create a second chosen derived map or reverse
the dependency from ReasLib to the chapter.
-/

open CategoryTheory

/- Lemma 21.37.6 (0FN6), site comparison and the finality criterion. -/
@[stacks 0FN6 "site-level comparison"]
#check @CategoryTheory.CatCommSq.BeckChevalley.comparison

@[stacks 0FN6 "site-level comparison isomorphism from finality"]
#check @CategoryTheory.CatCommSq.BeckChevalley.comparison_isIso_of_final

/- Lemma 21.37.6 (0FN6), exactness of the abelian lower-shriek. -/
@[stacks 0FN6 "exact lower-shriek criterion"]
#check @CategoryTheory.Functor.AbelianLowerShriek.exact_of_isRightAdjoint

@[stacks 0FN6 "exact lower-shriek from finite connected limits"]
#check @CategoryTheory.Functor.AbelianLowerShriek.exact_of_preservesFiniteConnectedLimits

/- Lemma 21.37.6 (0FN6), module-linear and derived transport bridges. -/
@[stacks 0FN6 "module-linear final-square bridge"]
#check @RingedSite.Hom.FinalSquare.ModuleLift.lowerShriekComparison_isIso_of_final

@[stacks 0FN6 "derived comparison transport"]
#check @CategoryTheory.Functor.RightDerived.natIsoOfIso

@[stacks 0FN6 "derived comparison transport on isomorphism classes"]
#check @CategoryTheory.Functor.RightDerived.isIsomorphic_of_isIsomorphic
