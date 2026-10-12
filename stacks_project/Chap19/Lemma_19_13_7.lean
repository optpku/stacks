/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Filtration.Complex.KInjective
import StacksCheckRecall

@[expose] public section

/-!
# Filtered K-Injective Resolutions

Lemma 19.13.7 is owned by the reusable filtered-complex resolution API.  Its individual
injectivity, K-injectivity, and quasi-isomorphism clauses are available through separate classes,
while `FilteredComplex.KInjectiveResolution` bundles the compatible resolving complex and map.
-/

open CategoryTheory

noncomputable section

universe w v u

variable {A : Type u} [Category.{v} A] [Abelian A]
  [IsGrothendieckAbelian.{w} A]

/- Lemma 19.13.7: filtered K-injective resolutions exist in every Grothendieck abelian
category. -/
@[stacks 0BKI] #check
  fun (K : FilteredComplex A) ↦
    (FilteredComplex.KInjectiveResolution.nonempty K :
      Nonempty (FilteredComplex.KInjectiveResolution K))

/- The three orthogonal properties can be consumed independently downstream. -/
#check @FilteredComplex.IsTermwiseInjective
#check @FilteredComplex.IsKInjective
#check @FilteredComplex.IsQuasiIso
