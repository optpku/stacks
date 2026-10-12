/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Fibered.Gerbe.Cohomology.Section
import StacksCheckRecall

@[expose] public section

open CategoryTheory

/- Lemma 21.11.1 (0CK0): a cofinal system of coverings with vanishing first cohomology on
terms and pairwise overlaps, together with vanishing second cohomology of the band on `U`,
produces a section of the abelian gerbe over `U`. -/
@[stacks 0CK0 "cofinal H1 and H2 vanishing gives a gerbe section"]
#check @CategoryTheory.Sheaf.Cech.CofinalH

@[stacks 0CK0 "cofinal vanishing supplies a refining covering"]
#check @CategoryTheory.Sheaf.Cech.CofinalH.exists_refinement

@[stacks 0CK0 "degree-one cofinal vanishing on terms and overlaps"]
#check @CategoryTheory.Sheaf.HasCofinalCoveringsWithVanishingH1OnTermsAndOverlaps

@[stacks 0CK0 "cofinal H1 and H2 vanishing gives a gerbe section"]
#check @CategoryTheory.IsGerbe.existsSection_of_cofinalH1
