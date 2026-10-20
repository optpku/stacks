module

public import ReasLib.CategoryTheory.Sites.Topos.Factorization.Special
public import StacksCheckRecall.CommandCrossRef

/-!
# Lemma 7.29.6

Special-cocontinuous replacement-site factorizations are reusable topos API
owned by `MorphismOfTopoiIn.Factorization`.
-/

@[expose] public section

/- Lemma 7.29.6 (03A2): every morphism of topoi admits a subcanonical
finite-limit replacement site with the stated special-cocontinuous source
presentation and target-side continuity data. -/
@[stacks 03A2 "factorization"] #check @CategoryTheory.MorphismOfTopoiIn.Factorization.SpecialSite

@[stacks 03A2 "existence"] #check @CategoryTheory.MorphismOfTopoiIn.Factorization.SpecialSite.exists_of_morphism

@[stacks 03A2 "specification"] #check @CategoryTheory.MorphismOfTopoiIn.Factorization.SpecialSite.spec

@[stacks 03A2 "cover image"] #check @CategoryTheory.MorphismOfTopoiIn.Factorization.SpecialSite.target_cover_mem
