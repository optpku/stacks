module

public import stacks_project.Chap85.Remark_85_5_4_Fiberwise
public import stacks_project.Chap85.Remark_85_5_4_MorphismDiagram
import StacksCheckRecall

/-!
# Remark 85.5.4

In Situation 85.3.3, with augmentations `a0`, `a'0` as in Remark 85.4.1 and a
morphism `h` of simplicial sites as in Remark 85.5.1, a morphism of topoi
`h₋₁ : Sh(D) ⟶ Sh(D')` is compatible with `h`, `a0`, `a'0` when it is presented
by a morphism of sites (case A) or a cocontinuous functor (case B) closing the
degree-zero square. In both cases the same square commutes as morphisms of
topoi.
-/

@[expose] public section

open CategoryTheory

/- Remark 85.5.4 (1)
In Situation 85.3.3 case A, a morphism of topoi `h₋₁ : Sh(D) ⟶ Sh(D')` is
compatible with `h`, `a0`, `a'0` if it comes from a morphism of sites
`h₋₁ : D ⟶ D'` presented by `v : D' ⥤ D` such that
`u0' ⋙ (α.app ⦋0⦌).toFunctor = v ⋙ u0` as morphisms of sites. The same square
commutes as morphisms of topoi, see Sites Definition 7.14.5. -/
@[stacks 0D98] #check @SimplicialSites.IsCompatible
@[stacks 0D98] #check @SimplicialSites.IsCompatible.iff
@[stacks 0D98] #check @SimplicialSites.IsCompatible.topos
@[stacks 0D98] #check @SimplicialSites.IsCompatible.inverseImage_comp

/- Remark 85.5.4 (2)
In Situation 85.3.3 case B, a morphism of topoi `h₋₁ : Sh(D) ⟶ Sh(D')` is
compatible with `h`, `a0`, `a'0` if it comes from a cocontinuous functor
`v : D ⥤ D'` such that `(α.app (op ⦋0⦌)).toFunctor ⋙ u0' = u0 ⋙ v` as functors.
The same square commutes as morphisms of topoi, see Sites Lemma 7.21.2. -/
@[stacks 0D98] #check @Grothendieck.IsCompatible
@[stacks 0D98] #check @Grothendieck.IsCompatible.iff
@[stacks 0D98] #check @Grothendieck.IsCompatible.topos
@[stacks 0D98] #check @Grothendieck.IsCompatible.inverseImage_comp
