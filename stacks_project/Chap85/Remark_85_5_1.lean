module

public import stacks_project.Chap85.Remark_85_5_1_Morphism
import StacksCheckRecall

/-!
# Remark 85.5.1

A morphism of simplicial sites in Situation 85.3.3 is either a stagewise family
of morphisms of sites (case A) or a stagewise family of cocontinuous functors
(case B). In both cases the same square commutes as morphisms of topoi.
-/

@[expose] public section

open CategoryTheory

/- Remark 85.5.1 (1)
In Situation 85.3.3 case A, a morphism of simplicial sites is a family of
morphisms of sites `h_n : C.obj n ⟶ C'.obj n` presented by functors
`(α.app n).toFunctor : C'.obj n ⥤ C.obj n`, with
`f'_φ ∘ h_n = h_m ∘ f_φ` as morphisms of sites for all `φ : m ⟶ n`.
The same square commutes as morphisms of topoi, see Sites Definition 7.14.5. -/
@[stacks 0D95] #check @SimplicialSites.IsMorphism
@[stacks 0D95] #check @SimplicialSites.IsMorphism.naturality_toFunctor
@[stacks 0D95] #check @SimplicialSites.IsMorphism.topos
@[stacks 0D95] #check @SimplicialSites.IsMorphism.inverseImage_naturality

/- Remark 85.5.1 (2)
In Situation 85.3.3 case B, a morphism of simplicial sites is a family of
cocontinuous functors `v_n : C_n ⥤ C'_n` inducing morphisms of topoi
`h_n : Sh(C_n) ⟶ Sh(C'_n)`, with `u'_φ ∘ v_n = v_m ∘ u_φ` as functors for all
`φ : m ⟶ n`. The same square commutes as morphisms of topoi, see Sites
Lemma 7.21.2. -/
@[stacks 0D95] #check @Grothendieck.IsFiberwiseMorphism
@[stacks 0D95] #check @Grothendieck.IsFiberwiseMorphism.naturality_toFunctor
@[stacks 0D95] #check @Grothendieck.IsFiberwiseMorphism.topos
@[stacks 0D95] #check @Grothendieck.IsFiberwiseMorphism.inverseImage_naturality
