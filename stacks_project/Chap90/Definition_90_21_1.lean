module

public import stacks_project.Chap90.Definition_90_21_1_Groupoid
import StacksCheckRecall

universe u v w

open CategoryTheory

/- Definition 90.21.1 (1): A groupoid in functors on a category `C` is a quintuple
`(U, R, s, t, c)` of functors `U, R : C ⥤ Type w` and morphisms `s, t : R ⟶ U` and
`c : pullback s t ⟶ R` such that for every object `T` of `C`, the evaluation
`(U.obj T, R.obj T, s.app T, t.app T, c.app T)` is a groupoid category. -/
@[stacks 06K3] #check GroupoidInFunctors

/- Definition 90.21.1 (2): A morphism of groupoids in functors on `C` consists of
morphisms `U ⟶ U'` and `R ⟶ R'` such that for every object `T` of `C`, the
components `U.obj T ⟶ U'.obj T` and `R.obj T ⟶ R'.obj T` define a functor of
the corresponding groupoid categories. -/
@[stacks 06K3] #check GroupoidInFunctors.Hom
