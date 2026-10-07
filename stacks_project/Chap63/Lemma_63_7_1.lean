module

public import stacks_project.Chap63.Lemma_63_7_1_Adjunction
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.Scheme.Etale

/- Lemma 63.7.1: Let `f : X ⟶ Y` be a locally quasi-finite morphism of
schemes. Let `Λ` be a ring. The functors `f_!` and `f^!` of
Definition 63.4.4 and Lemma 63.6.1 induce adjoint functors
`f_! = lowerShriekModuleDerived : D(X_étale, Λ) ⥤ D(Y_étale, Λ)` and
`Rf^! = upperShriekModuleDerived : D(Y_étale, Λ) ⥤ D(X_étale, Λ)`
on derived categories. Stacks locally quasi-finite is rendered as
`[LocallyQuasiFinite f]` together with `[LocallyOfFiniteType f]`, as in
`lowerShriek_exact`. -/
@[stacks 0F5N]
#check lowerShriekModuleDerivedAdjunction

end
