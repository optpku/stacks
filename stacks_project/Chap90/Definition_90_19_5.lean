module

public import stacks_project.Chap90.Definition_90_19_5_AutFunctor
import StacksCheckRecall

@[expose] public section

open CategoryTheory

/- Definition 90.19.5: if `p : F ⥤ C` is cofibered in groupoids and a choice of
pushforwards has been made, the automorphism functor of `x : F` is
`Functor.autFunctor p x : Under (p.obj x) ⥤ Type v`, sending `f : p.obj x ⟶ V` to
`Aut (Chosen.pushforwardObj p f.hom (Fiber.ofObj p x))` in the fibre over `V` and
sending an under-morphism to the homomorphism induced by
`Chosen.pushforwardComparison`. -/
@[stacks 06JT]
#check Functor.autFunctor
