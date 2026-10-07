module

public import stacks_project.Chap63.Definition_63_4_4_LowerShriek
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry.Scheme.Etale

/- Definition 63.4.4: for a locally quasi-finite morphism `f : X ⟶ Y` of
schemes, the direct image with compact support is the functor
`lowerShriek f : Ab(X_étale) ⥤ Ab(Y_étale)` given by sheafifying the abelian
presheaf `lowerShriekPresheaf f`, i.e. `f_! F = (f_{p!} F)^#`. -/
@[stacks 0F6R] #check lowerShriek

end
