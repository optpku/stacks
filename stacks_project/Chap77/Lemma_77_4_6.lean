module

public import stacks_project.Chap77.Lemma_77_4_6_EtaleFree
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry.AlgebraicSpace.Modules

/- Lemma 77.4.6: a finite-type morphism of algebraic spaces and a finite-type
quasi-coherent module, flat at every point of a fibre, admit an étale scheme
neighbourhood of the base point and an affine étale refinement of the stalk
pullback whose pulled-back module has free global sections and which covers
exactly the original fibre. -/
@[stacks 0CVW] #check existsEtaleCoverWithFreeSections_of_finiteType
