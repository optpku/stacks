module

public import stacks_project.Chap66.Definition_66_29_1_QCoh
public import stacks_project.Chap66.Definition_66_29_1_RingedSite
import StacksCheckRecall

@[expose] public section

/- Definition 66.29.1 (1): a quasi-coherent 𝒪_X-module on an algebraic space X over a scheme S
is a quasi-coherent module on the ringed site (X_étale, 𝒪_X) in the sense of
SheafOfModules.IsQuasicoherent. -/
@[stacks 03G9] #check AlgebraicGeometry.AlgebraicSpace.quasiCoherentModuleProperty

/- Definition 66.29.1 (2): the category of quasi-coherent sheaves on X is denoted QCoh(𝒪_X). -/
@[stacks 03G9] #check AlgebraicGeometry.AlgebraicSpace.QCoh
