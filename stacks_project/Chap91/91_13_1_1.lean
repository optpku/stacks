module

public import stacks_project.Chap91.«91_13_1_1_Cube»
import StacksCheckRecall

/- 91.13.1.1: the commutative diagram of morphisms of ringed topoi with vertices
`(Sh(C2), O2)`, `(Sh(C'2), O'2)`, `(Sh(B2), O_{B2})`, `(Sh(B'2), O_{B'2})`,
`(Sh(C1), O1)`, `(Sh(C'1), O'1)`, `(Sh(B1), O_{B1})`, `(Sh(B'1), O_{B'1})`.
The present arrows are `i2`, `f2`, `f'2`, `t2`, `i1`, `f1`, `f'1`, `t1`, and
the named diagonal `g : (Sh(C2), O2) ⟶ (Sh(C1), O1)`; the unlabeled maps
`(Sh(B2), O_{B2}) ⟶ (Sh(B1), O_{B1})` and `(Sh(B'2), O_{B'2}) ⟶ (Sh(B'1), O_{B'1})`
complete the base face. The morphism `(Sh(C'2), O'2) ⟶ (Sh(C'1), O'1)` is not
part of the diagram. In the wrapping lemma the four horizontals `i2`, `t2`,
`i1`, `t1` are first-order thickenings; that hypothesis is not recorded on
`OpenCube`. -/
@[stacks 08UH] #check @RingedSite.ToposHom.OpenCube
