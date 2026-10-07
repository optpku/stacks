module

import stacks_project.Chap81.«81_6_5_2_Cube»
import StacksCheckRecall

/- 81.6.5.2: For a triple (V, U', φ) with U = U' ×_{X'} X and
G(V, U', φ) = V ⨿_U U', a chosen étale scheme presentation yields a commutative
cube with vertices U, U', V, G(V, U', φ) and scheme vertices U1, U1', V1,
G1(V1, U1', φ1). The side faces are cartesian, the front and back faces are
pushouts, and the northeast arrows — in particular G1 ⟶ G — are surjective
étale. -/
@[stacks 07W2] #check AlgebraicGeometry.AlgebraicSpace.Pushout.OverEtaleCube
