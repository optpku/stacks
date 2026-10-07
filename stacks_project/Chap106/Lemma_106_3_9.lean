module

public import stacks_project.Chap106.Lemma_106_3_9_Properties
import StacksCheckRecall

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.AlgebraicStack
open scoped Bicategory

universe u

/- Lemma 106.3.9 (1): a thickening of algebraic stacks is an algebraic space if
and only if the target is an algebraic space. -/
@[stacks 0BPW] #check IsThickening.isRepresentableByAlgebraicSpace_iff

/- Lemma 106.3.9 (2): a thickening of algebraic stacks is a scheme if and only
if the target is a scheme. -/
@[stacks 0BPW] #check IsThickening.isScheme_iff

/- Lemma 106.3.9 (3): a thickening of algebraic stacks is DM if and only if the
target is DM. -/
@[stacks 0BPW] #check IsThickening.isDM_iff

/- Lemma 106.3.9 (4): a thickening of algebraic stacks is quasi-DM if and only
if the target is quasi-DM. -/
@[stacks 0BPW] #check IsThickening.isQuasiDM_iff

/- Lemma 106.3.9 (5): a thickening of algebraic stacks is separated if and only
if the target is separated. -/
@[stacks 0BPW] #check IsThickening.isSeparated_iff

/- Lemma 106.3.9 (6): a thickening of algebraic stacks is quasi-separated if and
only if the target is quasi-separated. -/
@[stacks 0BPW] #check IsThickening.isQuasiSeparated_iff
