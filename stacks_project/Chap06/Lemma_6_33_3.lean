/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Topology.Sheaves.OpenCover.Algebraic.Basis
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.OpenCover
import StacksCheckRecall

@[expose] public section

/- Lemma 6.33.3 (1): an open-cover gluing datum of sheaves of abelian groups is realized by an
`AddCommGrpCat`-valued sheaf on the ambient space. This is a standard algebraic specialization of
the coefficient-generic realization theorem. -/
@[stacks 00AM "sheaves of abelian groups"]
recall TopCat.Sheaf.OpenCover.Gluing.existsRealizingSheaf

/- Lemma 6.33.3 (2): an open-cover gluing datum of sheaves valued in a type of algebraic
structures is realized by a `C`-valued sheaf on the ambient space. -/
@[stacks 00AM "sheaves of algebraic structures"]
recall TopCat.Sheaf.OpenCover.Gluing.existsRealizingSheaf

/- Lemma 6.33.3 (3): under the Stacks convention that rings are commutative with `1`, an
open-cover gluing datum of sheaves of modules is realized by a sheaf on the ambient space. The
library owner is stated for a possibly noncommutative ring sheaf, of which the textbook setting is
a direct specialization. -/
@[stacks 00AM "sheaves of modules"]
recall ModuleSheafOpenCover.Gluing.existsRealizingSheaf
