module

public import ReasLib.Topology.Sheaves.OpenCover.Algebraic.Basis
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.OpenCover
import StacksCheckRecall

@[expose] public section

/- Lemma 6.33.4 (1): for an open cover `X = ⋃ i, U i`, restriction gives an equivalence between
sheaves of sets on `X` and open-cover gluing data for `U`. This is the set-valued specialization
of the coefficient-generic algebraic descent equivalence. -/
@[stacks 00AN]
recall TopCat.Sheaf.OpenCover.Gluing.ofSheafFunctor_isEquivalence

/- Lemma 6.33.4 (2): for an open cover `X = ⋃ i, U i`, restriction gives an equivalence between
sheaves of abelian groups on `X` and their open-cover gluing data. -/
@[stacks 00AN "sheaves of abelian groups"]
recall TopCat.Sheaf.OpenCover.Gluing.ofSheafFunctor_isEquivalence

/- Lemma 6.33.4 (3): for a type of algebraic structures, restriction gives an equivalence
between `C`-valued sheaves on `X` and their open-cover gluing data. -/
@[stacks 00AN "sheaves of algebraic structures"]
recall TopCat.Sheaf.OpenCover.Gluing.ofSheafFunctor_isEquivalence

/- Lemma 6.33.4 (4): under the Stacks convention that rings are commutative with `1`,
restriction gives an equivalence between sheaves of modules on `X` and their open-cover gluing
data. The library owner is stated for arbitrary ring sheaves, so the commutative source statement
is its direct specialization. -/
@[stacks 00AN "sheaves of modules"]
recall ModuleSheafOpenCover.Gluing.ofSheafFunctor_isEquivalence
