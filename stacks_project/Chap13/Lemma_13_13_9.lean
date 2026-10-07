module

import ReasLib.CategoryTheory.Filtration.Derived.BoundedLocalization.Triangulated
import StacksCheckRecall

@[expose] public section

open CategoryTheory CategoryTheory.MorphismProperty CategoryTheory.ObjectProperty

universe v u

namespace CategoryTheory.FilteredObject.FiniteDerived

/- Lemma 13.13.9 (`05S6`): the three bounded variants of finite filtered acyclic complexes
and finite filtered quasi-isomorphisms. -/
@[stacks 05S6] #check Plus.Acyclic
@[stacks 05S6] #check Minus.Acyclic
@[stacks 05S6] #check Bounded.Acyclic
@[stacks 05S6] #check Plus.QuasiIso
@[stacks 05S6] #check Minus.QuasiIso
@[stacks 05S6] #check Bounded.QuasiIso

section Closure

variable (C : Type u) [Category.{v} C] [Abelian C]

/- Lemma 13.13.9 (`05S6`): these acyclic properties are strictly full, saturated under
retracts, and triangulated. -/
@[stacks 05S6]
#check (inferInstance : (Plus.Acyclic C).IsClosedUnderIsomorphisms)

@[stacks 05S6]
#check (inferInstance : (Plus.Acyclic C).IsStableUnderRetracts)

@[stacks 05S6]
#check (inferInstance : (Plus.Acyclic C).IsTriangulated)

@[stacks 05S6]
#check (inferInstance : (Minus.Acyclic C).IsClosedUnderIsomorphisms)

@[stacks 05S6]
#check (inferInstance : (Minus.Acyclic C).IsStableUnderRetracts)

@[stacks 05S6]
#check (inferInstance : (Minus.Acyclic C).IsTriangulated)

@[stacks 05S6]
#check (inferInstance : (Bounded.Acyclic C).IsClosedUnderIsomorphisms)

@[stacks 05S6]
#check (inferInstance : (Bounded.Acyclic C).IsStableUnderRetracts)

@[stacks 05S6]
#check (inferInstance : (Bounded.Acyclic C).IsTriangulated)

/- Lemma 13.13.9 (`05S6`): the corresponding quasi-isomorphisms are saturated
multiplicative systems. -/
@[stacks 05S6]
#check (inferInstance : (Plus.QuasiIso C).IsSaturatedMultiplicativeSystem)

@[stacks 05S6]
#check (inferInstance : (Minus.QuasiIso C).IsSaturatedMultiplicativeSystem)

@[stacks 05S6]
#check (inferInstance : (Bounded.QuasiIso C).IsSaturatedMultiplicativeSystem)

end Closure

/- Lemma 13.13.9 (`05S6`) (1): the bounded-below quotient has the stated kernel, localizes at
finite filtered quasi-isomorphisms, and is triangulated. -/
@[stacks 05S6 "(1)"] #check Plus.Quotient.functor
@[stacks 05S6 "(1)"] #check Plus.Quotient.kernel_eq
@[stacks 05S6 "(1)"] #check Plus.Acyclic.trW
@[stacks 05S6 "(1)"] #check Plus.Quotient.isLocalization
@[stacks 05S6 "(1)"] #check Plus.Quotient.isTriangulated

/- Lemma 13.13.9 (`05S6`) (2): the bounded-above quotient has the stated kernel, localizes at
finite filtered quasi-isomorphisms, and is triangulated. -/
@[stacks 05S6 "(2)"] #check Minus.Quotient.functor
@[stacks 05S6 "(2)"] #check Minus.Quotient.kernel_eq
@[stacks 05S6 "(2)"] #check Minus.Acyclic.trW
@[stacks 05S6 "(2)"] #check Minus.Quotient.isLocalization
@[stacks 05S6 "(2)"] #check Minus.Quotient.isTriangulated

/- Lemma 13.13.9 (`05S6`) (3): the bounded quotient has the stated kernel, localizes at finite
filtered quasi-isomorphisms, and is triangulated. -/
@[stacks 05S6 "(3)"] #check Bounded.Quotient.functor
@[stacks 05S6 "(3)"] #check Bounded.Quotient.kernel_eq
@[stacks 05S6 "(3)"] #check Bounded.Acyclic.trW
@[stacks 05S6 "(3)"] #check Bounded.Quotient.isLocalization
@[stacks 05S6 "(3)"] #check Bounded.Quotient.isTriangulated

end CategoryTheory.FilteredObject.FiniteDerived
