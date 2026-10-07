module

public import ReasLib.Algebra.Module.ClosedPointFiber.Splitting
import StacksCheckRecall

/-!
# Proposition 15.128.4 (0GVB)

The dependence locus, component-codimension predicate, and codimension-controlled extension
theorem are owned by `ReasLib.Algebra.Module.ClosedPointFiber.Splitting`.

@stack 0GVB
-/

@[expose] public section

@[stacks 0GVB "section dependence locus"]
#check @Module.ClosedFiber.sectionDependenceLocus

@[stacks 0GVB "component codimension bound"]
#check @Module.ClosedFiber.irreducibleComponentsCodimAtLeast

/- Proposition 15.128.4 (a): the chosen section has the prescribed visible classes. -/
@[stacks 0GVB "Proposition 15.128.4 (a)"]
#check @Module.ClosedFiber.CodimControlledExtension.prescribedValues

/- Proposition 15.128.4 (b): the enlarged dependence locus is supported on the original and
exceptional closed sets. -/
@[stacks 0GVB "Proposition 15.128.4 (b)"]
#check @Module.ClosedFiber.CodimControlledExtension.dependenceLocus_subset

/- Proposition 15.128.4 (c): every exceptional irreducible component has codimension at least
`k`. -/
@[stacks 0GVB "Proposition 15.128.4 (c)"]
#check @Module.ClosedFiber.CodimControlledExtension.components_codimAtLeast

/- Proposition 15.128.4, clauses (a)-(c): one pair of witnesses satisfies all three clauses. -/
@[stacks 0GVB "Proposition 15.128.4, clauses (a)-(c)"]
#check @Module.ClosedFiber.existsSectionWithCodimControlledDependenceLocus
