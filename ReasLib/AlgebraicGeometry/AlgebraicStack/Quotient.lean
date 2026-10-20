module

public import ReasLib.AlgebraicGeometry.GroupScheme.Action
public import ReasLib.AlgebraicGeometry.GroupoidScheme.Action
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Groupoid.OfScheme
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Groupoid.Quotient.Small
public import ReasLib.AlgebraicGeometry.Scheme.Algebraic
public import ReasLib.AlgebraicGeometry.AlgebraicStack.Noetherian

/-!
# Quotient and classifying stacks of group schemes

The quotient of a group-scheme action is the stackification of its represented
action groupoid. The classifying stack is the quotient of the terminal scheme
by the trivial action.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicStack

/-- The quotient stack of a group scheme acting on a scheme over a field is the
stackification of the represented action groupoid. -/
def quotient {k : Type u} [Field k] (G : GroupScheme (Spec (.of k)))
    (X : GroupScheme.Action G) : GroupoidsOver (Spec (.of k)) :=
  GroupoidAlgebraicSpace.SmallQuotient.quotientStack
    (GroupoidAlgebraicSpace.ofScheme (GroupoidScheme.ofAction G X))

/-- The quotient of an action is the quotient stack of its represented action groupoid. -/
theorem quotient_spec {k : Type u} [Field k] (G : GroupScheme (Spec (.of k)))
    (X : GroupScheme.Action G) :
    quotient G X =
      GroupoidAlgebraicSpace.SmallQuotient.quotientStack
        (GroupoidAlgebraicSpace.ofScheme (GroupoidScheme.ofAction G X)) := rfl

/-- The classifying stack of a group scheme over a field is the quotient by its
trivial action on the terminal scheme over that field. -/
def classifying {k : Type u} [Field k] (G : GroupScheme (Spec (.of k))) :
    GroupoidsOver (Spec (.of k)) :=
  quotient G (GroupScheme.trivialAction G)

/-- The classifying stack is the quotient of the trivial action. -/
theorem classifying_spec {k : Type u} [Field k] (G : GroupScheme (Spec (.of k))) :
    classifying G = quotient G (GroupScheme.trivialAction G) := rfl

/-- The quotient stack of a finite-type group scheme action over a field is an
algebraic stack. -/
instance instAlgebraicStack_quotient {k : Type u} [Field k]
    (G : GroupScheme (Spec (.of k))) (X : GroupScheme.Action G)
    [Algebraic X.X] [Algebraic G.X] : AlgebraicStack (quotient G X) := sorry

/-- The quotient stack of a finite-type group scheme action over a field is
locally Noetherian. -/
instance instIsLocallyNoetherian_quotient {k : Type u} [Field k]
    (G : GroupScheme (Spec (.of k))) (X : GroupScheme.Action G)
    [Algebraic X.X] [Algebraic G.X] : IsLocallyNoetherian (quotient G X) := sorry

/-- The classifying stack of a finite-type group scheme over a field is an
algebraic stack. -/
instance instAlgebraicStack_classifying {k : Type u} [Field k]
    (G : GroupScheme (Spec (.of k))) [Algebraic G.X] :
    AlgebraicStack (classifying G) := sorry

/-- The classifying stack of a finite-type group scheme over a field is locally
Noetherian. -/
instance instIsLocallyNoetherian_classifying {k : Type u} [Field k]
    (G : GroupScheme (Spec (.of k))) [Algebraic G.X] :
    IsLocallyNoetherian (classifying G) := sorry

end AlgebraicGeometry.AlgebraicStack
