module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.FunctorOfPoints
public import ReasLib.AlgebraicGeometry.Scheme.PreRelation.QuotientSheaf
public import ReasLib.AlgebraicGeometry.Scheme.EtaleEquivalenceRelation
public import ReasLib.AlgebraicGeometry.Scheme.Coproduct.Over

/-!
# Algebraic-space quotients of étale equivalence relations

The small étale quotient sheaf of a scheme étale equivalence relation defines an
algebraic space with a canonical quotient projection.
-/

@[expose] public section

open CategoryTheory Opposite

noncomputable section

universe u v

namespace AlgebraicGeometry.Scheme.PreRelation

variable {S : Scheme.{u}} {U : Over S}

/-- The small étale quotient sheaf of an étale equivalence relation on a scheme
is an algebraic space. -/
instance instIsAlgebraicSpaceSmallEtaleQuotientSheaf (P : PreRelation U)
    [P.IsEtaleEquivalenceRelation] :
    AlgebraicSpace.IsAlgebraicSpace P.smallEtaleQuotientSheaf.obj := sorry

/-- The algebraic space whose functor of points is the small étale quotient sheaf
of a scheme étale equivalence relation. -/
def etaleQuotientSpace (P : PreRelation U) [P.IsEtaleEquivalenceRelation] :
    AlgebraicSpace S :=
  AlgebraicSpace.ofIsAlgebraicSpace P.smallEtaleQuotientSheaf.obj

/-- The functor of points of the étale quotient space is the small étale quotient sheaf. -/
@[simp]
theorem etaleQuotientSpace_functorOfPoints (P : PreRelation U)
    [P.IsEtaleEquivalenceRelation] :
    P.etaleQuotientSpace.functorOfPoints = P.smallEtaleQuotientSheaf.obj := rfl

/-- The canonical projection from a scheme to the algebraic-space quotient of
an étale equivalence relation on it. -/
def etaleQuotientMap (P : PreRelation U) [P.IsEtaleEquivalenceRelation] :
    AlgebraicSpace.ofOver U ⟶ P.etaleQuotientSpace :=
  P.smallEtaleQuotientSheafMk

/-- On scheme-valued points the algebraic-space quotient projection is the
canonical map into the small étale quotient sheaf. -/
@[simp]
theorem etaleQuotientMap_app (P : PreRelation U) [P.IsEtaleEquivalenceRelation]
    {T : Over S} (a : T ⟶ U) :
    P.etaleQuotientMap.app (op T) a = P.smallEtaleQuotientSheafMk.app (op T) a := rfl

/-- The canonical morphism from a coproduct summand to the algebraic-space
quotient of an étale equivalence relation on the coproduct. -/
def etaleQuotientSummand {I : Type v} [Small.{u} I] (Mi : I → Over S)
    (P : PreRelation (Scheme.Coproduct.overMk Mi)) [P.IsEtaleEquivalenceRelation]
    (i : I) : AlgebraicSpace.ofOver (Mi i) ⟶ P.etaleQuotientSpace :=
  yoneda.map (Scheme.Coproduct.overι Mi i) ≫ P.etaleQuotientMap

/-- On scheme-valued points the quotient summand map takes the quotient class
after composing with the coproduct inclusion. -/
@[simp]
theorem etaleQuotientSummand_app {I : Type v} [Small.{u} I] (Mi : I → Over S)
    (P : PreRelation (Scheme.Coproduct.overMk Mi)) [P.IsEtaleEquivalenceRelation]
    (i : I) {T : Over S} (a : T ⟶ Mi i) :
    (etaleQuotientSummand Mi P i).app (op T) a =
      P.smallEtaleQuotientSheafMk.app (op T) (a ≫ Scheme.Coproduct.overι Mi i) := rfl

end AlgebraicGeometry.Scheme.PreRelation
