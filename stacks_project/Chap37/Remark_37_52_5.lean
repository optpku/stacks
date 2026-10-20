module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Fiber.ClosedPoint.Specialization.Chain
import StacksCheckRecall

@[expose] public section

open CategoryTheory
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Hom

/- Remark 37.52.5: a locally finite-type morphism admits an avoidant chain of immediate
specializations in a fibre, ending at a closed point and specializing to a prescribed closed
fibre point. -/
@[stacks 053V]
#check (AlgebraicGeometry.Scheme.Hom.exists_immediateSpecializationChain_avoiding :
  ∀ {X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFiniteType f] (x x' : X)
    (hxx' : Specializes x x')
    (hx'_closed : f.asFiber x' ∈ closedPoints (f.fiber (f x')))
    (Z : Set (f.fiber (f x))) (hZ : IsClosed Z)
    (hxZ : f.asFiber x ∉ Z),
    ∃ chain : Fin (f.residueFieldTrdegAt x + 1) → f.fiber (f x),
      chain 0 = f.asFiber x ∧
        (∀ i : Fin (f.residueFieldTrdegAt x),
          IsImmediateSpecialization (chain i.castSucc) (chain i.succ)) ∧
        chain (Fin.last (f.residueFieldTrdegAt x)) ∈
          closedPoints (f.fiber (f x)) ∧
          Specializes (f.fiberι (f x) (chain (Fin.last (f.residueFieldTrdegAt x)))) x' ∧
          ∀ i : Fin (f.residueFieldTrdegAt x + 1), chain i ∉ Z)

/- The closure of the distinguished fibre point has topological Krull dimension equal to its
residue-field transcendence degree. -/
#check (AlgebraicGeometry.Scheme.Hom.topologicalKrullDim_closure_asFiber_eq_residueFieldTrdegAt :
  ∀ {X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFiniteType f] (x : X),
    topologicalKrullDim (closure ({f.asFiber x} : Set (f.fiber (f x)))) =
      (f.residueFieldTrdegAt x : WithBot ℕ∞))

end AlgebraicGeometry.Scheme.Hom
