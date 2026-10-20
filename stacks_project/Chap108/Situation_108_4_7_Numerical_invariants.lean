module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.CohStack.Euler
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.CohStack.Numerical

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open CategoryTheory.Limits

universe u

/- Situation 108.4.7 (Numerical invariants) (1): Perfectness of the derived tensor-pushforward. -/
@[stacks 0DNC] #check (AlgebraicGeometry.AlgebraicSpace.CohStack.Obj.numericalPushforward_isPerfect :
    ∀ {S : Scheme.{u}} {X B : AlgebraicSpace S} {f : X ⟶ B}
      [FinitePresentation f] [Separated f] (x : CohStack.Obj f)
      {E : ModuleDerived X}, ModuleDerived.IsPerfect E →
      ModuleDerived.IsPerfect (x.numericalPushforward E))

/- Situation 108.4.7 (Numerical invariants) (2): Compatibility with arbitrary base change through the canonical comparison. -/
@[stacks 0DNC] #check (AlgebraicGeometry.AlgebraicSpace.CohStack.Obj.numericalBaseChangeMap_isIso :
    ∀ {S : Scheme.{u}} {X B : AlgebraicSpace S} {f : X ⟶ B}
      [FinitePresentation f] [Separated f] (x : CohStack.Obj f)
      (E : ModuleDerived X), ModuleDerived.IsPerfect E →
      ∀ {Y : AlgebraicSpace S} (g : Y ⟶ ofOver x.σ.left),
      IsIso (x.numericalBaseChangeMap E g))

/- Situation 108.4.7 (Numerical invariants) (3): Local constancy of the fiber Euler characteristic. -/
@[stacks 0DNC] #check (AlgebraicGeometry.AlgebraicSpace.CohStack.Obj.eulerChar_isLocallyConstant :
    ∀ {S : Scheme.{u}} {X B : AlgebraicSpace S} {f : X ⟶ B}
      [FinitePresentation f] [Separated f] (x : CohStack.Obj f)
      {E : ModuleDerived X}, ModuleDerived.IsPerfect E → IsLocallyConstant (x.eulerChar E))

/- Situation 108.4.7 (Numerical invariants) (4): Membership is equality with P at every index and every point. -/
@[stacks 0DNC] #check (AlgebraicGeometry.AlgebraicSpace.CohStack.Numerical.mem_iff :
    ∀ {S : Scheme.{u}} {X B : AlgebraicSpace S} {f : X ⟶ B}
      [FinitePresentation f] [Separated f] {I : Type u} (E : I → ModuleDerived X)
      (P : I → ℤ) (x : CohStack.Obj f),
      CohStack.numerical f E P x ↔ ∀ i t, x.eulerChar (E i) t = P i)

/- The invariant also equals the Euler characteristic of the fiberwise tensor. -/
#check (AlgebraicGeometry.AlgebraicSpace.CohStack.Obj.eulerChar_eq_fibreTensor :
    ∀ {S : Scheme.{u}} {X B : AlgebraicSpace S} {f : X ⟶ B}
      [FinitePresentation f] (x : CohStack.Obj f) (E : ModuleDerived X),
      ModuleDerived.IsPerfect E → ∀ (t : FieldValuedPoint (ofOver x.σ.left)),
      x.eulerChar E (Points.mk t) =
        ModuleDerived.fiberEulerChar (x.fibreTensorPushforward E t)
          (Points.mk (FieldValuedPoint.of t.K t.structureHom (𝟙 (ofOver t.overObj)))))

/- The prescribed numerical invariants define a full groupoid fibration. -/
#check (AlgebraicGeometry.AlgebraicSpace.CohStack.toGroupoidsNumerical :
    ∀ {S : Scheme.{u}} {X B : AlgebraicSpace S} (f : X ⟶ B)
      [FinitePresentation f] {I : Type u} (E : I → ModuleDerived X) (P : I → ℤ),
      (∀ i, ModuleDerived.IsPerfect (E i)) →
      FiberedCategoryOver.Groupoids.{u + 1, u, u + 1, u + 1} (Over S))
