module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Flat.Locus
import StacksCheckRecall

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme.Modules

/-
Theorem 37.15.1: If `f : X ⟶ S` is locally of finite presentation and `ℱ` is a
finitely presented module on `X`, then the locus where `ℱ` is flat over `S` is open.
-/
@[stacks 0399]
#check (AlgebraicGeometry.Scheme.Modules.isOpen_flatOverAt :
  ∀ {X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFinitePresentation f]
    (ℱ : X.Modules) [ℱ.IsFinitePresentation],
    IsOpen {x : X | flatOverAt ℱ f x})

end AlgebraicGeometry.Scheme.Modules
