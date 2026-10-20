/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Spec
public import Mathlib.RingTheory.Noetherian.Defs
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Coherent
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.FunctorOfPoints
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Proper
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Coherent.Category
import StacksCheckRecall

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace CategoryTheory

universe u

section

variable {A : Type u} [CommRing A] [IsNoetherianRing A] (I : Ideal A)
variable (X : AlgebraicSpace (Spec (CommRingCat.of A)))
variable (f : X ⟶ ofOver (Over.mk (𝟙 (Spec (CommRingCat.of A))))) [Proper f]
variable (F : X.Modules) [F.IsCoherent]

/- Situation 69.22.1: `A` is a Noetherian ring, `I` is an ideal of `A`,
`f : X ⟶ Spec(A)` is a proper morphism of algebraic spaces, and `F` is a coherent
sheaf on `X`. -/
@[stacks 08AV] #check (AlgebraicGeometry.AlgebraicSpace.Proper :
  (X ⟶ AlgebraicGeometry.AlgebraicSpace.ofOver
    (Over.mk (𝟙 (Spec (CommRingCat.of A))))) → Prop)

/- Assumption (1): `A` is a Noetherian ring. -/
#check (inferInstance : IsNoetherianRing A)

/- Assumption (2): `I ⊂ A` is an ideal. -/
#check (I : Ideal A)

/- Assumption (3): `f : X ⟶ Spec(A)` is a proper morphism of algebraic spaces. -/
#check (f : X ⟶ ofOver (Over.mk (𝟙 (Spec (CommRingCat.of A)))))
#check (inferInstance : Proper f)

/- Assumption (4): `F` is a coherent sheaf on `X`. -/
#check (inferInstance : F.IsCoherent)

end
