/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.FiniteEtale
public import Mathlib.AlgebraicGeometry.Sites.EtalePoint
public import Mathlib.CategoryTheory.FintypeCat

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme.FiniteEtale

/-- The forgetful functor from finite étale schemes over a scheme to étale schemes over it. -/
abbrev toEtale (X : Scheme.{u}) : FiniteEtale X ⥤ X.Etale :=
  MorphismProperty.Over.changeProp X inf_le_right le_rfl

variable {X : Scheme.{u}} {K : Type u} [Field K] [IsAlgClosed K]

/-- The set-valued geometric-fiber functor at a specified geometric point. -/
noncomputable def fiber (point : Spec (.of K) ⟶ X) : FiniteEtale X ⥤ Type u :=
  toEtale X ⋙ (Scheme.pointSmallEtale point).fiber

/-- The geometric fiber of a finite étale scheme is finite. -/
instance fiber_obj_finite (point : Spec (.of K) ⟶ X) (Y : FiniteEtale X) :
    Finite ((fiber point).obj Y) := sorry

/-- The geometric-fiber functor lifted to the category of finite sets. -/
noncomputable def finiteFiber (point : Spec (.of K) ⟶ X) : FiniteEtale X ⥤ FintypeCat.{u} :=
  ObjectProperty.lift Finite (fiber point) (fiber_obj_finite point)

/-- The finite-set lift retains the canonical étale-point fiber carrier. -/
theorem finiteFiber_obj (point : Spec (.of K) ⟶ X) (Y : FiniteEtale X) :
    ((finiteFiber point).obj Y).obj =
      (Scheme.pointSmallEtale point).fiber.obj ((toEtale X).obj Y) := sorry

/-- The finite-set lift acts on geometric fibers by the canonical étale-point map. -/
theorem finiteFiber_map_apply (point : Spec (.of K) ⟶ X)
    {Y Z : FiniteEtale X} (morphism : Y ⟶ Z) (element : (fiber point).obj Y) :
    ((finiteFiber point).map morphism) element =
      (Scheme.pointSmallEtale point).fiber.map ((toEtale X).map morphism) element := sorry

end AlgebraicGeometry.Scheme.FiniteEtale
