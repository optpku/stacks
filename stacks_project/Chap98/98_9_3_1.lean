module

public import stacks_project.Chap94.Definition_94_12_1_Representable
public import stacks_project.Chap98.Lemma_98_9_3_FormalObject
public import stacks_project.Chap98.Definition_98_9_1_Hom
public import stacks_project.Chap98.«98_9_3_1_Approximation»
import Mathlib.Tactic.CrossRefAttribute

/-!
# Approximation of objects by formal objects

Stacks tag 07X6: restricting an object of a category fibred in groupoids over
`(Sch/S)_fppf` along `Spec(R ⧸ m^{n+1}) ⟶ Spec(R)` yields a formal object, and
this construction is functorial.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.GroupoidsOver

variable {S : Scheme.{u}} [IsLocallyNoetherian S]

/-- 98.9.3.1: the functor sending an object `x` of `X` over `Spec(R)`, where `R`
is a Noetherian complete local `S`-algebra with `R ⧸ m` of finite type over `S`,
to the formal object of restrictions `x` along `Spec(R ⧸ m^{n+1}) ⟶ Spec(R)`.
The source is the full subcategory of such objects of `X`, and the target is the
category of formal objects of `X`. Lean stage `n` lies over `Spec(R ⧸ m^{n+1})`,
matching the Stacks object `ξ_{n+1}`. -/
@[stacks 07X6]
noncomputable def approximation (X : GroupoidsOver S) :
    CompleteLocalObject X ⥤ FormalObject X :=
  FormalObject.approximation

/-- The labeled approximation functor sends an object over `Spec(R)` to the
formal object of its restrictions along `Spec(R ⧸ m^{n+1}) ⟶ Spec(R)`. -/
theorem approximation_obj {X : GroupoidsOver S} (x : CompleteLocalObject X) :
    (approximation X).obj x = FormalObject.restriction x :=
  sorry

end AlgebraicGeometry.GroupoidsOver
