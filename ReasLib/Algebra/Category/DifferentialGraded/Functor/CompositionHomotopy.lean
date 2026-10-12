/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Category.DifferentialGraded.Functor.Composition
public import ReasLib.Algebra.Category.DifferentialGraded.Functor.Homotopy
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Composition of the Functors Induced by Differential Graded Functors

This leaf records how strict identity and composition of differential graded
functors act on closed degree-zero morphisms and on their homotopy categories.
It keeps those functoriality formulas separate from the construction of the
individual induced functors.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u v w z

namespace DifferentialGradedCategory

variable {R : Type u} [CommRing R]
variable {A : Type v} {B : Type w} {C : Type z}
variable [DA : DifferentialGradedCategory R A]
variable [DB : DifferentialGradedCategory R B]
variable [DC : DifferentialGradedCategory R C]

namespace DgFunctor

/-- The identity DG functor acts identically on closed degree-zero morphisms. -/
@[simp, stacks 09L6 "identity DG functor on closed morphisms"]
theorem id_mapCompHom {X Y : A} (f : CompHom X Y) :
    mapCompHom (id R A) f = f := sorry

/-- The action of a composite DG functor on a closed degree-zero morphism is successive action. -/
@[simp, stacks 09L6 "composition of DG functors on closed morphisms"]
theorem comp_mapCompHom (G : DgFunctor R B C) (F : DgFunctor R A B)
    {X Y : A} (f : CompHom X Y) :
    mapCompHom (G.comp F) f = mapCompHom G (mapCompHom F f) := sorry

/-- The functor on closed degree-zero morphisms induced by the identity DG functor is the identity. -/
@[simp, stacks 09L6 "identity DG functor on the closed category"]
theorem id_mapComp : mapComp (id R A) = 𝟭 (Comp R A) := sorry

/-- The functor on closed degree-zero morphisms induced by a composite DG functor is a composite. -/
@[simp, stacks 09L6 "composition of induced functors on the closed category"]
theorem comp_mapComp (G : DgFunctor R B C) (F : DgFunctor R A B) :
    mapComp (G.comp F) = mapComp F ⋙ mapComp G := sorry

/-- The identity DG functor acts identically on every homotopy class. -/
@[simp, stacks 09L8 "identity DG functor on homotopy classes"]
theorem id_mapHomotopyClass {X Y : A} (f : HomotopyClass X Y) :
    mapHomotopyClass (id R A) f = f := sorry

/-- The action of a composite DG functor on a homotopy class is successive action. -/
@[simp, stacks 09L8 "composition of DG functors on homotopy classes"]
theorem comp_mapHomotopyClass (G : DgFunctor R B C) (F : DgFunctor R A B)
    {X Y : A} (f : HomotopyClass X Y) :
    mapHomotopyClass (G.comp F) f =
      mapHomotopyClass G (mapHomotopyClass F f) := sorry

/-- The functor on the homotopy category induced by the identity DG functor is the identity. -/
@[simp, stacks 09L8 "identity DG functor on the homotopy category"]
theorem id_mapK : mapK (id R A) = 𝟭 (K R A) := sorry

/-- The functor on the homotopy category induced by a composite DG functor is a composite. -/
@[simp, stacks 09L8 "composition of induced functors on the homotopy category"]
theorem comp_mapK (G : DgFunctor R B C) (F : DgFunctor R A B) :
    mapK (G.comp F) = mapK F ⋙ mapK G := sorry

end DgFunctor

end DifferentialGradedCategory
