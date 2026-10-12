/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Galois.IsFundamentalgroup
public import Mathlib.CategoryTheory.Galois.Topology
public import Mathlib.CategoryTheory.Action.Concrete
public import Mathlib.CategoryTheory.Action.Continuous
public import Mathlib.Topology.Category.FinTopCat

@[expose] public section

open CategoryTheory
open scoped FintypeCatDiscrete

universe u

namespace CategoryTheory.DiscreteContAction

variable (G : Type u) [Group G] [TopologicalSpace G]

/-- The finite-type-valued forgetful functor on finite discrete continuous `G`-actions. -/
def forgetFintype : DiscreteContAction FintypeCat.{u} G ⥤ FintypeCat.{u} :=
  ObjectProperty.ι _ ⋙ ObjectProperty.ι _ ⋙ Action.forget FintypeCat G

/-- The set-valued view of `forgetFintype`. -/
def forgetType : DiscreteContAction FintypeCat.{u} G ⥤ Type u :=
  forgetFintype G ⋙ FintypeCat.incl

/-- The underlying action on the finite fiber of a discrete continuous action. -/
instance (X : DiscreteContAction FintypeCat.{u} G) :
    MulAction G ((forgetFintype G).obj X) :=
  inferInstanceAs (MulAction G X.obj.obj.V)

/-- The canonical action on the fibers of `forgetFintype` is natural. -/
instance forgetFintypeIsNaturalSMul :
    PreGaloisCategory.IsNaturalSMul (forgetFintype G) G := sorry

/-- The continuous action homomorphism from `G` to the automorphism group of its finite
discrete continuous fiber functor. -/
def toAut [IsTopologicalGroup G] : G →ₜ* Aut (forgetFintype G) :=
  { PreGaloisCategory.toAut (forgetFintype G) G with
    continuous_toFun := sorry }

/-- The component of `toAut` at a finite discrete continuous action is its given `G`-action. -/
theorem toAut_hom_app_apply [IsTopologicalGroup G] (g : G)
    (X : DiscreteContAction FintypeCat.{u} G) (x : (forgetFintype G).obj X) :
    (toAut G g).hom.app X x = g • x := sorry

end CategoryTheory.DiscreteContAction
