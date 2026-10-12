/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Fibered.Stack.InSetsOver.Forgetful
public import ReasLib.CategoryTheory.Fibered.Stack.InSetsOver.TwoFibreProduct.Pseudofunctor.Action
public import ReasLib.CategoryTheory.Fibered.Sets.TwoFibreProduct.Pseudofunctor.Action
import Mathlib.Tactic.CrossRefAttribute

/-!
# Forgetful computations for set-stack two-fibre-product actions

This leaf exposes the direct action through the setoid-stack, neutral set-fibred, based-functor,
and total-functor views used by downstream applications.
-/

@[expose] public section

noncomputable section

universe u v w vB

namespace CategoryTheory

open Bicategory
open scoped Bicategory

variable {C : Type u} [Category.{v} C]
variable {J : GrothendieckTopology C}

namespace StackOver.Sets.TwoFibreProduct

variable {S T : Bicategory.Cospan
  (StackOver.Sets.{u, v, max w (max u (max v vB)), max v vB} J)}

/-- Forgetting the pseudofunctor map to stacks in setoids gives the ambient action. -/
@[simp, stacks 0434 "set-stack two-fibre-product ambient action readout"]
theorem pseudofunctor.map.hom (psi : S ⟶ T) :
    ((pseudofunctor J).map psi).hom = (ambientPseudofunctor J).map psi := sorry

/-- The set-fibred `2`-cell underlying the direct two-fibre-product action. -/
@[stacks 0434 "set-stack two-fibre-product set-valued two-cell readout"]
noncomputable def map₂.toSets {psi phi : S ⟶ T} (Gamma : psi ⟶ phi) :=
  StackOver.Sets.Hom₂.toSetsNatTrans (map₂ Gamma)

/-- The based natural transformation underlying the direct two-fibre-product `2`-cell. -/
@[stacks 0434 "set-stack two-fibre-product based two-cell readout"]
noncomputable def map₂.toBased {psi phi : S ⟶ T} (Gamma : psi ⟶ phi) :=
  StackOver.Sets.Hom₂.toBasedNatTrans (map₂ Gamma)

/-- The ordinary natural transformation on total categories underlying the direct
two-fibre-product `2`-cell. -/
@[stacks 0434 "set-stack two-fibre-product ordinary two-cell readout"]
noncomputable def map₂.toNatTrans {psi phi : S ⟶ T} (Gamma : psi ⟶ phi) :=
  StackOver.Sets.Hom₂.toNatTrans (map₂ Gamma)

/-- The neutral set-fibred action has the same underlying based functor as the direct stack map. -/
@[stacks 0434 "set-stack two-fibre-product set-valued map readout"]
theorem map.toSets (psi : S ⟶ T) :
    FiberedCategoryOver.Sets.toBasedFunctor
        (StackOver.Sets.Hom.toSetsMor (map psi)) =
      FiberedCategoryOver.Sets.toBasedFunctor
        (FiberedCategoryOver.Sets.TwoFibreProduct.map
          ((Bicategory.Cospan.map
            (StackOver.Sets.toSets.pseudofunctor J).toPseudofunctor).map psi)) := sorry

/-- The based functor underlying the direct stack map is the based functor of its ambient
setoid-stack action. -/
@[stacks 0434 "set-stack two-fibre-product based map readout"]
theorem map.toBased (psi : S ⟶ T) :
    StackOver.Sets.Hom.toBasedFunctor (map psi) =
      StackOver.Setoids.Hom.toBasedFunctor
        ((ambientPseudofunctor J).map psi) := sorry

/-- The total functor underlying the direct stack map is the total functor of its ambient
setoid-stack action. -/
@[simp, stacks 0434 "set-stack two-fibre-product total map readout"]
theorem map.toTotal (psi : S ⟶ T) :
    StackOver.Sets.Hom.toFunctor (map psi) =
      StackOver.Setoids.Hom.toFunctor
        ((ambientPseudofunctor J).map psi) := sorry

end StackOver.Sets.TwoFibreProduct

end CategoryTheory
