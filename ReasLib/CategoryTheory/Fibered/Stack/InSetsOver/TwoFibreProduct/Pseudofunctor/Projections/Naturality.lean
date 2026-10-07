module

public import ReasLib.CategoryTheory.Fibered.Stack.InSetsOver.TwoFibreProduct.Pseudofunctor.Projections.Construction
import Mathlib.Tactic.CrossRefAttribute

/-!
# Naturality computations for set-stack two-fibre-product projections

The formulas here expose both directions of the projection naturality isomorphisms after
forgetting the proof-bearing set-stack endpoints.
-/

@[expose] public section

noncomputable section

universe u v w vB

namespace CategoryTheory

open Bicategory
open scoped Bicategory Pseudofunctor.StrongTrans

variable {C : Type u} [Category.{v} C]
variable {J : GrothendieckTopology C}

namespace StackOver.Sets.TwoFibreProduct

variable {S T : Bicategory.Cospan
  (StackOver.Sets.{u, v, max w (max u (max v vB)), max v vB} J)}

/-- The forward first-projection naturality cell forgets to the ambient forward cell. -/
@[simp, stacks 0434 "set-stack first projection forward naturality readout"]
theorem pseudofunctor.fst.naturality.hom.toAmbient (psi : S ⟶ T) :
    HEq (((pseudofunctor.fst J).naturality psi).hom.hom)
      ((pseudofunctor.fst.ambient J).naturality psi).hom := sorry

/-- The inverse first-projection naturality cell forgets to the ambient inverse cell. -/
@[simp, stacks 0434 "set-stack first projection inverse naturality readout"]
theorem pseudofunctor.fst.naturality.inv.toAmbient (psi : S ⟶ T) :
    HEq (((pseudofunctor.fst J).naturality psi).inv.hom)
      ((pseudofunctor.fst.ambient J).naturality psi).inv := sorry

/-- The forward second-projection naturality cell forgets to the ambient forward cell. -/
@[simp, stacks 0434 "set-stack second projection forward naturality readout"]
theorem pseudofunctor.snd.naturality.hom.toAmbient (psi : S ⟶ T) :
    HEq (((pseudofunctor.snd J).naturality psi).hom.hom)
      ((pseudofunctor.snd.ambient J).naturality psi).hom := sorry

/-- The inverse second-projection naturality cell forgets to the ambient inverse cell. -/
@[simp, stacks 0434 "set-stack second projection inverse naturality readout"]
theorem pseudofunctor.snd.naturality.inv.toAmbient (psi : S ⟶ T) :
    HEq (((pseudofunctor.snd J).naturality psi).inv.hom)
      ((pseudofunctor.snd.ambient J).naturality psi).inv := sorry

end StackOver.Sets.TwoFibreProduct

end CategoryTheory
