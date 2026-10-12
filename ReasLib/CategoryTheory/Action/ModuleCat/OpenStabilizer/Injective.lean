/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Action.ModuleCat.Cofree.Injective
public import ReasLib.CategoryTheory.Action.ModuleCat.OpenStabilizer.Coreflection

/-!
# Functorial injective embeddings for discrete continuous module actions

The cofree adjunction supplies functorial injective embeddings in the algebraic action category.
The open-stabilizer coreflection then transfers them to the full subcategory of discrete
continuous module actions.
-/

@[expose] public section

open CategoryTheory Limits
open scoped Topology

universe u v

namespace CategoryTheory.Action.ModuleCat.DiscreteModuleCat

variable (R : Type u) [Ring R]
variable (G : Type v) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- The category of discrete `R`-modules with continuous `G`-action has functorial injective
embeddings. -/
@[stacks 04JF]
noncomputable instance hasFunctorialInjectives :
    HasFunctorialInjectives
      (Action.ModuleCat.DiscreteModuleCat R G) :=
  HasFunctorialInjectives.of_rightAdjoint
    (OpenStabilizer.adjunction R G) (OpenStabilizer.isZero_of_inclusion_obj_isZero R G)

end CategoryTheory.Action.ModuleCat.DiscreteModuleCat
