module

public import ReasLib.CategoryTheory.Action.ModuleCat.OpenStabilizer.Definition

/-!
# The open-stabilizer submodule

For an algebraic `R`-linear action of a topological group, the elements with open stabilizer form
a canonical invariant submodule.  This is the concrete object underlying the open-stabilizer
coreflection.
-/

@[expose] public section

open CategoryTheory Limits
open scoped Topology

universe u v

namespace CategoryTheory.Action.ModuleCat.OpenStabilizer

variable (R : Type u) [Ring R]
variable (G : Type v) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- The zero element of a linear action has open stabilizer. -/
theorem isOpen_stabilizer_zero (X : Action (ModuleCat.{max u v} R) G) :
    IsOpen (MulAction.stabilizer G (0 : X.V) : Set G) := sorry

/-- A sum of elements with open stabilizers has open stabilizer. -/
theorem isOpen_stabilizer_add {X : Action (ModuleCat.{max u v} R) G} {x y : X.V}
    (hx : IsOpen (MulAction.stabilizer G x : Set G))
    (hy : IsOpen (MulAction.stabilizer G y : Set G)) :
    IsOpen (MulAction.stabilizer G (x + y) : Set G) := sorry

/-- An `R`-multiple of an element with open stabilizer has open stabilizer. -/
theorem isOpen_stabilizer_smul {X : Action (ModuleCat.{max u v} R) G} (r : R) {x : X.V}
    (hx : IsOpen (MulAction.stabilizer G x : Set G)) :
    IsOpen (MulAction.stabilizer G (r • x) : Set G) := sorry

/-- A translate of an element with open stabilizer has open stabilizer. -/
theorem isOpen_stabilizer_action {X : Action (ModuleCat.{max u v} R) G} (g : G) {x : X.V}
    (hx : IsOpen (MulAction.stabilizer G x : Set G)) :
    IsOpen (MulAction.stabilizer G (g • x) : Set G) := sorry

/-- An equivariant linear map sends elements with open stabilizer to elements with open
stabilizer. -/
theorem isOpen_stabilizer_map {X Y : Action (ModuleCat.{max u v} R) G} (f : X ⟶ Y)
    {x : X.V} (hx : IsOpen (MulAction.stabilizer G x : Set G)) :
    IsOpen (MulAction.stabilizer G (f.hom.hom x) : Set G) := sorry

/-- The `R`-submodule of elements whose stabilizer is open. -/
@[stacks 04JF "open-stabilizer submodule"]
def submodule (X : Action (ModuleCat.{max u v} R) G) : Submodule R X.V where
  carrier := {x | IsOpen (MulAction.stabilizer G x : Set G)}
  zero_mem' := isOpen_stabilizer_zero R G X
  add_mem' := isOpen_stabilizer_add R G
  smul_mem' := isOpen_stabilizer_smul R G

/-- Membership in the open-stabilizer submodule. -/
@[simp]
theorem mem_submodule (X : Action (ModuleCat.{max u v} R) G) (x : X.V) :
    x ∈ submodule R G X ↔ IsOpen (MulAction.stabilizer G x : Set G) := sorry

/-- The action of a group element restricted to the open-stabilizer submodule. -/
@[stacks 04JF "restricted action map"]
def actionHom (X : Action (ModuleCat.{max u v} R) G) (g : G) :
    End (ModuleCat.of R (submodule R G X)) :=
  ModuleCat.ofHom <|
    LinearMap.codRestrict (submodule R G X)
      ((X.ρ g).hom.domRestrict (submodule R G X))
      fun x ↦ isOpen_stabilizer_action R G g x.2

/-- The restricted action sends the identity of `G` to the identity morphism. -/
theorem actionHom_one (X : Action (ModuleCat.{max u v} R) G) :
    actionHom R G X 1 = 𝟙 _ := sorry

/-- Restricting the action is compatible with multiplication in `G`. -/
theorem actionHom_mul (X : Action (ModuleCat.{max u v} R) G) (g h : G) :
    actionHom R G X (g * h) = actionHom R G X g * actionHom R G X h := sorry

/-- The action of `G` restricts to the open-stabilizer submodule. -/
def action (X : Action (ModuleCat.{max u v} R) G) :
    Action (ModuleCat.{max u v} R) G where
  V := ModuleCat.of R (submodule R G X)
  ρ :=
    { toFun := actionHom R G X
      map_one' := actionHom_one R G X
      map_mul' := actionHom_mul R G X }

/-- Restricting the action to the open-stabilizer submodule does not change stabilizers. -/
theorem stabilizer_action (X : Action (ModuleCat.{max u v} R) G)
    (x : (action R G X).V) :
    MulAction.stabilizer G x = MulAction.stabilizer G x.1 := sorry

/-- An equivariant map restricts to a linear map between open-stabilizer submodules. -/
def map {X Y : Action (ModuleCat.{max u v} R) G} (f : X ⟶ Y) :
    submodule R G X →ₗ[R] submodule R G Y :=
  LinearMap.codRestrict (submodule R G Y)
    (f.hom.hom.domRestrict (submodule R G X))
    fun x ↦ isOpen_stabilizer_map R G f x.2

/-- The restricted linear map is the ambient equivariant map on underlying elements. -/
@[simp]
theorem map_apply {X Y : Action (ModuleCat.{max u v} R) G} (f : X ⟶ Y)
    (x : submodule R G X) : (map R G f x).1 = f.hom.hom x.1 := sorry

/-- A restricted equivariant map commutes with every restricted group action. -/
theorem actionHom_naturality {X Y : Action (ModuleCat.{max u v} R) G}
    (f : X ⟶ Y) (g : G) :
    actionHom R G X g ≫ ModuleCat.ofHom (map R G f) =
      ModuleCat.ofHom (map R G f) ≫ actionHom R G Y g := sorry

/-- An equivariant map induces a morphism between the restricted open-stabilizer actions. -/
def actionMap {X Y : Action (ModuleCat.{max u v} R) G} (f : X ⟶ Y) :
    action R G X ⟶ action R G Y where
  hom := ModuleCat.ofHom (map R G f)
  comm := actionHom_naturality R G f

end CategoryTheory.Action.ModuleCat.OpenStabilizer
