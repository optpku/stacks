module

public import Mathlib.CategoryTheory.Abelian.Subobject
public import Mathlib.CategoryTheory.ObjectProperty.Small
public import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Quotient Representatives in Abelian Categories

For a family of source objects, cokernels of their subobjects form a canonical family of strict
representatives for all quotients.  The iso-closure API lets consumers classify arbitrary epic
images without choosing kernels or cokernel comparisons in each application.
-/

open CategoryTheory.Limits

universe w t v u

namespace CategoryTheory.ObjectProperty

variable {C : Type u} [Category.{v} C] [Abelian C]
variable {alpha : Type t}

/-- The strict representatives obtained as cokernels of subobjects of a family of source
objects. -/
@[stacks 079E "quotient representatives"]
noncomputable def quotientRepresentatives (S : alpha → C) : ObjectProperty C :=
  ObjectProperty.ofObj
    (fun p : (Sigma fun a : alpha ↦ Subobject (S a)) ↦ cokernel p.2.arrow)

namespace QuotientRepresentatives

/-- The cokernel of a subobject of a source object belongs to its quotient representative
family. -/
theorem cokernel_mem (S : alpha → C) (a : alpha) (K : Subobject (S a)) :
    quotientRepresentatives S (cokernel K.arrow) := sorry

/-- Quotient representatives of a small family with small subobject lattices form a small object
property. -/
instance small (S : alpha → C)
    [Small.{w} (Sigma fun a : alpha ↦ Subobject (S a))] :
    ObjectProperty.Small.{w} (quotientRepresentatives S) := sorry

/-- The target of an epimorphism from a member of the source family lies in the isomorphism
closure of its quotient representatives. -/
theorem mem_isoClosure_of_epi (S : alpha → C) (a : alpha) {M : C}
    (f : S a ⟶ M) [Epi f] :
    (quotientRepresentatives S).isoClosure M := sorry

end QuotientRepresentatives

end CategoryTheory.ObjectProperty
