module

public import Mathlib.CategoryTheory.Generator.Abelian
import Mathlib.Tactic.CrossRefAttribute

/-!
# Injective coseparators

An injective coseparator packages the two properties commonly needed by duality arguments:
morphisms into the chosen object detect maps, and maps into it extend across monomorphisms.  The
package is deliberately an explicit parameter, since an injective coseparator is not canonical.
-/

@[expose] public section

open CategoryTheory.Limits

universe v u

namespace CategoryTheory

variable (C : Type u) [Category.{v} C]

/-- An object which is both injective and a coseparator. -/
@[stacks 01DQ "dualizing injective target"]
structure InjectiveCoseparator where
  /-- The underlying object. -/
  obj : C
  /-- The underlying object is injective. -/
  injective : Injective obj
  /-- Morphisms into the underlying object detect equality. -/
  isCoseparator : IsCoseparator obj

attribute [instance] InjectiveCoseparator.injective

/-- A complete abelian category with enough injectives and a separator admits an injective
coseparator. -/
@[stacks 01DQ "existence from a separator"]
theorem nonempty_injectiveCoseparator [Abelian C] [HasLimits C] [EnoughInjectives C]
    (G : C) (hG : IsSeparator G) :
    Nonempty (InjectiveCoseparator C) := sorry

/-- A complete abelian category with enough injectives and a chosen separator admits an
injective coseparator. -/
theorem nonempty_injectiveCoseparator_of_hasSeparator [Abelian C] [HasLimits C]
    [EnoughInjectives C] [HasSeparator C] :
    Nonempty (InjectiveCoseparator C) := sorry

end CategoryTheory
