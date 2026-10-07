module

public import Mathlib.RingTheory.Extension.Cotangent.Basic
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Finite generator families with free conormal module

This file bundles a finite family of algebra generators whose associated
conormal module `I / I²` is free.  The owner is independent of any particular
localization or smoothing construction.
-/

@[expose] public section

universe u v w

namespace Algebra

variable (R : Type u) (S : Type v)
variable [CommRing R] [CommRing S] [Algebra R S]

/-- A finite family of algebra generators whose conormal module is free. -/
@[stacks 07CE "finite generators with free cotangent module"]
structure FreeCotangentGenerators where
  /-- The type indexing the chosen algebra generators. -/
  index : Type w
  /-- The chosen generator family is finite. -/
  [finiteIndex : Finite index]
  /-- The chosen finite family of algebra generators. -/
  generators : Generators R S index
  /-- The conormal module of the chosen generators is free. -/
  [freeCotangent : Module.Free S generators.toExtension.Cotangent]

attribute [instance] FreeCotangentGenerators.finiteIndex
attribute [instance] FreeCotangentGenerators.freeCotangent

namespace FreeCotangentGenerators

/-- Bundle a finite family of generators with free conormal module. -/
@[stacks 07CE "finite free cotangent generators constructor"]
def of {ι : Type w} [Finite ι] (P : Generators R S ι)
    [Module.Free S P.toExtension.Cotangent] :
    FreeCotangentGenerators.{u, v, w} R S where
  index := ι
  finiteIndex := inferInstance
  generators := P
  freeCotangent := inferInstance

/-- The generator family supplied to `FreeCotangentGenerators.of` is recovered by projection. -/
@[simp]
theorem generators_of {ι : Type w} [Finite ι] (P : Generators R S ι)
    [Module.Free S P.toExtension.Cotangent] :
    (FreeCotangentGenerators.of R S P).generators = P := sorry

/-- Free cotangent generators expose their finiteness and conormal freeness together. -/
theorem spec (P : FreeCotangentGenerators.{u, v, w} R S) :
    Finite P.index ∧ Module.Free S P.generators.toExtension.Cotangent := sorry

/-- The finite generator family can be reindexed by an initial finite type. -/
theorem exists_finReindex (P : FreeCotangentGenerators.{u, v, w} R S) :
    ∃ (n : ℕ) (e : Fin n ≃ P.index),
      Module.Free S (P.generators.reindex e).toExtension.Cotangent := sorry

end FreeCotangentGenerators

end Algebra
