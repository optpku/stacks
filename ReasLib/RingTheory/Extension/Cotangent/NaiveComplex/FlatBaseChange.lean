module

public import Mathlib.RingTheory.Extension.Cotangent.BaseChange
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.RingTheory.Extension.Cotangent.NaiveComplex.Canonical
public import ReasLib.RingTheory.Extension.Cotangent.NaiveComplex.RestrictScalars

/-!
# Flat Base Change for Naive Cotangent Complexes

Source-ring base change is taken along a span `R → S` and `R → T`. It is distinct from
`NaiveCotangent.BaseChange`, which concerns
extension of scalars along a composable tower `R → S → T`.

The degreewise cotangent-space and conormal identifications are owned by
mathlib.  This file gives the chain-complex-level formulation and its
canonical self-presentation specialization.
-/

@[expose] public section

open CategoryTheory
open scoped TensorProduct

universe u v w

noncomputable section

namespace Algebra.Extension.NaiveCotangent.FlatBaseChange

variable {R : Type u} {S : Type v} {T : Type w}
variable [CommRing R] [CommRing S] [CommRing T]
variable [Algebra R S] [Algebra R T]

/-- The literal scalar extension to `T` of a presentation's naive cotangent complex after
viewing it as a complex of `R`-modules. -/
@[stacks 00S4 "flat source base change"]
noncomputable abbrev scalarExtension (P : Extension.{max u (max v w)} R S) :
    ChainComplex (ModuleCat.{max u (max v w)} T) ℕ :=
  ((ModuleCat.extendScalars (algebraMap R T)).mapHomologicalComplex (ComplexShape.down ℕ)).obj
    (restrictScalars P R)

/-- The naive cotangent complex of the base-changed presentation, viewed over the new source
ring `T`. -/
@[stacks 00S4 "base-changed presentation"]
noncomputable abbrev baseChanged (P : Extension.{max u (max v w)} R S) :
    ChainComplex (ModuleCat.{max u (max v w)} T) ℕ :=
  restrictScalars (P.baseChange (T := T)) T

/-- Flat base change identifies the literal scalar extension of a presentation's naive
cotangent complex with the naive cotangent complex of its base-changed presentation. -/
@[stacks 00S4 "flat source base change"]
theorem homotopyEquiv [Module.Flat R T] (P : Extension.{max u (max v w)} R S) :
    Nonempty <| HomotopyEquiv (scalarExtension (T := T) P) (baseChanged (T := T) P) := sorry

end Algebra.Extension.NaiveCotangent.FlatBaseChange

namespace Algebra.NaiveCotangent.FlatBaseChange

variable {R S T : Type u} [CommRing R] [CommRing S] [CommRing T]
variable [Algebra R S] [Algebra R T]

/-- The literal source-base-change complex for the canonical naive cotangent complex of `S`
over `R`. -/
@[stacks 00S4 "canonical flat source base change"]
noncomputable abbrev scalarExtension : ChainComplex (ModuleCat T) ℕ :=
  Extension.NaiveCotangent.FlatBaseChange.scalarExtension (T := T)
    (Algebra.Generators.self R S).toExtension

/-- The canonical naive cotangent complex of `T ⊗[R] S`, viewed as a complex of `T`-modules. -/
@[stacks 00S4 "canonical flat source base change"]
noncomputable abbrev canonical : ChainComplex (ModuleCat T) ℕ :=
  Extension.NaiveCotangent.restrictScalars
    (Algebra.Generators.self T (T ⊗[R] S)).toExtension T

/-- Flat source base change identifies the canonical naive cotangent complex after extension
from `R` to `T` with the canonical complex of `T ⊗[R] S`. -/
@[stacks 00S4 "flat base change"]
theorem homotopyEquiv [Module.Flat R T] :
    Nonempty <| HomotopyEquiv
      (scalarExtension (R := R) (S := S) (T := T))
      (canonical (R := R) (S := S) (T := T)) := sorry

end Algebra.NaiveCotangent.FlatBaseChange
