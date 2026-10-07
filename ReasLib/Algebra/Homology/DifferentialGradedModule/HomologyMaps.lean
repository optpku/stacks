module

public import ReasLib.Algebra.Homology.CochainComplex.Cokernel
public import ReasLib.Algebra.Homology.DifferentialGradedModule.Forget
public import ReasLib.Algebra.Homology.HomologicalComplex.HomologyMaps

/-!
# Cycles and differential-cokernel maps of DG-module morphisms

This leaf lifts two recurring degreewise conditions from the underlying cochain complex to the
public right-DG-module API.
@stack 0653
-/

@[expose] public section

noncomputable section

universe u v

open CategoryTheory

namespace DifferentialGradedModule.Hom

variable {R : Type u} [CommRing R]
variable {A : CochainDGAlgebra.{u, v} R}

/-- The map on cycles in degree `n` induced by a right-DG-module morphism. -/
abbrev cyclesMap {M N : DifferentialGradedModule.{u, v} A} (f : M ⟶ N) (n : ℤ) :=
  HomologicalComplex.cyclesMap f.toCochainMap n

/-- A right-DG-module morphism is epic on cycles when its underlying cochain map is epic on
cycles. -/
@[stacks 0FSE "epimorphic on cycles for DG-module morphisms"]
abbrev EpiOnCycles {M N : DifferentialGradedModule.{u, v} A} (f : M ⟶ N) : Prop :=
  f.toCochainMap.EpiOnCycles

/-- The map on incoming-differential cokernels in degree `n` induced by a right-DG-module
morphism. -/
abbrev differentialCokernelMap {M N : DifferentialGradedModule.{u, v} A}
    (f : M ⟶ N) (n : ℤ) :=
  CochainComplex.differentialCokernelMap f.toCochainMap n

/-- A right-DG-module morphism is monic on differential cokernels when every induced map on an
incoming-differential cokernel is monic. -/
@[stacks 0653 "monicity on DG-module incoming differential cokernels"]
abbrev MonoOnDifferentialCokernels {M N : DifferentialGradedModule.{u, v} A}
    (f : M ⟶ N) : Prop :=
  CochainComplex.MonoOnDifferentialCokernels f.toCochainMap

namespace EpiOnCycles

/-- An epic-on-cycles morphism has an epic cycles map in each specified degree. -/
theorem epi {M N : DifferentialGradedModule.{u, v} A} {f : M ⟶ N}
    (hf : f.EpiOnCycles) (n : ℤ) : Epi (f.cyclesMap n) := sorry

end EpiOnCycles

namespace MonoOnDifferentialCokernels

/-- A morphism monic on differential cokernels has a monic induced map in each specified
degree. -/
theorem mono {M N : DifferentialGradedModule.{u, v} A} {f : M ⟶ N}
    (hf : f.MonoOnDifferentialCokernels) (n : ℤ) :
    Mono (f.differentialCokernelMap n) := sorry

end MonoOnDifferentialCokernels

end DifferentialGradedModule.Hom
