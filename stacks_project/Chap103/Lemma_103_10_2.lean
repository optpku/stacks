module

public import Mathlib.CategoryTheory.Adjunction.Basic
public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import Mathlib.CategoryTheory.Limits.Preserves.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.Kernels
public import Mathlib.CategoryTheory.ObjectProperty.ContainsZero
public import stacks_project.Chap103.Lemma_103_10_1

/-!
# Kernel of the right adjoint to quasi-coherent inclusion

On an algebraic stack, the right adjoint `Q : LQCoh^{fbc}(𝒪_X) ⥤ QCoh(𝒪_X)` of
Lemma 103.10.1 has parasitic kernel, parasitic counit kernel and cokernel, and
is exact while preserving all limits and colimits.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open CategoryTheory.ObjectProperty
open AlgebraicGeometry.GroupoidsOver

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidsOver

variable {S : Scheme.{u}}

/-- Parasitic objects of `LQCohFbc X`, obtained by restricting
`EtaleModules.parasitic` along the inclusion into étale modules. -/
abbrev LQCohFbc.parasitic (X : GroupoidsOver S) [AlgebraicStack X] :
    ObjectProperty (LQCohFbc X) :=
  (EtaleModules.parasitic X).inverseImage (LQCohFbc.inclusion X)

/-- An object of `LQCohFbc X` is parasitic if and only if its underlying étale
module is parasitic. -/
theorem LQCohFbc.mem_parasitic {X : GroupoidsOver S} [AlgebraicStack X]
    (F : LQCohFbc X) :
    LQCohFbc.parasitic X F ↔
      EtaleModules.IsParasitic ((LQCohFbc.inclusion X).obj F) :=
  sorry

/-- Lemma 103.10.2 (1): the kernel of `LQCohFbc.toQCoh` is exactly the
collection of parasitic objects of `LQCohFbc X`. -/
@[stacks 0779]
theorem LQCohFbc.toQCoh_kernel (X : GroupoidsOver S) [AlgebraicStack X] :
    Functor.kernel (LQCohFbc.toQCoh X) = LQCohFbc.parasitic X :=
  sorry

/-- An object of `LQCohFbc X` becomes zero after `toQCoh` if and only if it is
parasitic. -/
theorem LQCohFbc.toQCoh_isZero_iff {X : GroupoidsOver S} [AlgebraicStack X]
    (F : LQCohFbc X) :
    IsZero ((LQCohFbc.toQCoh X).obj F) ↔ LQCohFbc.parasitic X F :=
  sorry

/-- Lemma 103.10.2 (2): the kernel of the adjunction map `Q(F) ⟶ F` is a
parasitic object of `LQCohFbc X`. -/
@[stacks 0779]
theorem LQCohFbc.toQCoh_counit_kernel_isParasitic
    {X : GroupoidsOver S} [AlgebraicStack X]
    (adj : QCoh.toLQCohFbc X ⊣ LQCohFbc.toQCoh X) (F : LQCohFbc X) :
    LQCohFbc.parasitic X (kernel (adj.counit.app F)) :=
  sorry

/-- Lemma 103.10.2 (2): the cokernel of the adjunction map `Q(F) ⟶ F` is a
parasitic object of `LQCohFbc X`. -/
@[stacks 0779]
theorem LQCohFbc.toQCoh_counit_cokernel_isParasitic
    {X : GroupoidsOver S} [AlgebraicStack X]
    (adj : QCoh.toLQCohFbc X ⊣ LQCohFbc.toQCoh X) (F : LQCohFbc X) :
    LQCohFbc.parasitic X (cokernel (adj.counit.app F)) :=
  sorry

/-- Lemma 103.10.2 (3): the functor `LQCohFbc.toQCoh` is exact. -/
@[stacks 0779]
theorem LQCohFbc.toQCoh_exact (X : GroupoidsOver S) [AlgebraicStack X] :
    exactFunctor (LQCohFbc X) (QCoh X) (LQCohFbc.toQCoh X) :=
  sorry

/-- Lemma 103.10.2 (3): the functor `LQCohFbc.toQCoh` preserves all limits. -/
@[stacks 0779]
instance LQCohFbc.toQCoh_preservesLimits (X : GroupoidsOver S)
    [AlgebraicStack X] :
    PreservesLimits (LQCohFbc.toQCoh X) :=
  sorry

/-- Lemma 103.10.2 (3): the functor `LQCohFbc.toQCoh` preserves all colimits. -/
@[stacks 0779]
instance LQCohFbc.toQCoh_preservesColimits (X : GroupoidsOver S)
    [AlgebraicStack X] :
    PreservesColimits (LQCohFbc.toQCoh X) :=
  sorry

end AlgebraicGeometry.GroupoidsOver
