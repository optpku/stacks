/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Abelian.FunctorCategory
public import Mathlib.CategoryTheory.Abelian.Subcategory
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Coherent.Closure
public import ReasLib.CategoryTheory.InverseSystem.Sequential
public import stacks_project.Chap66.Definition_66_24_1_Noetherian
public import stacks_project.Chap69.Lemma_69_12_8_ClosedImmersion
public import stacks_project.Chap69.Lemma_69_13_2_IdealPower

/-!
# Coherent formal modules on algebraic spaces

This file defines inverse systems of coherent modules along a quasi-coherent
ideal sheaf on an algebraic space, and bundles them as a full subcategory.
-/

@[expose] public section

open CategoryTheory Opposite AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open CategoryTheory.Limits

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- The quotient module `M / I^n M` obtained as the cokernel of the inclusion of
the ideal-power product subobject. -/
abbrev idealPowerQuotient {S : Scheme.{u}} {X : AlgebraicSpace S}
    (I : IdealSubobject X) (M : X.Modules) (n : ℕ) : X.Modules :=
  cokernel (Modules.idealPowerProductSubobject I M n).arrow

/-- The quotient module `M / I^n M` is the cokernel of the inclusion of `I^n M`. -/
theorem idealPowerQuotient_eq {S : Scheme.{u}} {X : AlgebraicSpace S}
    (I : IdealSubobject X) (M : X.Modules) (n : ℕ) :
    idealPowerQuotient I M n =
      cokernel (Modules.idealPowerProductSubobject I M n).arrow := sorry

/-- An inverse system of coherent modules is a coherent formal module system along
`I` when each stage is annihilated by `I^n` and each successor map induces an
isomorphism from the quotient by `I^n`. -/
def IsCoherentFormalModuleSystem {S : Scheme.{u}} {X : AlgebraicSpace S}
    (I : IdealSubobject X) :
    ObjectProperty (SequentialInverseSystem (Coh X)) :=
  fun F ↦
    (∀ n : ℕ,
      Modules.idealPowerProductSubobject I (F.obj (op n)).obj n = ⊥) ∧
    ∀ n : ℕ,
      ∃ h : (Modules.idealPowerProductSubobject I
            (F.obj (op (n + 1))).obj n).arrow ≫
          (Coh.inclusion X).map (F.stepMap n) = 0,
        IsIso (cokernel.desc
          (Modules.idealPowerProductSubobject I
            (F.obj (op (n + 1))).obj n).arrow
          ((Coh.inclusion X).map (F.stepMap n)) h)

/-- The full category of coherent formal module systems along an ideal subobject
`I`. -/
abbrev CoherentFormalModules {S : Scheme.{u}} (X : AlgebraicSpace S)
    (I : IdealSubobject X) :=
  (IsCoherentFormalModuleSystem I).FullSubcategory

/-- An inverse system is a coherent formal module system exactly when each stage
is annihilated by the corresponding ideal power and each successor map induces
the quotient isomorphism. -/
theorem isCoherentFormalModuleSystem_iff {S : Scheme.{u}} {X : AlgebraicSpace S}
    (I : IdealSubobject X) (F : SequentialInverseSystem (Coh X)) :
    IsCoherentFormalModuleSystem I F ↔
      (∀ n : ℕ,
        Modules.idealPowerProductSubobject I (F.obj (op n)).obj n = ⊥) ∧
      ∀ n : ℕ,
        ∃ h : (Modules.idealPowerProductSubobject I
              (F.obj (op (n + 1))).obj n).arrow ≫
            (Coh.inclusion X).map (F.stepMap n) = 0,
          IsIso (cokernel.desc
            (Modules.idealPowerProductSubobject I
              (F.obj (op (n + 1))).obj n).arrow
            ((Coh.inclusion X).map (F.stepMap n)) h) :=
  sorry

/-- The zero inverse system is a coherent formal module system over a Noetherian
algebraic space. -/
instance isCoherentFormalModuleSystem_containsZero {S : Scheme.{u}}
    {X : AlgebraicSpace S} [IsNoetherian X] (I : IdealSubobject X)
    [IsQuasiCoherent I] :
    (IsCoherentFormalModuleSystem I).ContainsZero :=
  sorry

/-- Coherent formal module systems over a Noetherian algebraic space are closed
under kernels. -/
instance isCoherentFormalModuleSystem_isClosedUnderKernels {S : Scheme.{u}}
    {X : AlgebraicSpace S} [IsNoetherian X] (I : IdealSubobject X)
    [IsQuasiCoherent I] :
    (IsCoherentFormalModuleSystem I).IsClosedUnderKernels :=
  sorry

/-- Coherent formal module systems over a Noetherian algebraic space are closed
under cokernels. -/
instance isCoherentFormalModuleSystem_isClosedUnderCokernels {S : Scheme.{u}}
    {X : AlgebraicSpace S} [IsNoetherian X] (I : IdealSubobject X)
    [IsQuasiCoherent I] :
    (IsCoherentFormalModuleSystem I).IsClosedUnderCokernels :=
  sorry

/-- Coherent formal module systems over a Noetherian algebraic space are closed
under finite products. -/
instance isCoherentFormalModuleSystem_isClosedUnderFiniteProducts
    {S : Scheme.{u}} {X : AlgebraicSpace S} [IsNoetherian X]
    (I : IdealSubobject X) [IsQuasiCoherent I] :
    (IsCoherentFormalModuleSystem I).IsClosedUnderFiniteProducts :=
  sorry

/-- Coherent formal modules along a quasi-coherent ideal on a Noetherian
algebraic space form an abelian category. -/
noncomputable instance coherentFormalModules_abelian
    {S : Scheme.{u}} {X : AlgebraicSpace S} [IsNoetherian X]
    (I : IdealSubobject X) [IsQuasiCoherent I] :
    Abelian (CoherentFormalModules X I) :=
  CategoryTheory.ObjectProperty.instAbelianFullSubcategoryOfContainsZeroOfIsClosedUnderKernelsOfIsClosedUnderCokernelsOfIsClosedUnderFiniteProducts
    (IsCoherentFormalModuleSystem I)

end AlgebraicGeometry.AlgebraicSpace
