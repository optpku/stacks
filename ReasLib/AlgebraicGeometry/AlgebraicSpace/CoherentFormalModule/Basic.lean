module

public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
public import ReasLib.CategoryTheory.InverseSystem.Sequential
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Coherent.Category
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.IdealPower

/-!
# Coherent formal modules on algebraic spaces

An inverse system of coherent modules on an algebraic space is a
coherent formal module along an ideal subobject `I` when each stage
is annihilated by the corresponding power of `I` and each successor map induces
an isomorphism on the expected ideal-power quotient.
-/

@[expose] public section

open CategoryTheory Opposite CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.Modules

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- The map `F_{n+1} / I ^ n F_{n+1} ⟶ F_n` induced by a successor transition that
vanishes on `I ^ n F_{n+1}`. -/
def inducedQuotient {S : Scheme.{u}} {X : AlgebraicSpace S} (I : IdealSubobject X)
    (F : SequentialInverseSystem (Coh X)) (n : ℕ)
    (h : (idealPowerProductSubobject I (F.obj (op (n + 1))).obj n).arrow ≫
        (F.stepMap n).hom = 0) :
    cokernel (idealPowerProductSubobject I (F.obj (op (n + 1))).obj n).arrow ⟶
      (F.obj (op n)).obj :=
  cokernel.desc _ (F.stepMap n).hom h

/-- The successor transition of a system annihilated by `I ^ n` at stage `n`
vanishes on `I ^ n F_{n+1}`. -/
theorem stepMap_comp_idealPower_eq_zero {S : Scheme.{u}} {X : AlgebraicSpace S}
    (I : IdealSubobject X) (F : SequentialInverseSystem (Coh X)) (n : ℕ)
    (h : idealPowerProductSubobject I (F.obj (op n)).obj n = ⊥) :
    (idealPowerProductSubobject I (F.obj (op (n + 1))).obj n).arrow ≫
      (F.stepMap n).hom = 0 := sorry

/-- An inverse system of coherent modules is a coherent formal module system along
`I` when each stage is annihilated by the corresponding power of `I` and each
successor map induces an isomorphism `F_{n+1} / I ^ n F_{n+1} ⟶ F_n`. -/
def IsCoherentFormalModuleSystem {S : Scheme.{u}} {X : AlgebraicSpace S}
    (I : IdealSubobject X) :
    ObjectProperty (SequentialInverseSystem (Coh X)) :=
  fun F ↦
    (∀ n : ℕ, idealPowerProductSubobject I (F.obj (op n)).obj n = ⊥) ∧
      ∀ n : ℕ,
        ∃ h :
          (idealPowerProductSubobject I (F.obj (op (n + 1))).obj n).arrow ≫
              (F.stepMap n).hom = 0,
          IsIso (inducedQuotient I F n h)

/-- The full category of coherent formal module systems along an ideal subobject `I`. -/
abbrev CoherentFormalModules {S : Scheme.{u}} (X : AlgebraicSpace S)
    (I : IdealSubobject X) :=
  (IsCoherentFormalModuleSystem I).FullSubcategory

/-- An inverse system is a coherent formal module system along `I` exactly when
its stages are annihilated by the corresponding powers of `I` and each successor
map induces an isomorphism on the expected ideal-power quotient. -/
theorem isCoherentFormalModuleSystem_iff {S : Scheme.{u}} {X : AlgebraicSpace S}
    (I : IdealSubobject X)
    (F : SequentialInverseSystem (Coh X)) :
    IsCoherentFormalModuleSystem I F ↔
      (∀ n : ℕ, idealPowerProductSubobject I (F.obj (op n)).obj n = ⊥) ∧
        ∀ n : ℕ,
          ∃ h :
            (idealPowerProductSubobject I (F.obj (op (n + 1))).obj n).arrow ≫
                (F.stepMap n).hom = 0,
            IsIso (inducedQuotient I F n h) := sorry


end AlgebraicGeometry.AlgebraicSpace
