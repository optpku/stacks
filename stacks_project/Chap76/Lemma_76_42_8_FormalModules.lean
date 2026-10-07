module

public import ReasLib.CategoryTheory.InverseSystem.Sequential
public import stacks_project.Chap69.Lemma_69_12_8_ClosedImmersion
public import stacks_project.Chap69.Lemma_69_13_2_IdealPower

/-!
# Coherent formal modules on algebraic spaces

An object of `Coh(X, I)` is an inverse system of coherent `𝒪_X`-modules whose
stage `n` is annihilated by `I^n` and whose successor maps induce isomorphisms
`F_{n+1} / I^n F_{n+1} ≅ F_n`.
-/

@[expose] public section

open CategoryTheory Opposite AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open CategoryTheory.Limits

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

namespace Modules

variable {S : Scheme.{u}} {X : AlgebraicSpace S}

/-- The quotient module `F / I^n F`, as the cokernel of the inclusion of the
subobject `I^n F`. -/
noncomputable def powerQuotient (I : IdealSubobject X) (F : X.Modules) (n : ℕ) :
    X.Modules :=
  cokernel (idealPowerProductSubobject I F n).arrow

/-- `powerQuotient I F n` is the cokernel of the subobject arrow of `I^n F`. -/
theorem powerQuotient_eq (I : IdealSubobject X) (F : X.Modules) (n : ℕ) :
    powerQuotient I F n = cokernel (idealPowerProductSubobject I F n).arrow :=
  rfl

/-- The canonical projection `F ⟶ F / I^n F`. -/
noncomputable def powerQuotient.projection (I : IdealSubobject X) (F : X.Modules)
    (n : ℕ) : F ⟶ powerQuotient I F n :=
  cokernel.π (idealPowerProductSubobject I F n).arrow

/-- A module is annihilated by `I^n` when the product subobject `I^n F` is zero. -/
def IsAnnihilatedByIdealPower (I : IdealSubobject X) (F : X.Modules) (n : ℕ) :
    Prop :=
  idealPowerProductSubobject I F n = ⊥

/-- Annihilation by `I^n` is vanishing of the product subobject `I^n F`. -/
theorem isAnnihilatedByIdealPower_iff (I : IdealSubobject X) (F : X.Modules)
    (n : ℕ) :
    IsAnnihilatedByIdealPower I F n ↔
      idealPowerProductSubobject I F n = ⊥ :=
  Iff.rfl

end Modules

/-- The map `F_{n+1} / I^n F_{n+1} ⟶ F_n` induced by a successor transition that
vanishes on `I^n F_{n+1}`. -/
noncomputable def inducedSuccessorPowerQuotient
    {S : Scheme.{u}} {X : AlgebraicSpace S} (I : IdealSubobject X)
    (F : SequentialInverseSystem (Coh X)) (n : ℕ)
    (h : (Modules.idealPowerProductSubobject I (F.obj (op (n + 1))).obj n).arrow ≫
        (F.stepMap n).hom = 0) :
    Modules.powerQuotient I (F.obj (op (n + 1))).obj n ⟶ (F.obj (op n)).obj :=
  cokernel.desc
    (Modules.idealPowerProductSubobject I (F.obj (op (n + 1))).obj n).arrow
    (F.stepMap n).hom h

/-- An inverse system of coherent modules is a coherent formal module system
along `I` when each stage `n` is annihilated by `I^n` and each successor map
induces an isomorphism `F_{n+1} / I^n F_{n+1} ≅ F_n`. -/
def IsCoherentFormalModuleSystem {S : Scheme.{u}} {X : AlgebraicSpace S}
    (I : IdealSubobject X) :
    ObjectProperty (SequentialInverseSystem (Coh X)) :=
  fun F ↦
    (∀ n : ℕ, Modules.IsAnnihilatedByIdealPower I (F.obj (op n)).obj n) ∧
      ∀ n : ℕ,
        ∃ h :
          (Modules.idealPowerProductSubobject I (F.obj (op (n + 1))).obj n).arrow ≫
              (F.stepMap n).hom = 0,
          IsIso (inducedSuccessorPowerQuotient I F n h)

/-- The full category of coherent formal module systems along a quasi-coherent
ideal sheaf `I`. -/
abbrev CoherentFormalModules {S : Scheme.{u}} (X : AlgebraicSpace S)
    (I : IdealSubobject X) :=
  (IsCoherentFormalModuleSystem I).FullSubcategory

/-- An inverse system is a coherent formal module system exactly when its stages
are annihilated by the corresponding ideal powers and successors induce the
expected quotient isomorphisms. -/
theorem isCoherentFormalModuleSystem_iff {S : Scheme.{u}} {X : AlgebraicSpace S}
    (I : IdealSubobject X) (F : SequentialInverseSystem (Coh X)) :
    IsCoherentFormalModuleSystem I F ↔
      (∀ n : ℕ, Modules.IsAnnihilatedByIdealPower I (F.obj (op n)).obj n) ∧
        ∀ n : ℕ,
          ∃ h :
            (Modules.idealPowerProductSubobject I
                  (F.obj (op (n + 1))).obj n).arrow ≫
                (F.stepMap n).hom = 0,
            IsIso (inducedSuccessorPowerQuotient I F n h) :=
  Iff.rfl

end AlgebraicGeometry.AlgebraicSpace
