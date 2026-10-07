module

public import stacks_project.Chap98.Example_98_22_3_BaseChange
public import stacks_project.Chap98.Example_98_22_3_Functor
public import stacks_project.Chap98.Example_98_22_3_Obstruction
import Mathlib.Tactic.CrossRefAttribute

/-!
# Global-sections obstruction theory

Stacks tag 07YH: the category fibred in groupoids associated to
`T/S ↦ Γ(W_T, F_T)`, for `F` quasi-coherent and flat over `S = Spec(Λ)`, has an
obstruction theory whose obstruction modules are `H^1(W_A, F_A ⊗_A M)` and whose
obstruction classes are connecting images along the first-order thickening
`W_A ⟶ W_{A'}`.
-/

@[expose] public section

open CategoryTheory Opposite
open AlgebraicGeometry
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidsOver.GlobalSections

variable {Λ : Type u} [CommRing Λ] [IsNoetherianRing Λ]
variable {W : Scheme.{u}} (w : W ⟶ S Λ)
variable (F : W.Modules) [SheafOfModules.IsQuasicoherent F]

/-- Example 98.22.3: let `S = Spec(Λ)` for a Noetherian ring `Λ`, let `w : W ⟶ S` be a
morphism of schemes, and let `F` be a quasi-coherent `O_W`-module flat over `S`. The
functor `T/S ↦ Γ(W_T, F_T)` determines a category fibred in groupoids `toGroupoids w F`.
For a deformation situation given by a square-zero extension `A' → A` of `Λ`-algebras and
a section `x ∈ Γ(W_A, F_A)`, a lift of `x` to `Γ(W_{A'}, F_{A'})` exists if and only if
the connecting obstruction class of `x` in `O_x(I)` vanishes. -/
@[stacks 07YH]
theorem exists_lift_iff_obstructionClass_eq_zero
    (hflat : Scheme.Modules.flatOver F w)
    {A A' : Type u} [CommRing A] [CommRing A'] [Algebra Λ A] [Algebra Λ A']
    [Algebra A' A] [IsScalarTower Λ A' A]
    [(algebraMap A' A).IsSquareZeroExtension]
    (x : Γ(affineModulePullback w F A, ⊤)) :
    (∃ y : Γ(affineModulePullback w F A', ⊤),
        (sectionsFunctor w F).map (specOverMap Λ A A').op y = x) ↔
      obstructionClass w F A A' hflat x = 0 :=
  sorry

end AlgebraicGeometry.GroupoidsOver.GlobalSections
