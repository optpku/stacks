module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.CategoryTheory.Subobject.Lattice
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Coherent
public import stacks_project.Chap65.Definition_65_12_1_Subspace
public import stacks_project.Chap66.«66_26_0_1_Pushforward»
public import stacks_project.Chap66.Definition_66_24_1_Noetherian
public import stacks_project.Chap67.Definition_67_14_4_IdealSubobject
public import stacks_project.Chap67.Definition_67_47_7_Irreducible
public import stacks_project.Chap67.Lemma_67_48_6_Reduced
public import stacks_project.Chap69.Definition_69_12_1_Instances

/-!
# Lemma 69.14.3

On a Noetherian algebraic space, every coherent module admits a finite filtration by
coherent subsheaves whose successive quotients are pushforwards of ideal sheaves on
reduced closed subspaces with irreducible underlying space.
-/

@[expose]
public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.Modules

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Modules

/-- Lemma 69.14.3: let `S` be a scheme, let `X` be a Noetherian algebraic space over
`S`, and let `F` be a coherent `𝒪_X`-module. There exists a filtration
`0 = F_0 ⊂ ⋯ ⊂ F_m = F` by coherent subsheaves such that for each `j` there is a
reduced closed subspace `Z_j ⊂ X` with `|Z_j|` irreducible and an ideal sheaf
`I_j ⊂ 𝒪_{Z_j}` with `F_j / F_{j-1} ≅ (Z_j ⟶ X)_* I_j`. -/
@[stacks 07UR]
theorem exists_coherentSubobject_filtration_quotient_iso_pushforward_ideal
    {S : Scheme.{u}} {X : AlgebraicSpace S} [IsNoetherian X]
    (F : X.Modules) [F.IsCoherent] :
    ∃ (m : ℕ) (Fil : ℕ →o Subobject F) (Z : Fin m → ClosedSubspace X)
      (I : (j : Fin m) → IdealSubobject (Z j).X)
      (e : (j : Fin m) →
        cokernel (Subobject.ofLE (Fil j.1) (Fil (j.1 + 1))
          (Fil.monotone (Nat.le_succ j.1))) ≅
          (pushforward (Z j).ι).obj (I j).toModule),
      ∃ (hBot : Fil 0 = ⊥) (hTop : Fil m = ⊤)
        (hFiltrationCoherent :
          ∀ n, n ≤ m → ((Fil n : Subobject F) : X.Modules).IsCoherent)
        (hReduced : ∀ j : Fin m, IsReduced (Z j).X)
        (hIrreducible : ∀ j : Fin m, IsIrreducible (Z j).X),
        ∀ j : Fin m, (I j).toModule.IsCoherent :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Modules
