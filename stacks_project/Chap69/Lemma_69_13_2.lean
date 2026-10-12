/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Coherent
public import stacks_project.Chap66.Definition_66_4_1_Points
public import stacks_project.Chap66.Definition_66_24_1_Noetherian
public import stacks_project.Chap67.Definition_67_14_4_Subscheme
public import stacks_project.Chap67.Lemma_67_31_6_ModuleSupport
public import stacks_project.Chap69.Definition_69_12_1_Instances
public import stacks_project.Chap69.Lemma_69_13_2_IdealPower

/-!
# Lemma 69.13.2

A coherent module on a Noetherian algebraic space is annihilated by some power
of a quasi-coherent ideal sheaf if and only if its support is contained
set-theoretically in the corresponding closed subspace.
-/

@[expose]
public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.Modules

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Modules

/-- Lemma 69.13.2: let `S` be a scheme, let `X` be a Noetherian algebraic space over
`S`, let `F` be a coherent sheaf on `X`, and let `I ⊂ 𝒪_X` be a quasi-coherent
sheaf of ideals corresponding to the closed subspace `Z = subscheme I`. Then
there is some `n ≥ 0` such that `I^n F = 0` if and only if `Supp(F) ⊆ |Z|`
set-theoretically, where `|Z|` is the image of `Points.map (subschemeι I)`. -/
@[stacks 07UK]
theorem exists_idealPowerProductSubobject_eq_bot_iff_moduleSupport_subset
    {S : Scheme.{u}} {X : AlgebraicSpace S} [IsNoetherian X]
    (F : X.Modules) [F.IsCoherent] (I : IdealSubobject X) [IsQuasiCoherent I] :
    (∃ n : ℕ, idealPowerProductSubobject I F n = ⊥) ↔
      moduleSupport F ⊆ Set.range (Points.map (subschemeι I)) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Modules
