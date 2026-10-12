/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Module.Torsion.Basic
public import stacks_project.Chap64.Definition_64_18_1_ZEllSheaf
public import stacks_project.Chap64.Definition_64_18_6_Stalk
public import stacks_project.Chap64.Definition_64_18_6_QEll

/-!
# Torsion of canonical constructible ℓ-adic sheaves

The object and its stage/transition/constant API come from Definition 64.18.1.
The actual inverse-limit stalk and residue scalar action come from Definition 64.18.6.
Torsion is the canonical vanishing-power predicate, with its stagewise equivalence.
No second adic-system structure or replacement stalk is introduced here.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite CategoryTheory.Sheaf
open AlgebraicGeometry AlgebraicGeometry.Scheme

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Etale.ZEllSheaf

variable {X : Scheme.{u}} [IsNoetherian X] {ℓ : ℕ} [Fact (Nat.Prime ℓ)]
variable [HasSheafify X.smallEtaleTopology AddCommGrpCat.{u}]
variable [∀ (Y : Scheme.{u}) (V : Y.Etale),
  HasWeakSheafify (Y.smallEtaleTopology.over V) AddCommGrpCat.{u}]

/-- Compatibility predicate exposing the actual constructible-stage condition already
contained in the canonical `ZEllSheaf` object. -/
def IsConstructible (F : ZEllSheaf X ℓ) : Prop :=
  ∀ n, IsConstructibleEtale
    (fun {Y : Scheme.{u}} (f : Y ⟶ X) ↦ (etaleAbelianRestriction f).obj)
    (fun {Y : Scheme.{u}} (G : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u}) ↦
      IsFiniteLocallyConstantAddCommGrp G) (F.stage n)

/-- Every canonical ℓ-adic sheaf has constructible stages by its defining field. -/
theorem constructible (F : ZEllSheaf X ℓ) : F.IsConstructible := F.isConstructible

/-- The canonical constant ℓ-adic sheaf satisfies its defining adic cokernel comparisons. -/
theorem constant_isAdic (X : Scheme.{u}) (ℓ : ℕ) [Fact (Nat.Prime ℓ)] [IsNoetherian X]
    [HasSheafify X.smallEtaleTopology AddCommGrpCat.{u}] (n : ℕ) :
    IsIso (cokernel.desc ((ℓ ^ (n + 1)) • 𝟙 ((constant X ℓ).stage (n + 1)))
      ((constant X ℓ).stepMap n) ((constant X ℓ).step_comp_nsmul n)) :=
  (constant X ℓ).isAdic n

/-- The stalk is a finite ℤ_[ℓ]-module by constructibility and the adic transition laws;
therefore torsion is equivalent to annihilation by a single power of ℓ. -/
theorem stalk_isTorsion_iff (F : ZEllSheaf X ℓ) (x : GeometricPoint X) :
    Module.IsTorsion ℤ_[ℓ] (F.stalk x) ↔
      ∃ n : ℕ, Module.IsTorsionBy ℤ_[ℓ] (F.stalk x) (ℓ ^ n : ℤ_[ℓ]) := sorry

/-- Torsion of the canonical ℓ-adic sheaf implies torsion of each actual inverse-limit stalk. -/
theorem IsTorsion.stalk_isTorsion {F : ZEllSheaf X ℓ} (hF : F.IsTorsion)
    (x : GeometricPoint X) : Module.IsTorsion ℤ_[ℓ] (F.stalk x) := sorry

end AlgebraicGeometry.Scheme.Etale.ZEllSheaf
