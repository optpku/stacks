/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap59.Lemma_59_67_1_Torsion
import Mathlib.Tactic.CrossRefAttribute

/-!
# Locally ℓ-torsion abelian sheaves

An abelian sheaf is locally ℓ-torsion when every section is annihilated by ℓ
after restriction along some cover.
-/

@[expose] public section

open CategoryTheory Opposite
open CategoryTheory.Sheaf

noncomputable section

universe w v u

namespace CategoryTheory.Sheaf

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}

/-- A sheaf of abelian groups is locally `ℓ`-torsion if every section
restricts, along some cover, to sections annihilated by `ℓ`. -/
def IsLocallyEllTorsion (ℓ : ℕ) (F : Sheaf J AddCommGrpCat.{w}) : Prop :=
  ∀ (U : C) (s : F.obj.obj (op U)),
    ∃ T : J.Cover U, ∀ I : T.Arrow, ℓ • (F.obj.map I.f.op s) = 0

/-- Coverwise annihilation by `ℓ` is the defining condition. -/
theorem isLocallyEllTorsion_iff (ℓ : ℕ) (F : Sheaf J AddCommGrpCat.{w}) :
    IsLocallyEllTorsion ℓ F ↔
      ∀ (U : C) (s : F.obj.obj (op U)),
        ∃ T : J.Cover U, ∀ I : T.Arrow, ℓ • (F.obj.map I.f.op s) = 0 := sorry

namespace IsLocallyEllTorsion

/-- Sectionwise annihilation by `ℓ` implies local `ℓ`-torsion. -/
theorem ofSectionwise {ℓ : ℕ} {F : Sheaf J AddCommGrpCat.{w}}
    (hF : ∀ (U : C) (s : F.obj.obj (op U)), ℓ • s = 0) :
    IsLocallyEllTorsion ℓ F := sorry

/-- Local `ℓ`-torsion implies local `ℓ`-power torsion. -/
theorem toIsLocallyEllPowerTorsion {ℓ : ℕ} {F : Sheaf J AddCommGrpCat.{w}}
    (hF : IsLocallyEllTorsion ℓ F) :
    IsLocallyEllPowerTorsion ℓ F := sorry

/-- Local `ℓ`-torsion implies local finite-order torsion. -/
theorem toIsLocallyTorsion {ℓ : ℕ} {F : Sheaf J AddCommGrpCat.{w}}
    (hF : IsLocallyEllTorsion ℓ F) :
    IsLocallyTorsion F := sorry

end IsLocallyEllTorsion

end CategoryTheory.Sheaf

end
