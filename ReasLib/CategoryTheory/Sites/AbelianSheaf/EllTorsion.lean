module

public import ReasLib.CategoryTheory.Sites.AbelianSheaf.Torsion.Primary

@[expose] public section

open CategoryTheory Opposite

universe w v u

namespace CategoryTheory.Sheaf

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}

/-- An abelian sheaf is locally `ℓ`-torsion if every section admits a cover
on which each restriction is annihilated by `ℓ`. -/
def IsLocallyEllTorsion (ℓ : ℕ) (F : Sheaf J AddCommGrpCat.{w}) : Prop :=
  ∀ (U : C) (sectionValue : F.obj.obj (op U)),
    ∃ cover : J.Cover U, ∀ arrow : cover.Arrow,
      ℓ • (F.obj.map arrow.f.op sectionValue) = 0

/-- Local `ℓ`-torsion is equivalent to coverwise annihilation of every section by `ℓ`. -/
theorem isLocallyEllTorsion_iff (ℓ : ℕ) (F : Sheaf J AddCommGrpCat.{w}) :
    IsLocallyEllTorsion ℓ F ↔
      ∀ (U : C) (sectionValue : F.obj.obj (op U)),
        ∃ cover : J.Cover U, ∀ arrow : cover.Arrow,
          ℓ • (F.obj.map arrow.f.op sectionValue) = 0 := sorry

namespace IsLocallyEllTorsion

/-- Sectionwise annihilation by `ℓ` implies local `ℓ`-torsion. -/
theorem ofSectionwise {ℓ : ℕ} {F : Sheaf J AddCommGrpCat.{w}}
    (hF : ∀ (U : C) (sectionValue : F.obj.obj (op U)), ℓ • sectionValue = 0) :
    IsLocallyEllTorsion ℓ F := sorry

/-- Local `ℓ`-torsion implies local `ℓ`-power torsion. -/
theorem toIsLocallyEllPowerTorsion {ℓ : ℕ} {F : Sheaf J AddCommGrpCat.{w}}
    (hF : IsLocallyEllTorsion ℓ F) :
    IsLocallyPPowerTorsion ℓ F := sorry

/-- For positive `ℓ`, local `ℓ`-torsion implies local finite-order torsion. -/
theorem toIsLocallyTorsion {ℓ : ℕ} {F : Sheaf J AddCommGrpCat.{w}}
    (hℓ : 0 < ℓ) (hF : IsLocallyEllTorsion ℓ F) :
    IsLocallyTorsion F := sorry

end IsLocallyEllTorsion

end CategoryTheory.Sheaf
