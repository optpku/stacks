module

public import ReasLib.CategoryTheory.Sites.AbelianSheaf.EllPowerTorsion

/-!
# Locally ℓ-power torsion abelian sheaves

An abelian sheaf is locally ℓ-power torsion when every section is annihilated by
a power of ℓ after restriction along some cover.
-/

@[expose] public section

open CategoryTheory Opposite
open CategoryTheory.Sheaf

noncomputable section

universe w v u

namespace CategoryTheory.Sheaf

/- Locally `ℓ`-power torsion is the canonical coefficient predicate. -/
abbrev IsLocallyEllPowerTorsion {C : Type u} [Category.{v} C]
    {J : GrothendieckTopology C} (ℓ : ℕ)
    (F : Sheaf J AddCommGrpCat.{w}) : Prop :=
  IsLocallyPPowerTorsion ℓ F

#check (CategoryTheory.Sheaf.IsLocallyPPowerTorsion :
  ∀ {C : Type u} [Category.{v} C] {J : GrothendieckTopology C},
    ℕ → Sheaf J AddCommGrpCat.{w} → Prop)

/- Coverwise power annihilation characterizes the coefficient predicate. -/
#check (CategoryTheory.Sheaf.isLocallyPPowerTorsion_iff :
  ∀ {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
    (ℓ : ℕ) (F : Sheaf J AddCommGrpCat.{w}),
    IsLocallyPPowerTorsion ℓ F ↔
      ∀ (U : C) (s : F.obj.obj (op U)),
        ∃ T : J.Cover U, ∀ I : T.Arrow,
          ∃ k : ℕ, (ℓ ^ k) • (F.obj.map I.f.op s) = 0)

/- Sectionwise power annihilation implies local power torsion. -/
#check (CategoryTheory.Sheaf.IsLocallyPPowerTorsion.ofSectionwise :
  ∀ {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
    {ℓ : ℕ} {F : Sheaf J AddCommGrpCat.{w}},
    (∀ (U : C) (s : F.obj.obj (op U)), ∃ k : ℕ, (ℓ ^ k) • s = 0) →
      IsLocallyPPowerTorsion ℓ F)

/- Positive `ℓ` makes local power torsion imply local finite-order torsion. -/
#check (CategoryTheory.Sheaf.IsLocallyPPowerTorsion.toIsLocallyTorsion :
  ∀ {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
    {ℓ : ℕ} {F : Sheaf J AddCommGrpCat.{w}},
    0 < ℓ → IsLocallyPPowerTorsion ℓ F → IsLocallyTorsion F)

end CategoryTheory.Sheaf

end
