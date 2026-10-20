module

public import ReasLib.CategoryTheory.Sites.AbelianSheaf.EllTorsion

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

#check (CategoryTheory.Sheaf.IsLocallyEllTorsion :
    ℕ → Sheaf J AddCommGrpCat.{w} → Prop)

#check (CategoryTheory.Sheaf.isLocallyEllTorsion_iff :
    ∀ (ℓ : ℕ) (F : Sheaf J AddCommGrpCat.{w}),
    IsLocallyEllTorsion ℓ F ↔
      ∀ (U : C) (s : F.obj.obj (op U)),
        ∃ T : J.Cover U, ∀ I : T.Arrow, ℓ • (F.obj.map I.f.op s) = 0)

#check (CategoryTheory.Sheaf.IsLocallyEllTorsion.ofSectionwise :
    ∀ {ℓ : ℕ} {F : Sheaf J AddCommGrpCat.{w}},
      (∀ (U : C) (s : F.obj.obj (op U)), ℓ • s = 0) →
        IsLocallyEllTorsion ℓ F)

#check (CategoryTheory.Sheaf.IsLocallyEllTorsion.toIsLocallyEllPowerTorsion :
    ∀ {ℓ : ℕ} {F : Sheaf J AddCommGrpCat.{w}},
      IsLocallyEllTorsion ℓ F → CategoryTheory.Sheaf.IsLocallyPPowerTorsion ℓ F)

#check (CategoryTheory.Sheaf.IsLocallyEllTorsion.toIsLocallyTorsion :
    ∀ {ℓ : ℕ} {F : Sheaf J AddCommGrpCat.{w}},
      0 < ℓ → IsLocallyEllTorsion ℓ F → IsLocallyTorsion F)

end CategoryTheory.Sheaf

end
