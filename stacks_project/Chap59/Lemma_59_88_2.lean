/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.BaseChange.Monomorphism
import StacksCheckRecall

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

noncomputable section

universe u

/- Lemma 59.88.2 (1) -/
@[stacks 0F03] #check
  (AlgebraicGeometry.Scheme.Etale.BaseChange.higherMap_mono :
    ∀ {X S X' Y S' T : Scheme.{u}} (f : X ⟶ S) (n : ℤ) {q : ℕ}
      (hq : 1 ≤ q) (p : X' ⟶ X) (f' : X' ⟶ S') (s : S' ⟶ S)
      (h : Y ⟶ X') (e : Y ⟶ T) (g : T ⟶ S')
      [QuasiCompact g] [QuasiSeparated g]
      [HasSheafify T.smallEtaleTopology AddCommGrpCat.{u + 1}]
      [HasSheafify S'.smallEtaleTopology AddCommGrpCat.{u + 1}]
      [HasSheafify X'.smallEtaleTopology AddCommGrpCat.{u + 1}]
      [HasSheafify Y.smallEtaleTopology AddCommGrpCat.{u + 1}]
      [HasInjectiveResolutions
        (Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1})]
      [HasInjectiveResolutions
        (Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1})]
      (sq₁ : IsPullback p f' f s) (sq₂ : IsPullback h e f' g)
      (hBC : AlgebraicGeometry.Scheme.Etale.BaseChange.Holds f n (q - 1))
      (F : Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1})
      (hF : (n : ℤ) • 𝟙 F = 0),
      Mono (AlgebraicGeometry.Scheme.Etale.BaseChange.higherMap f' h e g sq₂ q F))

/- Lemma 59.88.2 (2) -/
@[stacks 0F03] #check
  (AlgebraicGeometry.Scheme.Etale.BaseChange.higherCokernelMap_mono :
    ∀ {X S X' Y S' T : Scheme.{u}} (n : ℤ) (f : X ⟶ S) {q : ℕ}
      (hq : 1 ≤ q) (p : X' ⟶ X) (f' : X' ⟶ S') (s : S' ⟶ S)
      (h : Y ⟶ X') (e : Y ⟶ T) (g : T ⟶ S')
      [QuasiCompact g] [QuasiSeparated g]
      [HasSheafify T.smallEtaleTopology AddCommGrpCat.{u + 1}]
      [HasSheafify S'.smallEtaleTopology AddCommGrpCat.{u + 1}]
      [HasSheafify X'.smallEtaleTopology AddCommGrpCat.{u + 1}]
      [HasSheafify Y.smallEtaleTopology AddCommGrpCat.{u + 1}]
      [HasInjectiveResolutions
        (Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1})]
      [HasInjectiveResolutions
        (Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1})]
      (sq₁ : IsPullback p f' f s) (sq₂ : IsPullback h e f' g)
      (hBC : AlgebraicGeometry.Scheme.Etale.BaseChange.Holds f n (q - 1))
      {F G : Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1}}
      (ι : F ⟶ G) [Mono ι] (hF : (n : ℤ) • 𝟙 F = 0)
      (hG : (n : ℤ) • 𝟙 G = 0),
      Mono (AlgebraicGeometry.Scheme.Etale.BaseChange.higherCokernelMap f' h e g sq₂ q ι))

/- Lemma 59.88.2 (3) -/
@[stacks 0F03] #check
  (AlgebraicGeometry.Scheme.Etale.BaseChange.higherCokernelToInjective_mono :
    ∀ {X S X' Y S' T : Scheme.{u}} (n : ℤ) (f : X ⟶ S) {q : ℕ}
      (hq : 1 ≤ q) (p : X' ⟶ X) (f' : X' ⟶ S') (s : S' ⟶ S)
      (h : Y ⟶ X') (e : Y ⟶ T) (g : T ⟶ S')
      [QuasiCompact g] [QuasiSeparated g]
      [HasSheafify T.smallEtaleTopology AddCommGrpCat.{u + 1}]
      [HasSheafify S'.smallEtaleTopology AddCommGrpCat.{u + 1}]
      [HasSheafify X'.smallEtaleTopology AddCommGrpCat.{u + 1}]
      [HasSheafify Y.smallEtaleTopology AddCommGrpCat.{u + 1}]
      [HasInjectiveResolutions
        (Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1})]
      [HasInjectiveResolutions
        (Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1})]
      (sq₁ : IsPullback p f' f s) (sq₂ : IsPullback h e f' g)
      (hBC : AlgebraicGeometry.Scheme.Etale.BaseChange.Holds f n (q - 1))
      (F : Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1})
      (hF : (n : ℤ) • 𝟙 F = 0)
      (Gmod : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} (ZMod n.natAbs)))
      [Injective Gmod]
      (ι : F ⟶ (sheafCompose T.smallEtaleTopology
        (forget₂ (ModuleCat.{u + 1} (ZMod n.natAbs)) AddCommGrpCat.{u + 1})).obj Gmod)
      [Mono ι],
      Mono (AlgebraicGeometry.Scheme.Etale.BaseChange.higherCokernelToInjective
        n f' h e g sq₂ hq F Gmod ι))

end

end
