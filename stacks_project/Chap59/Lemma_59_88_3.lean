/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.BaseChange.IntegralCover
import StacksCheckRecall

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

noncomputable section

universe u

/- Lemma 59.88.3 -/
@[stacks 0F04] #check
  (AlgebraicGeometry.Scheme.Etale.BaseChange.higherMap_isIso_of_integral_cover :
    ∀ {X S : Scheme.{u}} (f : X ⟶ S) (n : ℤ) {q : ℕ} (hq : 1 ≤ q)
      {X' S' Y T Y' T' : Scheme.{u}}
      (p : X' ⟶ X) (f' : X' ⟶ S') (s : S' ⟶ S)
      (h : Y ⟶ X') (e : Y ⟶ T) (g : T ⟶ S')
      (π' : Y' ⟶ Y) (e' : Y' ⟶ T') (π : T' ⟶ T)
      [QuasiCompact g] [QuasiSeparated g]
      [IsIntegralHom π] [Surjective π]
      [HasSheafify T.smallEtaleTopology AddCommGrpCat.{u + 1}]
      [HasSheafify T'.smallEtaleTopology AddCommGrpCat.{u + 1}]
      [HasSheafify S'.smallEtaleTopology AddCommGrpCat.{u + 1}]
      [HasSheafify X'.smallEtaleTopology AddCommGrpCat.{u + 1}]
      [HasSheafify Y.smallEtaleTopology AddCommGrpCat.{u + 1}]
      [HasSheafify Y'.smallEtaleTopology AddCommGrpCat.{u + 1}]
      [HasInjectiveResolutions
        (Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1})]
      [HasInjectiveResolutions
        (Sheaf T'.smallEtaleTopology AddCommGrpCat.{u + 1})]
      [HasInjectiveResolutions
        (Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1})]
      [HasInjectiveResolutions
        (Sheaf Y'.smallEtaleTopology AddCommGrpCat.{u + 1})]
      (sq_left : IsPullback p f' f s)
      (sq_unprimed : IsPullback h e f' g)
      (sq_cover : IsPullback π' e' e π)
      (sq_primed : IsPullback (π' ≫ h) e' f' (π ≫ g))
      (hBC : AlgebraicGeometry.Scheme.Etale.BaseChange.Holds f n (q - 1))
      (F : Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1})
      (hF : (n : ℤ) • 𝟙 F = 0)
      (hiso :
        IsIso (AlgebraicGeometry.Scheme.Etale.BaseChange.higherMap f'
          (π' ≫ h) e' (π ≫ g) sq_primed q
          ((AlgebraicGeometry.Scheme.Etale.Abelian.inverseImage π).obj F))),
      IsIso (AlgebraicGeometry.Scheme.Etale.BaseChange.higherMap f' h e g
        sq_unprimed q F))

end

end
