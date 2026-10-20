/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.BaseChange.Condition
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.BaseChange.Map
public import Mathlib.AlgebraicGeometry.Morphisms.Integral
public import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap

@[expose] public section

open CategoryTheory
open AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Etale.BaseChange

/-- Under an integral surjective cover of the target, an isomorphism of the
degree-`q` higher-direct-image base-change map descends to the original square. -/
theorem higherMap_isIso_of_integral_cover
    {X S : Scheme.{u}} (f : X ⟶ S) (n : ℤ) {q : ℕ} (hq : 1 ≤ q)
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
    (hBC : Holds f n (q - 1))
    (F : Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1})
    (hF : (n : ℤ) • 𝟙 F = 0)
    (hiso :
      IsIso (higherMap f' (π' ≫ h) e' (π ≫ g) sq_primed q
        ((Abelian.inverseImage π).obj F))) :
    IsIso (higherMap f' h e g sq_unprimed q F) := sorry

end AlgebraicGeometry.Scheme.Etale.BaseChange

end

end
