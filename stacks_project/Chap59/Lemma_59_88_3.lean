module

public import Mathlib.AlgebraicGeometry.Morphisms.Integral
public import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap
public import stacks_project.Chap59.Remark_59_88_1

@[expose] public section

open CategoryTheory
open AlgebraicGeometry

noncomputable section

universe u

/-- Lemma 59.88.3: assume `BC(f, n, q - 1)` for some `q ≥ 1`.  In cartesian
diagrams relating `f : X ⟶ S` to `f'` and then to `e`, `e'` over `g`, `π` with
`g` quasi-compact and quasi-separated and `π` integral surjective, if the
degree-`q` étale higher-direct-image base-change map for the primed square
`(f', g' = g ≫ π, h' = h ≫ π')` is an isomorphism on `F' = π⁻¹ F` for an
`n`-annihilated abelian sheaf `F` on `Tₑₜ`, then the corresponding map for the
unprimed square `(f', g, h)` is an isomorphism. -/
@[stacks 0F04]
theorem etaleHigherDirectImage_baseChange_iso_of_integral_cover
    {X S : Scheme.{u}} (f : X ⟶ S) (n : ℤ) {q : ℕ} (hq : 1 ≤ q)
    (invImg : ∀ {A B : Scheme.{u}}, (A ⟶ B) →
      Sheaf B.smallEtaleTopology AddCommGrpCat.{u} ⥤
        Sheaf A.smallEtaleTopology AddCommGrpCat.{u})
    (baseChangeMap :
      ∀ {X' Y S' T : Scheme.{u}}
        (p : X' ⟶ X) (f' : X' ⟶ S') (s : S' ⟶ S)
        (h : Y ⟶ X') (e : Y ⟶ T) (g : T ⟶ S')
        [QuasiCompact g] [QuasiSeparated g]
        [HasSheafify T.smallEtaleTopology AddCommGrpCat.{u}]
        [HasSheafify S'.smallEtaleTopology AddCommGrpCat.{u}]
        [HasSheafify X'.smallEtaleTopology AddCommGrpCat.{u}]
        [HasSheafify Y.smallEtaleTopology AddCommGrpCat.{u}]
        [HasInjectiveResolutions
          (Sheaf T.smallEtaleTopology AddCommGrpCat.{u})]
        [HasInjectiveResolutions
          (Sheaf Y.smallEtaleTopology AddCommGrpCat.{u})],
        IsPullback p f' f s → IsPullback h e f' g →
        (F : Sheaf T.smallEtaleTopology AddCommGrpCat.{u}) → (q : ℕ) →
        (invImg f').obj
            (Sheaf.higherDirectImage (Scheme.smallEtalePullback g) F q) ⟶
          Sheaf.higherDirectImage (Scheme.smallEtalePullback h)
            ((invImg e).obj F) q)
    {X' S' Y T Y' T' : Scheme.{u}}
    (p : X' ⟶ X) (f' : X' ⟶ S') (s : S' ⟶ S)
    (h : Y ⟶ X') (e : Y ⟶ T) (g : T ⟶ S')
    (π' : Y' ⟶ Y) (e' : Y' ⟶ T') (π : T' ⟶ T)
    [QuasiCompact g] [QuasiSeparated g]
    [QuasiCompact (π ≫ g)] [QuasiSeparated (π ≫ g)]
    [IsIntegralHom π] [Surjective π]
    [HasSheafify T.smallEtaleTopology AddCommGrpCat.{u}]
    [HasSheafify T'.smallEtaleTopology AddCommGrpCat.{u}]
    [HasSheafify S'.smallEtaleTopology AddCommGrpCat.{u}]
    [HasSheafify X'.smallEtaleTopology AddCommGrpCat.{u}]
    [HasSheafify Y.smallEtaleTopology AddCommGrpCat.{u}]
    [HasSheafify Y'.smallEtaleTopology AddCommGrpCat.{u}]
    [HasInjectiveResolutions
      (Sheaf T.smallEtaleTopology AddCommGrpCat.{u})]
    [HasInjectiveResolutions
      (Sheaf T'.smallEtaleTopology AddCommGrpCat.{u})]
    [HasInjectiveResolutions
      (Sheaf Y.smallEtaleTopology AddCommGrpCat.{u})]
    [HasInjectiveResolutions
      (Sheaf Y'.smallEtaleTopology AddCommGrpCat.{u})]
    (sq_left : IsPullback p f' f s)
    (sq_unprimed : IsPullback h e f' g)
    (sq_cover : IsPullback π' e' e π)
    (sq_primed : IsPullback (π' ≫ h) e' f' (π ≫ g))
    (hBC : baseChangeCondition f n (q - 1) invImg baseChangeMap)
    (F : Sheaf T.smallEtaleTopology AddCommGrpCat.{u})
    (hF : (n : ℤ) • 𝟙 F = 0)
    (hiso :
      IsIso (baseChangeMap p f' s (π' ≫ h) e' (π ≫ g)
        sq_left sq_primed ((invImg π).obj F) q)) :
    IsIso (baseChangeMap p f' s h e g sq_left sq_unprimed F q) := sorry

end

end
