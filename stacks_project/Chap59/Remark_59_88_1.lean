module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.BaseChange.Condition
import StacksCheckRecall

@[expose] public section

open CategoryTheory
open AlgebraicGeometry

universe u

export AlgebraicGeometry.Scheme.Etale (baseChangeCondition baseChangeCondition_mono)

/- Remark 59.88.1: for `f : X ⟶ S`, the condition `BC(f, n, q₀)` requires that in
every pair of cartesian squares

`X' ⟶ X`, `X' ⟶ S' ⟶ S` and `Y ⟶ X'`, `Y ⟶ T ⟶ S'`,

the base-change map
`(f')⁻¹ R^q g_* F ⟶ R^q h_* e⁻¹ F` is an isomorphism for `q ≤ q₀` and every
abelian sheaf `F` on `Tₑₜ` annihilated by `n`. -/
@[stacks 0F02] #check
  (AlgebraicGeometry.Scheme.Etale.baseChangeCondition :
    ∀ {X S : Scheme.{u}} (f : X ⟶ S) (n : ℤ) (q₀ : ℕ)
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
            ((invImg e).obj F) q), Prop)

end
