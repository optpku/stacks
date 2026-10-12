/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.BaseChange.IntegralFactor
import StacksCheckRecall

@[expose] public section

open CategoryTheory
open AlgebraicGeometry

universe u

/- Lemma 59.88.4: assume `BC(f, n, q - 1)` for some `q ≥ 1`. In cartesian
diagrams relating `f : X ⟶ S` to `f'`, `f''`, with `π : S'' ⟶ S'` integral and
`g' : T ⟶ S''` quasi-compact and quasi-separated, if the degree-`q` étale
higher-direct-image base-change map for the composite square
`(f', g = g' ≫ π, h = h' ≫ π')` is an isomorphism on an `n`-annihilated abelian
sheaf `F` on `Tₑₜ`, then the corresponding map for the inner square
`(f'', g', h')` is an isomorphism. -/
@[stacks 0F05] #check
  (AlgebraicGeometry.Scheme.Etale.BaseChange.higherMap_isIso_of_integral_factor :
    ∀ {X S : Scheme.{u}} (f : X ⟶ S) (n : ℤ) {q : ℕ} (hq : 1 ≤ q)
    {X' S' X'' S'' Y T : Scheme.{u}}
    (p : X' ⟶ X) (f' : X' ⟶ S') (s : S' ⟶ S)
    (π' : X'' ⟶ X') (f'' : X'' ⟶ S'') (π : S'' ⟶ S')
    (h' : Y ⟶ X'') (e : Y ⟶ T) (g' : T ⟶ S'')
    [IsIntegralHom π] [QuasiCompact g'] [QuasiSeparated g']
    (sq_left : IsPullback p f' f s)
    (sq_mid : IsPullback π' f'' f' π)
    (sq_inner : IsPullback h' e f'' g')
    (sq_outer : IsPullback (h' ≫ π') e f' (g' ≫ π))
    (hBC : AlgebraicGeometry.Scheme.Etale.BaseChange.Holds f n (q - 1))
    (F : Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1})
    (hF : n • 𝟙 F = 0)
    (hiso : IsIso (AlgebraicGeometry.Scheme.Etale.BaseChange.higherMap
      f' (h' ≫ π') e (g' ≫ π) sq_outer q F)),
    IsIso (AlgebraicGeometry.Scheme.Etale.BaseChange.higherMap
      f'' h' e g' sq_inner q F))

end
