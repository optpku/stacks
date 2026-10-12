/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.BaseChange.Condition
public import Mathlib.AlgebraicGeometry.Morphisms.Integral

@[expose] public section

open CategoryTheory
open AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Etale.BaseChange

/-- Suppose the étale base-change condition for `f` and `n` holds through degree `q - 1`,
with `1 ≤ q`. In a tower of cartesian squares whose intervening base morphism `π` is
integral and whose final base morphism `g'` is quasi-compact and quasi-separated, the
canonical degree-`q` comparison for an `n`-annihilated abelian sheaf is an isomorphism
for the inner square whenever it is an isomorphism for the outer rectangle. -/
theorem higherMap_isIso_of_integral_factor
    {X S : Scheme.{u}} (f : X ⟶ S) (n : ℤ) {q : ℕ} (hq : 1 ≤ q)
    {X' S' X'' S'' Y T : Scheme.{u}}
    (p : X' ⟶ X) (f' : X' ⟶ S') (s : S' ⟶ S)
    (π' : X'' ⟶ X') (f'' : X'' ⟶ S'') (π : S'' ⟶ S')
    (h' : Y ⟶ X'') (e : Y ⟶ T) (g' : T ⟶ S'')
    [IsIntegralHom π] [QuasiCompact g'] [QuasiSeparated g']
    (sq_left : IsPullback p f' f s)
    (sq_mid : IsPullback π' f'' f' π)
    (sq_inner : IsPullback h' e f'' g')
    (sq_outer : IsPullback (h' ≫ π') e f' (g' ≫ π))
    (hBC : Holds f n (q - 1))
    (F : Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1})
    (hF : n • 𝟙 F = 0)
    (hiso : IsIso (higherMap f' (h' ≫ π') e (g' ≫ π) sq_outer q F)) :
    IsIso (higherMap f'' h' e g' sq_inner q F) := sorry

end AlgebraicGeometry.Scheme.Etale.BaseChange

end
