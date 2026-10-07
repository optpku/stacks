module

public import stacks_project.Chap83.Lemma_83_3_6_Square

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry AlgebraicSpace
open GroupoidAlgebraicSpace
open scoped Bicategory

namespace AlgebraicGeometry.GroupoidAlgebraicSpace

/-- Lemma 83.3.6: Let `S` be a scheme, `B` an algebraic space over `S`, and
`(U, R, s, t, c)` a groupoid in algebraic spaces over `B`. Let `U ⟶ X` be an
`R`-invariant morphism of algebraic spaces over `B`, and let `g : X' ⟶ X` be a
morphism of algebraic spaces over `B`. With `(U', R', s', t', c')` the base change
of Lemma 83.3.3, the square with apex `[U'/R']`, legs `[U'/R'] ⟶ [U/R]` and
`[U'/R'] ⟶ 𝒮_{X'}`, and cospan `[U/R] ⟶ 𝒮_X ← 𝒮_{X'}` is a 2-fibre product of
stacks in groupoids over `(Sch/S)_fppf`. -/
@[stacks 0DTG, instance]
instance baseChangeQuotientCone_isBilimit {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) {X X' : Over B} (φ : G.U ⟶ X)
    (hφ : G.toPreRelation.IsInvariantHom φ) (g : X' ⟶ X) :
    (baseChangeQuotientCone G φ hφ g).IsBilimit := sorry

end AlgebraicGeometry.GroupoidAlgebraicSpace
