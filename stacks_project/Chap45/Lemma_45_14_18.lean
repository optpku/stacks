module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.WeilCohomology.ChernTheory.ScalarExtension

open AlgebraicGeometry CategoryTheory WeilCohomology

universe u v w x y z q w' x' y' z' q'

/- Lemma 45.14.18 -/
@[stacks 0FVT] #check (WeilCohomology.ChernTheory.axiomsOfScalarExtension : ∀ {k : Type u} [Field k] {k' : Type u} [Field k'] [Algebra k k']
    {F : Type v} [Field F] [CharZero F]
    {F' : Type v} [Field F'] [CharZero F'] [Algebra F F']
    {TateLine : Type x} {TateLine' : Type x'}
    [AddCommGroup TateLine] [Module F TateLine]
    [AddCommGroup TateLine'] [Module F' TateLine']
    {V : Type w} [Category.{z} V]
    {dimension : V → ℕ} {product : V → V → V}
    {fst : ∀ X Y, product X Y ⟶ X} {snd : ∀ X Y, product X Y ⟶ Y}
    {point : V} {CH : V → Type y} [∀ X, CommRing (CH X)]
    {CHgrade : ∀ X, ℤ → Submodule ℤ (CH X)} [∀ X, GradedAlgebra (CHgrade X)]
    {cyclePullback : ∀ {X Y : V}, (X ⟶ Y) → CHgrade Y →ₐᵍ[ℤ] CHgrade X}
    {cyclePushforward : ∀ {X Y : V}, (X ⟶ Y) → CH X →+ CH Y}
    {pointCycle : CHgrade point 0}
    {geometry : SmoothProjectiveContext k V dimension product fst snd point CH CHgrade
      cyclePullback cyclePushforward pointCycle}
    {H : V → Type q} [∀ X, Ring (H X)] [∀ X, Algebra F (H X)]
    {V' : Type w'} [Category.{z'} V']
    {dimension' : V' → ℕ} {product' : V' → V' → V'}
    {fst' : ∀ X Y, product' X Y ⟶ X} {snd' : ∀ X Y, product' X Y ⟶ Y}
    {point' : V'} {CH' : V' → Type y'} [∀ X, CommRing (CH' X)]
    {CHgrade' : ∀ X, ℤ → Submodule ℤ (CH' X)} [∀ X, GradedAlgebra (CHgrade' X)]
    {cyclePullback' : ∀ {X Y : V'}, (X ⟶ Y) → CHgrade' Y →ₐᵍ[ℤ] CHgrade' X}
    {cyclePushforward' : ∀ {X Y : V'}, (X ⟶ Y) → CH' X →+ CH' Y}
    {pointCycle' : CHgrade' point' 0}
    {geometry' : SmoothProjectiveContext k' V' dimension' product' fst' snd' point'
      CH' CHgrade' cyclePullback' cyclePushforward' pointCycle'}
    {H' : V' → Type q'} [∀ X, Ring (H' X)] [∀ X, Algebra F' (H' X)]
    (baseChange : V ⥤ V')
    (T : ChernTheory F TateLine geometry H)
    (T' : ChernTheory F' TateLine' geometry' H')
    (e : T.ScalarExtension T' baseChange), T'.Axioms → T.Axioms)
