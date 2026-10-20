module

public import ReasLib.AlgebraicGeometry.WeilCohomology.Pushforward
import StacksCheckRecall

@[expose] public section

open CategoryTheory

universe u v w x

namespace WeilCohomology

variable {V : Type u} [Category.{v} V]
variable {F : Type w} [Field F] [CharZero F]
variable (H : V → Type x) [∀ X, Ring (H X)] [∀ X, Algebra F (H X)]
variable (pullback : ∀ {X Y : V}, (X ⟶ Y) → H Y →ₐ[F] H X)
variable (pushforward : ∀ {X Y : V}, (X ⟶ Y) → H X →ₗ[F] H Y)
variable (trace : ∀ X : V, H X →ₗ[F] F)

/- Lemma 45.7.1 (1): assuming data (D1) and (D3) satisfying Poincaré duality (A),
for a morphism `f : X ⟶ Y` of smooth projective varieties the pushforward satisfies
`f₍*₎ (f⁎ b * a) = b * f₍*₎ a`. Here `H X` denotes total cohomology and `trace X`
is the top-degree trace, extended by zero outside the top degree. -/
@[stacks 0FGT] #check
  (WeilCohomology.projectionFormula H pullback pushforward trace :
    (∀ {X Y : V} (f : X ⟶ Y) (b : H Y) (a : H X),
      trace X (pullback f b * a) = trace Y (b * pushforward f a)) →
    (∀ (X : V) (x y : H X),
      (∀ c : H X, trace X (c * x) = trace X (c * y)) → x = y) →
    ∀ {X Y : V} (f : X ⟶ Y) (b : H Y) (a : H X),
      pushforward f (pullback f b * a) = b * pushforward f a)

/- Lemma 45.7.1 (2): assuming data (D1) and (D3) satisfying Poincaré duality (A),
for morphisms `f : X ⟶ Y` and `g : Y ⟶ Z` of smooth projective varieties,
pushforward is functorial: `g₍*₎ ∘ f₍*₎ = (f ≫ g)₍*₎`. -/
@[stacks 0FGT] #check
  (WeilCohomology.pushforward_comp H pullback pushforward trace :
    (∀ {X Y Z : V} (f : X ⟶ Y) (g : Y ⟶ Z),
      pullback (f ≫ g) = (pullback f).comp (pullback g)) →
    (∀ {X Y : V} (f : X ⟶ Y) (b : H Y) (a : H X),
      trace X (pullback f b * a) = trace Y (b * pushforward f a)) →
    (∀ (X : V) (x y : H X),
      (∀ c : H X, trace X (c * x) = trace X (c * y)) → x = y) →
    ∀ {X Y Z : V} (f : X ⟶ Y) (g : Y ⟶ Z),
      (pushforward g).comp (pushforward f) = pushforward (f ≫ g))

end WeilCohomology
