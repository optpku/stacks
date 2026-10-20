module

public import ReasLib.AlgebraicGeometry.WeilCohomology.Pushforward
import StacksCheckRecall

@[expose] public section

open CategoryTheory
open scoped TensorProduct

universe u v w x

/- Lemma 45.9.2: for nonempty equidimensional smooth projective objects `X` and `Y`,
pushforward along the second projection sends the Künneth tensor `a ⊗ₜ[F] b` to
`(integral hX a) • b`. The hypotheses record (D0), (D1), and (D3), together with
the Künneth and indexed trace properties in (A) and (B). -/
@[stacks 0FHC] #check
  (WeilCohomology.pushforward_snd_kunnethMap_tmul_of_indexedTrace :
    ∀ {V : Type u} [Category.{v} V] {F : Type w} [Field F] [CharZero F]
      (H : V → Type x) [∀ Z, Ring (H Z)] [∀ Z, Algebra F (H Z)]
      (product : V → V → V) (fst : ∀ X Y, product X Y ⟶ X)
      (snd : ∀ X Y, product X Y ⟶ Y)
      (pullback : ∀ {X Y : V}, (X ⟶ Y) → H Y →ₐ[F] H X)
      (IsNonemptyEquidimensional : V → ℕ → Prop)
      (product_isNonemptyEquidimensional : ∀ {X Y : V} {d e : ℕ},
        IsNonemptyEquidimensional X d → IsNonemptyEquidimensional Y e →
          IsNonemptyEquidimensional (product X Y) (d + e))
      (indexedPushforward : ∀ {X Y : V} {d e : ℕ},
        IsNonemptyEquidimensional X d → IsNonemptyEquidimensional Y e →
          (X ⟶ Y) → H X →ₗ[F] H Y)
      (kunnethMap : ∀ X Y, H X ⊗[F] H Y →ₗ[F] H (product X Y))
      (integral : ∀ {X : V} {d : ℕ},
        IsNonemptyEquidimensional X d → H X →ₗ[F] F)
      (h_kunneth : ∀ X Y, Function.Bijective (kunnethMap X Y))
      (kunnethMap_tmul : ∀ {X Y : V} (a : H X) (b : H Y),
        kunnethMap X Y (a ⊗ₜ[F] b) =
          pullback (fst X Y) a * pullback (snd X Y) b)
      (integral_kunnethMap_tmul : ∀ {X Y : V} {d e : ℕ}
        (hX : IsNonemptyEquidimensional X d) (hY : IsNonemptyEquidimensional Y e)
        (a : H X) (b : H Y),
        integral (product_isNonemptyEquidimensional hX hY)
            (kunnethMap X Y (a ⊗ₜ[F] b)) = integral hX a * integral hY b)
      (pushforward_adjoint : ∀ {S T : V} {d e : ℕ}
        (hS : IsNonemptyEquidimensional S d) (hT : IsNonemptyEquidimensional T e)
        (f : S ⟶ T) (x : H S) (c : H T),
        integral hS (x * pullback f c) =
          integral hT (indexedPushforward hS hT f x * c))
      (poincare_separates : ∀ {X : V} {d : ℕ}
        (hX : IsNonemptyEquidimensional X d) (x y : H X),
        (∀ c : H X, integral hX (x * c) = integral hX (y * c)) → x = y)
      {X Y : V} {d e : ℕ} (hX : IsNonemptyEquidimensional X d)
      (hY : IsNonemptyEquidimensional Y e) (a : H X) (b : H Y),
      indexedPushforward (product_isNonemptyEquidimensional hX hY) hY (snd X Y)
          (kunnethMap X Y (a ⊗ₜ[F] b)) = (integral hX a) • b)
