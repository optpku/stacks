module

public import ReasLib.AlgebraicGeometry.WeilCohomology.SchemeClassical.DimensionZero
public import ReasLib.AlgebraicGeometry.Scheme.BaseChange.Affine
public import Mathlib.RingTheory.TensorProduct.Maps

@[expose] public section

noncomputable section

open CategoryTheory
open scoped TensorProduct

universe u v w x y z

namespace WeilCohomology.SchemeClassicalTheory

open AlgebraicGeometry

variable {k : Type u} [Field k]
variable {F : Type v} [Field F] [CharZero F]
variable {TateLine : Type w} [AddCommGroup TateLine] [Module F TateLine]
variable {V : Type w} [Category.{z} V]
variable {dimension : V → ℕ} {product : V → V → V}
variable {fst : ∀ X Y, product X Y ⟶ X} {snd : ∀ X Y, product X Y ⟶ Y}
variable {point : V} {H : V → Type x} {CH : V → Type y}
variable [∀ X, Ring (H X)] [∀ X, Algebra F (H X)] [∀ X, CommRing (CH X)]
variable {Hgrade : ∀ X, ℤ × ℤ → Submodule F (H X)}
variable {CHgrade : ∀ X, ℤ → Submodule ℤ (CH X)}
variable [∀ X, GradedAlgebra (Hgrade X)] [∀ X, GradedAlgebra (CHgrade X)]
variable {cyclePullback : ∀ {X Y : V},
  (X ⟶ Y) → CHgrade Y →ₐᵍ[ℤ] CHgrade X}
variable {cyclePushforward : ∀ {X Y : V}, (X ⟶ Y) → CH X →+ CH Y}

variable (T : SchemeClassicalTheory k F TateLine V dimension product fst snd point
  H CH Hgrade CHgrade cyclePullback cyclePushforward)

/-- Pullback restricted to the bidegree `(0, 0)` commutative rings. -/
noncomputable def degreeZeroPullback {X Y : V} (f : X ⟶ Y) :
    Hgrade Y (0, 0) →+* Hgrade X (0, 0) :=
  (T.pullback f).toGradedRingHom.gradedZeroRingHom

/-- Coercing a degree-zero pullback to total cohomology recovers the original pullback. -/
theorem coe_degreeZeroPullback {X Y : V} (f : X ⟶ Y)
    (a : Hgrade Y (0, 0)) :
    (T.degreeZeroPullback f a : H X) = T.pullback f a := sorry

/-- Degree-zero pullback along an identity morphism is the identity ring homomorphism. -/
theorem degreeZeroPullback_id (X : V) :
    T.degreeZeroPullback (𝟙 X) = RingHom.id (Hgrade X (0, 0)) := sorry

/-- Degree-zero pullback reverses composition. -/
theorem degreeZeroPullback_comp {X Y Z : V} (f : X ⟶ Y) (g : Y ⟶ Z) :
    T.degreeZeroPullback (f ≫ g) =
      (T.degreeZeroPullback f).comp (T.degreeZeroPullback g) := sorry

/-- The action of degree-zero cohomology of a base on the total cohomology of an object
over that base. -/
noncomputable def degreeZeroAction {X S : V} (f : X ⟶ S) :
    Hgrade S (0, 0) →+* H X :=
  (T.pullback f).toAlgHom.toRingHom.comp
    (SetLike.GradeZero.subring (Hgrade S)).subtype

/-- The degree-zero action is pullback followed by the inclusion into total cohomology. -/
theorem degreeZeroAction_apply {X S : V} (f : X ⟶ S)
    (a : Hgrade S (0, 0)) :
    T.degreeZeroAction f a = T.pullback f a := sorry

/-- Degree-zero classes pulled back from the base are central in total cohomology. -/
theorem degreeZeroAction_commutes {X S : V} (f : X ⟶ S)
    (a : Hgrade S (0, 0)) (b : H X) :
    T.degreeZeroAction f a * b = b * T.degreeZeroAction f a := sorry

/-- The pullback-product pairing is additive in its total-cohomology argument. -/
theorem baseChangePairing_add_left
    {S'' X X'' : V} (p : X'' ⟶ X) (q : X'' ⟶ S'')
    (a₁ a₂ : H X) (b : Hgrade S'' (0, 0)) :
    T.pullback p (a₁ + a₂) * T.degreeZeroAction q b =
      T.pullback p a₁ * T.degreeZeroAction q b +
        T.pullback p a₂ * T.degreeZeroAction q b := sorry

/-- The pullback-product pairing is linear in its total-cohomology argument over the
degree-zero cohomology of the base. -/
theorem baseChangePairing_smul_left
    {S' S'' X X'' : V} (s : X ⟶ S') (p : X'' ⟶ X) (q : X'' ⟶ S'')
    (r : Hgrade S' (0, 0)) (a : H X) (b : Hgrade S'' (0, 0)) :
    T.pullback p (T.degreeZeroAction s r * a) * T.degreeZeroAction q b =
      T.degreeZeroAction (p ≫ s) r *
        (T.pullback p a * T.degreeZeroAction q b) := sorry

/-- The pullback-product pairing is additive in its degree-zero argument. -/
theorem baseChangePairing_add_right
    {S'' X X'' : V} (p : X'' ⟶ X) (q : X'' ⟶ S'')
    (a : H X) (b₁ b₂ : Hgrade S'' (0, 0)) :
    T.pullback p a * T.degreeZeroAction q (b₁ + b₂) =
      T.pullback p a * T.degreeZeroAction q b₁ +
        T.pullback p a * T.degreeZeroAction q b₂ := sorry

/-- For a realized commutative square, the pullback-product pairing is balanced over the
degree-zero cohomology of the original base. -/
theorem baseChangePairing_smul_right
    {S' S'' X X'' : V} (s : X ⟶ S') (g : S'' ⟶ S')
    (p : X'' ⟶ X) (q : X'' ⟶ S'')
    (h_square : IsPullback (T.scheme.map p).left (T.scheme.map q).left
      (T.scheme.map s).left (T.scheme.map g).left)
    (r : Hgrade S' (0, 0)) (a : H X) (b : Hgrade S'' (0, 0)) :
    T.pullback p a *
        T.degreeZeroAction q (T.degreeZeroPullback g r * b) =
      T.degreeZeroAction (p ≫ s) r *
        (T.pullback p a * T.degreeZeroAction q b) := sorry

/-- The canonical cohomological base-change map, obtained by multiplying the two pullbacks
from a realized pullback square. -/
noncomputable def baseChangeComparison
    {S' S'' X X'' : V} (s : X ⟶ S') (g : S'' ⟶ S')
    (p : X'' ⟶ X) (q : X'' ⟶ S'')
    (h_square : IsPullback (T.scheme.map p).left (T.scheme.map q).left
      (T.scheme.map s).left (T.scheme.map g).left) :
    -- Local instance justification (instance diamond): the ring structure is determined by `T`, which the degree-zero carrier does not determine.
    letI : CommRing (Hgrade S' (0, 0)) := T.degreeZeroCommRing S'
    -- Local instance justification (instance diamond): the ring structure is determined by `T`, which the degree-zero carrier does not determine.
    letI : CommRing (Hgrade S'' (0, 0)) := T.degreeZeroCommRing S''
    -- Local instance justification (noncanonical choice): this action is induced by `s`.
    letI : Algebra (Hgrade S' (0, 0)) (H X) :=
      (T.degreeZeroAction s).toAlgebra' (T.degreeZeroAction_commutes s)
    -- Local instance justification (noncanonical choice): this action is induced by `g`.
    letI : Algebra (Hgrade S' (0, 0)) (Hgrade S'' (0, 0)) :=
      (T.degreeZeroPullback g).toAlgebra
    -- Local instance justification (noncanonical choice): this action is induced by `p ≫ s`.
    letI : Algebra (Hgrade S' (0, 0)) (H X'') :=
      (T.degreeZeroAction (p ≫ s)).toAlgebra'
        (T.degreeZeroAction_commutes (p ≫ s))
    H X ⊗[Hgrade S' (0, 0)] Hgrade S'' (0, 0) →ₗ[Hgrade S' (0, 0)] H X'' :=
  -- Local instance justification (instance diamond): the ring structure is determined by `T`, which the degree-zero carrier does not determine.
  letI : CommRing (Hgrade S' (0, 0)) := T.degreeZeroCommRing S'
  -- Local instance justification (instance diamond): the ring structure is determined by `T`, which the degree-zero carrier does not determine.
  letI : CommRing (Hgrade S'' (0, 0)) := T.degreeZeroCommRing S''
  -- Local instance justification (noncanonical choice): this action is induced by `s`.
  letI : Algebra (Hgrade S' (0, 0)) (H X) :=
    (T.degreeZeroAction s).toAlgebra' (T.degreeZeroAction_commutes s)
  -- Local instance justification (noncanonical choice): this action is induced by `g`.
  letI : Algebra (Hgrade S' (0, 0)) (Hgrade S'' (0, 0)) :=
    (T.degreeZeroPullback g).toAlgebra
  -- Local instance justification (noncanonical choice): this action is induced by `p ≫ s`.
  letI : Algebra (Hgrade S' (0, 0)) (H X'') :=
    (T.degreeZeroAction (p ≫ s)).toAlgebra'
      (T.degreeZeroAction_commutes (p ≫ s))
  TensorProduct.lift
    (LinearMap.mk₂ (Hgrade S' (0, 0))
      (fun a b ↦ T.pullback p a * T.degreeZeroAction q b)
      (T.baseChangePairing_add_left p q)
      (T.baseChangePairing_smul_left s p q)
      (T.baseChangePairing_add_right p q)
      (T.baseChangePairing_smul_right s g p q h_square))

/-- On a pure tensor, `baseChangeComparison` is the product of the pullbacks from the two
factors of the realized square. -/
theorem baseChangeComparison_tmul
    {S' S'' X X'' : V} (s : X ⟶ S') (g : S'' ⟶ S')
    (p : X'' ⟶ X) (q : X'' ⟶ S'')
    (h_square : IsPullback (T.scheme.map p).left (T.scheme.map q).left
      (T.scheme.map s).left (T.scheme.map g).left)
    (a : H X) (b : Hgrade S'' (0, 0)) :
    -- Local instance justification (instance diamond): the ring structure is determined by `T`, which the degree-zero carrier does not determine.
    letI : CommRing (Hgrade S' (0, 0)) := T.degreeZeroCommRing S'
    -- Local instance justification (instance diamond): the ring structure is determined by `T`, which the degree-zero carrier does not determine.
    letI : CommRing (Hgrade S'' (0, 0)) := T.degreeZeroCommRing S''
    -- Local instance justification (noncanonical choice): this action is induced by `s`.
    letI : Algebra (Hgrade S' (0, 0)) (H X) :=
      (T.degreeZeroAction s).toAlgebra' (T.degreeZeroAction_commutes s)
    -- Local instance justification (noncanonical choice): this action is induced by `g`.
    letI : Algebra (Hgrade S' (0, 0)) (Hgrade S'' (0, 0)) :=
      (T.degreeZeroPullback g).toAlgebra
    -- Local instance justification (noncanonical choice): this action is induced by `p ≫ s`.
    letI : Algebra (Hgrade S' (0, 0)) (H X'') :=
      (T.degreeZeroAction (p ≫ s)).toAlgebra'
        (T.degreeZeroAction_commutes (p ≫ s))
    T.baseChangeComparison s g p q h_square
        (a ⊗ₜ[Hgrade S' (0, 0)] b) =
      T.pullback p a * T.degreeZeroAction q b := sorry

/-- Finite separable base change is bijective for the cohomology of a smooth projective scheme. -/
theorem cohomologyBaseChange_bijective_of_finiteSeparable
    {k' k'' : Type u} [CommRing k'] [CommRing k'']
    [Algebra k k'] [Algebra k' k''] [Algebra k k''] [IsScalarTower k k' k'']
    [Module.Finite k k'] [Algebra.IsSeparable k k']
    [Module.Finite k' k''] [Algebra.IsSeparable k' k'']
    (T : SchemeClassicalTheory k F TateLine V dimension product fst snd point
      H CH Hgrade CHgrade cyclePullback cyclePushforward)
    {S' S'' X X'' : V} (s : X ⟶ S') (g : S'' ⟶ S')
    (p : X'' ⟶ X) (q : X'' ⟶ S'')
    (e' : T.scheme.obj S' ≅
      Over.mk (Scheme.AffineBaseChange.specMap k k'))
    (e'' : T.scheme.obj S'' ≅
      Over.mk (Scheme.AffineBaseChange.specMap k k''))
    (h_g : T.scheme.map g = e''.hom ≫
      Scheme.AffineBaseChange.specMapOverBase k k' k'' ≫ e'.inv)
    [Smooth (T.scheme.map s ≫ e'.hom).left]
    [Projective (T.scheme.map s ≫ e'.hom).left]
    (h_square : IsPullback (T.scheme.map p).left (T.scheme.map q).left
      (T.scheme.map s).left (T.scheme.map g).left) :
    Function.Bijective (T.baseChangeComparison s g p q h_square) := sorry

end WeilCohomology.SchemeClassicalTheory
