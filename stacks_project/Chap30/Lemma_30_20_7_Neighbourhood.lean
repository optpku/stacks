module

public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.AlgebraicGeometry.Stalk
public import Mathlib.RingTheory.Ideal.Quotient.PowTransition
public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic

/-!
# Infinitesimal neighbourhoods of a fibre

For a morphism `f : X ⟶ Y` and a point `y`, the infinitesimal neighbourhood
`scheme f y n` is the fibre product `Spec(𝒪_{Y,y} ⧸ m_y^{n+1}) ×_Y X`. This is
the source's `X_{n+1}`, so `n = 0` recovers the ordinary fibre `X_y`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry
open IsLocalRing

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Hom
namespace FiberNeighbourhood

variable {X Y : Scheme.{u}}

/-- The quotient ring `𝒪_{Y,y} ⧸ m_y^{n+1}` of the stalk at `y`. -/
abbrev quotientRing (y : Y) (n : ℕ) : Type u :=
  Y.presheaf.stalk y ⧸ maximalIdeal (Y.presheaf.stalk y) ^ (n + 1)

/-- The infinitesimal quotient of a local stalk is a local ring. -/
instance isLocalRing_quotientRing (y : Y) (n : ℕ) : IsLocalRing (quotientRing y n) :=
  sorry

/-- The spectrum of the infinitesimal quotient `𝒪_{Y,y} ⧸ m_y^{n+1}`. -/
abbrev quotientSpec (y : Y) (n : ℕ) : Scheme.{u} :=
  Spec (CommRingCat.of (quotientRing y n))

/-- The canonical morphism `c_{n+1} : Spec(𝒪_{Y,y} ⧸ m_y^{n+1}) ⟶ Y`. -/
def toBase (y : Y) (n : ℕ) : quotientSpec y n ⟶ Y :=
  Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (maximalIdeal (Y.presheaf.stalk y) ^ (n + 1)))) ≫
    Y.fromSpecStalk y

/-- `toBase y n` is `Spec.map` of the quotient map, postcomposed with `fromSpecStalk`. -/
theorem toBase_def (y : Y) (n : ℕ) :
    toBase y n =
      Spec.map
          (CommRingCat.ofHom
            (Ideal.Quotient.mk (maximalIdeal (Y.presheaf.stalk y) ^ (n + 1)))) ≫
        Y.fromSpecStalk y :=
  sorry

/-- The infinitesimal neighbourhood `X_{n+1} = Spec(𝒪_{Y,y} ⧸ m_y^{n+1}) ×_Y X`. -/
def scheme (f : X ⟶ Y) (y : Y) (n : ℕ) : Scheme.{u} :=
  pullback f (toBase y n)

/-- The neighbourhood scheme is the chosen fibre product along `toBase`. -/
theorem scheme_def (f : X ⟶ Y) (y : Y) (n : ℕ) :
    scheme f y n = pullback f (toBase y n) :=
  sorry

/-- The closed immersion `i_{n+1} : X_{n+1} ⟶ X` of an infinitesimal neighbourhood. -/
def ι (f : X ⟶ Y) (y : Y) (n : ℕ) : scheme f y n ⟶ X :=
  pullback.fst f (toBase y n)

/-- The neighbourhood inclusion is the first projection of the fibre product. -/
theorem ι_eq_fst (f : X ⟶ Y) (y : Y) (n : ℕ) :
    ι f y n = pullback.fst f (toBase y n) :=
  sorry

/-- The structure morphism `f_{n+1} : X_{n+1} ⟶ Spec(𝒪_{Y,y} ⧸ m_y^{n+1})`. -/
def toSpec (f : X ⟶ Y) (y : Y) (n : ℕ) : scheme f y n ⟶ quotientSpec y n :=
  pullback.snd f (toBase y n)

/-- The neighbourhood structure morphism is the second projection of the fibre product. -/
theorem toSpec_eq_snd (f : X ⟶ Y) (y : Y) (n : ℕ) :
    toSpec f y n = pullback.snd f (toBase y n) :=
  sorry

/-- The pullback sheaf `ℱ_{n+1} = i_{n+1}^* ℱ` on an infinitesimal neighbourhood. -/
def sheaf (f : X ⟶ Y) (F : X.Modules) (y : Y) (n : ℕ) : (scheme f y n).Modules :=
  (Scheme.Modules.pullback (ι f y n)).obj F

/-- The neighbourhood sheaf is the module pullback of `F` along `ι`. -/
theorem sheaf_eq (f : X ⟶ Y) (F : X.Modules) (y : Y) (n : ℕ) :
    sheaf f F y n = (Scheme.Modules.pullback (ι f y n)).obj F :=
  sorry

/-- The displayed square of an infinitesimal neighbourhood is a pullback square. -/
theorem isPullback_ι_toSpec (f : X ⟶ Y) (y : Y) (n : ℕ) :
    IsPullback (ι f y n) (toSpec f y n) f (toBase y n) :=
  sorry

/-- The quotient transition `𝒪_{Y,y} ⧸ m_y^{n+2} ⟶ 𝒪_{Y,y} ⧸ m_y^{n+1}`. -/
def quotientStep (y : Y) (n : ℕ) :
    quotientRing y (n + 1) →+* quotientRing y n :=
  Ideal.Quotient.factorPow (maximalIdeal (Y.presheaf.stalk y)) (Nat.le_succ (n + 1))

/-- Successive base morphisms factor through the spectrum of `quotientStep`. -/
theorem toBase_succ_factor (y : Y) (n : ℕ) :
    toBase y n ≫ 𝟙 Y =
      Spec.map (CommRingCat.ofHom (quotientStep y n)) ≫ toBase y (n + 1) :=
  sorry

/-- The closed immersion of successive infinitesimal neighbourhoods of the fibre. -/
def schemeTransition (f : X ⟶ Y) (y : Y) (n : ℕ) :
    scheme f y n ⟶ scheme f y (n + 1) :=
  pullback.map f (toBase y n) f (toBase y (n + 1)) (𝟙 X)
    (Spec.map (CommRingCat.ofHom (quotientStep y n))) (𝟙 Y)
    (Category.id_comp f).symm (toBase_succ_factor y n)

/-- Neighbourhood transitions lie over `X` through `ι`. -/
theorem schemeTransition_ι (f : X ⟶ Y) (y : Y) (n : ℕ) :
    schemeTransition f y n ≫ ι f y (n + 1) = ι f y n :=
  sorry

/-- Neighbourhood transitions lie over the quotient spectra through `toSpec`. -/
theorem schemeTransition_toSpec (f : X ⟶ Y) (y : Y) (n : ℕ) :
    schemeTransition f y n ≫ toSpec f y (n + 1) =
      toSpec f y n ≫ Spec.map (CommRingCat.ofHom (quotientStep y n)) :=
  sorry

/-- The ring identification `𝒪_{Y,y} ⧸ m_y = κ(y)` used at stage `n = 0`. -/
def residueQuotientEquiv (y : Y) :
    quotientRing y 0 ≃+* IsLocalRing.ResidueField (Y.presheaf.stalk y) :=
  Ideal.quotEquivOfEq (pow_one (maximalIdeal (Y.presheaf.stalk y)))

/-- Stage `0` of the base morphism factors through the residue-field morphism of `y`. -/
theorem toBase_zero_fromSpecResidueField (y : Y) :
    toBase y 0 ≫ 𝟙 Y =
      Spec.map (CommRingCat.ofHom (residueQuotientEquiv y).symm.toRingHom) ≫
        Y.fromSpecResidueField y :=
  sorry

/-- The residue-field morphism of `y` factors through stage `0` of `toBase`. -/
theorem fromSpecResidueField_toBase_zero (y : Y) :
    Y.fromSpecResidueField y ≫ 𝟙 Y =
      Spec.map (CommRingCat.ofHom (residueQuotientEquiv y).toRingHom) ≫
        toBase y 0 :=
  sorry

/-- Stage `0` of the neighbourhood recovers the scheme-theoretic fibre `X_y`. -/
def schemeZeroFiberIso (f : X ⟶ Y) (y : Y) : scheme f y 0 ≅ f.fiber y where
  hom :=
    pullback.map f (toBase y 0) f (Y.fromSpecResidueField y) (𝟙 X)
      (Spec.map (CommRingCat.ofHom (residueQuotientEquiv y).symm.toRingHom)) (𝟙 Y)
      (Category.id_comp f).symm (toBase_zero_fromSpecResidueField y)
  inv :=
    pullback.map f (Y.fromSpecResidueField y) f (toBase y 0) (𝟙 X)
      (Spec.map (CommRingCat.ofHom (residueQuotientEquiv y).toRingHom)) (𝟙 Y)
      (Category.id_comp f).symm (fromSpecResidueField_toBase_zero y)
  hom_inv_id := sorry
  inv_hom_id := sorry

end FiberNeighbourhood
end AlgebraicGeometry.Scheme.Hom
