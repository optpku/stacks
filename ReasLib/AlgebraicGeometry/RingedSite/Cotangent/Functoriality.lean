module

public import Mathlib.CategoryTheory.CommSq
public import ReasLib.AlgebraicGeometry.RingedSite.Module.ChangeOfRings
public import ReasLib.AlgebraicGeometry.RingedSite.Topos.HomOfSite
public import ReasLib.AlgebraicGeometry.RingedSite.Topos.TwoMorphism.Square
public import ReasLib.CategoryTheory.Sites.Topos.Composition
public import ReasLib.AlgebraicGeometry.RingedSite.Cotangent.PolynomialSite

/-!
# The double square of ringed topoi induced by base change of `C_{B/A}`

A commutative square of rings induces identity-on-topoi change-of-rings maps `h` and `f`,
the map `g` of the functor `u`, and two commutative squares of ringed topoi.
-/

@[expose] public section

open CategoryTheory
open RingedSite.Cotangent
open RingedSite.ToposHom
open SheafOfModules.RingedSite

noncomputable section

universe u

namespace RingedSite.Cotangent.Functoriality

variable {A A' B B' : CommRingCat.{u}}
variable {α : A ⟶ B} {ρ : A ⟶ A'} {β : A' ⟶ B'} {φ : B ⟶ B'}

/-- The same-site ringed-site morphism on `C_{B'/A'}` induced by `B ⟶ B'`. -/
def hHom (sq : CommSq ρ α β φ) :
    constRingedSite β B' ⟶ constRingedSite β B :=
  sameSiteHom.{u + 1, u, u + 1} (constSheafMapLift β φ)

/-- The morphism `h` is the identity on `Sh(C')` and is given by `B ⟶ B'` on sheaves of rings. -/
def h (sq : CommSq ρ α β φ) :
    ToposHom (constRingedSite β B') (constRingedSite β B) :=
  Hom.toToposHom (hHom sq)

/-- The same-site ringed-site morphism on the point induced by `B ⟶ B'`. -/
def fHom (sq : CommSq ρ α β φ) : point B' ⟶ point B :=
  sameSiteHom.{u + 1, u + 1, u + 1} (pointRingSheafMap φ)

/-- The morphism `f` is the identity on `Sh(*)` and is given by `B ⟶ B'` on sheaves of rings. -/
def f (sq : CommSq ρ α β φ) : ToposHom (point B') (point B) :=
  Hom.toToposHom (fHom sq)

/-- The inverse-image comparison for `g` on constant `B'`-sheaves. -/
def gPresheaf (sq : CommSq ρ α β φ) :
    (mapOp sq).op ⋙ (constRingedSite β B').structureSheaf.obj ⟶
      (constRingedSite α B').structureSheaf.obj :=
  𝟙 _

/-- Every functor of chaotic sites is cocontinuous; in particular `u` is cocontinuous. -/
instance mapOp_isCocontinuous (sq : CommSq ρ α β φ) :
    (mapOp sq).IsCocontinuous
      (constRingedSite α B').siteTopology (constRingedSite β B').siteTopology :=
  Functor.isCocontinuous_bot (mapOp sq)

/-- The morphism `g : (Sh(C), underline{B'}) ⟶ (Sh(C'), underline{B'})` induced by `u`. -/
def g (sq : CommSq ρ α β φ) :
    ToposHom (constRingedSite α B') (constRingedSite β B') :=
  Cocontinuous.toRingedTopos (mapOp sq) (gPresheaf sq)

/-- The identity morphism of the ringed point with coefficients `B'`. -/
def rightLower (sq : CommSq ρ α β φ) : ToposHom (point B') (point B') :=
  ToposHom.id (point B')

/-- Two adjacent commutative squares of ringed topoi on polynomial sites and ringed points. -/
structure Diagram where
  /-- The left square, comparing `h` with `f`. -/
  left : CommSquare
    (constRingedSite β B') (constRingedSite β B) (point B') (point B)
  /-- The right square, comparing `g` with the identity on `(Sh(*), B')`. -/
  right : CommSquare
    (constRingedSite α B') (constRingedSite β B') (point B') (point B')

variable (sq : CommSq ρ α β φ)

/-- The left-hand commutative square of ringed topoi, comparing `h` with `f`. -/
def leftSquare : CommSquare
    (constRingedSite β B') (constRingedSite β B) (point B') (point B) where
  upper := h sq
  left := toPoint β B'
  right := toPoint β B
  lower := f sq
  cell :=
    { homIso := Iso.refl _
      comm := sorry }

/-- Comparison of the two functors `C_{B/A} ⥤ *` used in the right-hand square. -/
def starIso : starFunctor α ≅ mapOp sq ⋙ starFunctor β :=
  Functor.punitExt _ _

/-- The invertible `2`-cell of the right-hand square, comparing `g ≫ π'` with `π ≫ id`. -/
def rightCellIso :
    ((g sq).comp (toPoint β B')).toTopos.pushforward ≅
      ((toPoint α B').comp (rightLower sq)).toTopos.pushforward :=
  Functor.sheafPushforwardCocontinuousComp
      (⊥ : GrothendieckTopology (polynomialSite α))
      (⊥ : GrothendieckTopology (polynomialSite β)) (⊥ : GrothendieckTopology pointSite)
      (mapOp sq) (starFunctor β) ≪≫
    Functor.sheafPushforwardCocontinuousIso
      (⊥ : GrothendieckTopology (polynomialSite α)) (⊥ : GrothendieckTopology pointSite)
      (mapOp sq ⋙ starFunctor β) (starIso sq).symm ≪≫
    (Functor.rightUnitor
      ((starFunctor α).sheafPushforwardCocontinuous (Type (u + 1))
        (⊥ : GrothendieckTopology (polynomialSite α))
        (⊥ : GrothendieckTopology pointSite))).symm

/-- The right-hand commutative square of ringed topoi, comparing `g` with the identity on the
point. -/
def rightSquare : CommSquare
    (constRingedSite α B') (constRingedSite β B') (point B') (point B') where
  upper := g sq
  left := toPoint α B'
  right := toPoint β B'
  lower := rightLower sq
  cell :=
    { homIso := rightCellIso sq
      comm := sorry }

/-- The double square of ringed topoi induced by a commutative square of rings. -/
def ofCommSq :=
  Diagram.mk (leftSquare sq) (rightSquare sq)

/-- The upper edge of the left square is `h`. -/
theorem left_upper_eq_h : (ofCommSq sq).left.upper = h sq := sorry

/-- The upper edge of the right square is `g`. -/
theorem right_upper_eq_g : (ofCommSq sq).right.upper = g sq := sorry

/-- The lower edge of the right square is the identity on `(Sh(*), B')`. -/
theorem right_lower_id : (ofCommSq sq).right.lower = rightLower sq := sorry

/-- The two adjacent squares have the prescribed coefficient-change, base-change,
projection, and identity edges. -/
theorem ofCommSq_spec :
    (ofCommSq sq).left.upper = h sq ∧
    (ofCommSq sq).left.lower = f sq ∧
    (ofCommSq sq).left.left = toPoint β B' ∧
    (ofCommSq sq).left.right = toPoint β B ∧
    (ofCommSq sq).right.upper = g sq ∧
    (ofCommSq sq).right.lower = rightLower sq ∧
    (ofCommSq sq).right.left = toPoint α B' ∧
    (ofCommSq sq).right.right = toPoint β B' := sorry

end RingedSite.Cotangent.Functoriality
