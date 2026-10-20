/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.EllipticCurve.VariableChange
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Grp
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import ReasLib.AlgebraicGeometry.EllipticCurve.WeierstrassFamily
public import ReasLib.AlgebraicGeometry.GeneralLinear.Scheme
public import ReasLib.AlgebraicGeometry.Scheme.OverSpec
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.FunctorOfPoints
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Points
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Product
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Action

/-!
# Admissible changes of Weierstrass variables

The smooth affine group scheme `H = Spec(ℤ[u, u⁻¹, r, s, t])` represents admissible
changes of variables. Its faithful matrix realization and its action on the canonical
Weierstrass scheme `W = Spec(ℤ[a₁, a₂, a₃, a₄, a₆, 1/Δ])` are constructed explicitly.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme Limits Opposite
open CartesianMonoidalCategory MonoidalCategory
open scoped AlgebraicGeometry CategoryTheory.MonObj MonoidalLeftAction

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicStack.WeierstrassQuotient

/-- The unique morphism from a scheme over `Spec ℤ` to the identity object. -/
private def toTerminal (T : Over EllipticCurve.Moduli.specInt) : T ⟶ Over.mk (𝟙 EllipticCurve.Moduli.specInt) :=
  Over.homMk T.hom (Category.comp_id T.hom)

/-- The underlying scheme map of `toTerminal T` is the structure morphism of `T`. -/
private theorem toTerminal_left (T : Over EllipticCurve.Moduli.specInt) : (toTerminal T).left = T.hom :=
  rfl

/-- The terminal algebraic space `Spec ℤ` over itself. -/
def terminalSpace : AlgebraicSpace EllipticCurve.Moduli.specInt :=
  AlgebraicSpace.ofOver (Over.mk (𝟙 EllipticCurve.Moduli.specInt))

/-- `terminalSpace` is `ofOver` of the identity over `Spec ℤ`. -/
theorem terminalSpace_eq : terminalSpace = AlgebraicSpace.ofOver (Over.mk (𝟙 EllipticCurve.Moduli.specInt)) :=
  rfl

/-- The Weierstrass scheme as an algebraic space over the terminal algebraic space. -/
def schemeAsOver : Over terminalSpace :=
  Over.mk (AlgebraicSpace.ofOverMap
    (Over.homMk WeierstrassScheme.overInt.hom
      (Category.comp_id WeierstrassScheme.overInt.hom)))

/-- The underlying algebraic space of `schemeAsOver` is `ofOver` of the Weierstrass scheme. -/
theorem schemeAsOver_left : schemeAsOver.left = AlgebraicSpace.ofOver WeierstrassScheme.overInt :=
  rfl

/-- Parameters `(u, r, s, t)` of an admissible change of variables. -/
inductive GroupParam : Type
  /-- The unit coefficient `u`. -/
  | u
  /-- The translation coefficient `r`. -/
  | r
  /-- The shear coefficient `s`. -/
  | s
  /-- The translation coefficient `t`. -/
  | t
  deriving DecidableEq

/-- The polynomial ring `ℤ[u, r, s, t]` in universe `u`. -/
abbrev groupPolynomial : Type u :=
  MvPolynomial (ULift.{u} GroupParam) (ULift.{u} ℤ)

/-- The coordinate function `u`. -/
def groupUnit : groupPolynomial :=
  MvPolynomial.X ⟨.u⟩

/-- `groupUnit` is the variable `u`. -/
theorem groupUnit_eq : groupUnit = MvPolynomial.X ⟨.u⟩ :=
  rfl

/-- The coordinate ring of `H`, obtained by inverting `u`. -/
abbrev groupRing : Type u :=
  Localization.Away groupUnit

/-- The structure morphism of `H` on coordinate rings. -/
def groupToBase : CommRingCat.of (ULift.{u} ℤ) ⟶ CommRingCat.of groupRing :=
  CommRingCat.ofHom ((algebraMap groupPolynomial groupRing).comp MvPolynomial.C)

/-- The group scheme `H` of admissible changes of variables, as an object over `Spec ℤ`. -/
def groupScheme : Over EllipticCurve.Moduli.specInt :=
  OverSpec.affine groupToBase

/-- The underlying scheme of `groupScheme` is `Spec(ℤ[u, u⁻¹, r, s, t])`. -/
theorem groupScheme_left : groupScheme.left = Spec (CommRingCat.of groupRing) :=
  rfl

/-- The admissible-change group scheme is smooth over the integral base. -/
theorem groupScheme_smooth : Smooth groupScheme.hom :=
  sorry

/-- Polynomial evaluation of `(u, r, s, t)` at an admissible change of variables. -/
def polynomialEval {A : Type u} [CommRing A] (φ : ULift.{u} ℤ →+* A)
    (C : WeierstrassCurve.VariableChange A) : groupPolynomial →+* A :=
  MvPolynomial.eval₂Hom φ fun i ↦
    match i.down with
    | .u => (C.u : A)
    | .r => C.r
    | .s => C.s
    | .t => C.t

/-- Evaluation of `u` at an admissible change of variables is a unit. -/
theorem polynomialEval_unit {A : Type u} [CommRing A] (φ : ULift.{u} ℤ →+* A)
    (C : WeierstrassCurve.VariableChange A) : IsUnit (polynomialEval φ C groupUnit) :=
  sorry

/-- The coordinate-ring map classified by an admissible change of variables. -/
def homOfVariableChange {A : Type u} [CommRing A] (φ : ULift.{u} ℤ →+* A)
    (C : WeierstrassCurve.VariableChange A) : groupRing →+* A :=
  IsLocalization.Away.lift groupUnit (polynomialEval_unit φ C)

/-- The unit `u` recovered from a coordinate-ring homomorphism out of `groupRing`. -/
def unitOfHom {A : Type u} [CommRing A] (ψ : groupRing →+* A) : Aˣ :=
  ((IsLocalization.Away.algebraMap_isUnit groupUnit).map ψ).unit

/-- The admissible change of variables classified by a coordinate-ring homomorphism. -/
def variableChangeOfHom {A : Type u} [CommRing A] (ψ : groupRing →+* A) :
    WeierstrassCurve.VariableChange A where
  u := unitOfHom ψ
  r := ψ (algebraMap groupPolynomial groupRing (MvPolynomial.X ⟨.r⟩))
  s := ψ (algebraMap groupPolynomial groupRing (MvPolynomial.X ⟨.s⟩))
  t := ψ (algebraMap groupPolynomial groupRing (MvPolynomial.X ⟨.t⟩))

/-- Compatibility of `homOfVariableChange` with the structure maps from `ULift ℤ`. -/
private theorem compatibleOfVariableChange_w (T : Over EllipticCurve.Moduli.specInt)
    (C : WeierstrassCurve.VariableChange Γ(T.left, ⊤)) :
    groupToBase ≫ CommRingCat.ofHom (homOfVariableChange (OverSpec.baseRingHom T).hom C) =
      OverSpec.baseRingHom T :=
  sorry

/-- The base-compatible coordinate-ring homomorphism classified by an admissible change of
variables. -/
def compatibleOfVariableChange (T : Over EllipticCurve.Moduli.specInt)
    (C : WeierstrassCurve.VariableChange Γ(T.left, ⊤)) :
    OverSpec.CompatibleRingHom groupToBase T :=
  Under.homMk (CommRingCat.ofHom (homOfVariableChange (OverSpec.baseRingHom T).hom C))
    (by exact compatibleOfVariableChange_w T C)

/-- The admissible change of variables recovered from a compatible coordinate-ring homomorphism. -/
def variableChangeOfCompatible {T : Over EllipticCurve.Moduli.specInt} (ψ : OverSpec.CompatibleRingHom groupToBase T) :
    WeierstrassCurve.VariableChange Γ(T.left, ⊤) :=
  variableChangeOfHom ψ.right.hom

/-- Reconstructing a compatible coordinate-ring homomorphism from its change of variables is the
identity. -/
theorem compatibleOfVariableChange_variableChangeOfCompatible (T : Over EllipticCurve.Moduli.specInt)
    (ψ : OverSpec.CompatibleRingHom groupToBase T) :
    compatibleOfVariableChange T (variableChangeOfCompatible ψ) = ψ :=
  sorry

/-- Evaluating the compatible coordinate-ring homomorphism classified by a change of variables
recovers that change of variables. -/
theorem variableChangeOfCompatible_compatibleOfVariableChange (T : Over EllipticCurve.Moduli.specInt)
    (C : WeierstrassCurve.VariableChange Γ(T.left, ⊤)) :
    variableChangeOfCompatible (compatibleOfVariableChange T C) = C :=
  sorry

/-- Compatible coordinate-ring homomorphisms into `H` are admissible changes of variables. -/
def variableChangeCompatibleEquiv (T : Over EllipticCurve.Moduli.specInt) :
    OverSpec.CompatibleRingHom groupToBase T ≃
      WeierstrassCurve.VariableChange Γ(T.left, ⊤) where
  toFun := variableChangeOfCompatible
  invFun := compatibleOfVariableChange T
  left_inv := compatibleOfVariableChange_variableChangeOfCompatible T
  right_inv := variableChangeOfCompatible_compatibleOfVariableChange T

/-- Morphisms over `Spec ℤ` into `H` are admissible changes of variables on global sections. -/
def homOverEquiv (T : Over EllipticCurve.Moduli.specInt) :
    (T ⟶ groupScheme) ≃ WeierstrassCurve.VariableChange Γ(T.left, ⊤) :=
  (OverSpec.homEquiv groupToBase T).trans (variableChangeCompatibleEquiv T)

/-- The admissible change of variables classified by a morphism into `H`. -/
def variableChangeOfOver {T : Over EllipticCurve.Moduli.specInt} (f : T ⟶ groupScheme) :
    WeierstrassCurve.VariableChange Γ(T.left, ⊤) :=
  homOverEquiv T f

/-- The morphism into `H` classified by an admissible change of variables. -/
def overOfVariableChange {T : Over EllipticCurve.Moduli.specInt} (C : WeierstrassCurve.VariableChange Γ(T.left, ⊤)) :
    T ⟶ groupScheme :=
  (homOverEquiv T).symm C

/-- The group of admissible changes of variables over the global sections of an object over
`Spec ℤ`. -/
def variableChangeFunctorObj (T : (Over EllipticCurve.Moduli.specInt)ᵒᵖ) : GrpCat.{u} :=
  GrpCat.of (WeierstrassCurve.VariableChange Γ((unop T).left, ⊤))

/-- The point-group map induced by pullback of global sections. -/
def variableChangeFunctorMap {T T' : (Over EllipticCurve.Moduli.specInt)ᵒᵖ} (f : T ⟶ T') :
    variableChangeFunctorObj T ⟶ variableChangeFunctorObj T' :=
  GrpCat.ofHom (WeierstrassCurve.VariableChange.mapHom (Scheme.Hom.appTop f.unop.left).hom)

/-- Pullback of admissible changes of variables preserves identity morphisms. -/
theorem variableChangeFunctorMap_id (T : (Over EllipticCurve.Moduli.specInt)ᵒᵖ) :
    variableChangeFunctorMap (𝟙 T) = 𝟙 (variableChangeFunctorObj T) :=
  sorry

/-- Pullback of admissible changes of variables preserves composition. -/
theorem variableChangeFunctorMap_comp {T T' T'' : (Over EllipticCurve.Moduli.specInt)ᵒᵖ} (f : T ⟶ T') (g : T' ⟶ T'') :
    variableChangeFunctorMap (f ≫ g) =
      variableChangeFunctorMap f ≫ variableChangeFunctorMap g :=
  sorry

/-- The group-valued functor of admissible changes of variables. -/
def variableChangeFunctor : (Over EllipticCurve.Moduli.specInt)ᵒᵖ ⥤ GrpCat.{u} where
  obj := variableChangeFunctorObj
  map := variableChangeFunctorMap
  map_id := variableChangeFunctorMap_id
  map_comp := variableChangeFunctorMap_comp

/-- Naturality of `homOverEquiv` under precomposition. -/
theorem homOverEquiv_comp {T T' : Over EllipticCurve.Moduli.specInt} (f : T ⟶ T') (g : T' ⟶ groupScheme) :
    homOverEquiv T (f ≫ g) =
      (variableChangeFunctor ⋙ forget GrpCat).map f.op (homOverEquiv T' g) :=
  sorry

/-- The group scheme `H` represents the functor of admissible changes of variables. -/
def variableChangeRepresentableBy :
    (variableChangeFunctor ⋙ forget GrpCat).RepresentableBy groupScheme where
  homEquiv := homOverEquiv _
  homEquiv_comp := homOverEquiv_comp

/-- The canonical group-object structure on `H`, transported from `VariableChange`. -/
instance instGrpObj_groupScheme : GrpObj groupScheme :=
  GrpObj.ofRepresentableBy groupScheme variableChangeFunctor variableChangeRepresentableBy

/-- The row-coordinate matrix of an admissible change of variables `(u, r, s, t)`.
The shear entry is `u²s`: the unrestricted matrix shear coordinate equals `u²` times
mathlib's parameter `s`. Since `u` is a unit, this is an invertible reparameterization. -/
def toGLMatrixVal {A : Type u} [CommRing A] (C : WeierstrassCurve.VariableChange A) :
    Matrix (ULift.{u} (Fin 3)) (ULift.{u} (Fin 3)) A :=
  fun i j ↦
    match i.down.val, j.down.val with
    | 0, 0 => (C.u : A) ^ 2
    | 0, 1 => (C.u : A) ^ 2 * C.s
    | 0, 2 => 0
    | 1, 0 => 0
    | 1, 1 => (C.u : A) ^ 3
    | 1, 2 => 0
    | 2, 0 => C.r
    | 2, 1 => C.t
    | 2, 2 => 1
    | _, _ => 0

/-- The row-coordinate matrix of an admissible change of variables is invertible. -/
theorem toGLMatrix_isUnit {A : Type u} [CommRing A] (C : WeierstrassCurve.VariableChange A) :
    IsUnit (Matrix.det (toGLMatrixVal C)) :=
  sorry

/-- The row-coordinate matrix as an element of `GL₃`. -/
def toGLMatrix {A : Type u} [CommRing A] (C : WeierstrassCurve.VariableChange A) :
    Matrix.GeneralLinearGroup (ULift.{u} (Fin 3)) A :=
  Matrix.GeneralLinearGroup.mk'' (toGLMatrixVal C) (toGLMatrix_isUnit C)

/-- The matrix realization respects multiplication of admissible changes of variables. -/
theorem toGLMatrix_mul {A : Type u} [CommRing A]
    (C C' : WeierstrassCurve.VariableChange A) :
    toGLMatrix (C * C') = toGLMatrix C * toGLMatrix C' :=
  sorry

/-- The matrix realization distinguishes admissible changes of variables. -/
theorem toGLMatrix_injective {A : Type u} [CommRing A] :
    Function.Injective (toGLMatrix (A := A)) :=
  sorry

/-- The scheme-level matrix embedding `H ⟶ GL₃,ℤ` sending `(u, r, s, t)` to the row-coordinate matrix. -/
def toGLOver : groupScheme ⟶ GeneralLinear.schemeOver (ULift.{u} ℤ) (ULift.{u} (Fin 3)) :=
  GeneralLinear.HomOver.ofMatrix (ULift.{u} (Fin 3))
    (toGLMatrix (variableChangeOfOver (𝟙 groupScheme)))

/-- The row-coordinate matrix of `toGLOver` is the matrix attached to the universal change of variables. -/
theorem toGL_spec :
    GeneralLinear.HomOver.matrixOfHom (ULift.{u} (Fin 3)) toGLOver =
      toGLMatrix (variableChangeOfOver (𝟙 groupScheme)) :=
  sorry

/-- The matrix embedding `H ⟶ GL₃` as a morphism of algebraic spaces. -/
def toGL : AlgebraicSpace.ofOver groupScheme ⟶
    AlgebraicSpace.ofOver (GeneralLinear.schemeOver (ULift.{u} ℤ) (ULift.{u} (Fin 3))) :=
  AlgebraicSpace.ofOverMap toGLOver

/-- `toGL` is `ofOverMap` of the scheme-level matrix embedding. -/
theorem toGL_eq : toGL = AlgebraicSpace.ofOverMap toGLOver :=
  rfl

/-- Evaluation of Weierstrass coefficients at a Weierstrass curve. -/
def weierstrassEval {A : Type u} [CommRing A] (φ : ULift.{u} ℤ →+* A)
    (W : WeierstrassCurve A) : WeierstrassScheme.coeffRing →+* A :=
  MvPolynomial.eval₂Hom φ fun i ↦
    match i.down with
    | .a1 => W.a₁
    | .a2 => W.a₂
    | .a3 => W.a₃
    | .a4 => W.a₄
    | .a6 => W.a₆

/-- Evaluation of `Δ` at a Weierstrass curve with invertible discriminant is a unit. -/
theorem weierstrassEval_unit {A : Type u} [CommRing A] (φ : ULift.{u} ℤ →+* A)
    (W : WeierstrassCurve A) (hΔ : IsUnit W.Δ) :
    IsUnit (weierstrassEval φ W WeierstrassScheme.Δ) :=
  sorry

/-- The coordinate-ring map classified by a Weierstrass curve with invertible discriminant. -/
def homOfCurveRing {A : Type u} [CommRing A] (φ : ULift.{u} ℤ →+* A)
    (W : WeierstrassCurve A) (hΔ : IsUnit W.Δ) : WeierstrassScheme.ring →+* A :=
  IsLocalization.Away.lift WeierstrassScheme.Δ (weierstrassEval_unit φ W hΔ)

/-- Compatibility of the classified morphism into `W` with the structure morphisms to `Spec ℤ`. -/
private theorem homOfCurve_w {T : Over EllipticCurve.Moduli.specInt} (W : WeierstrassCurve Γ(T.left, ⊤)) (hΔ : IsUnit W.Δ) :
    (homToSpecGlobalSectionsEquiv T.left (CommRingCat.of WeierstrassScheme.ring)).symm
          (CommRingCat.ofHom (homOfCurveRing (OverSpec.baseRingHom T).hom W hΔ)) ≫
        WeierstrassScheme.overInt.hom =
      T.hom :=
  sorry

/-- The morphism into `W` classified by a Weierstrass curve with invertible discriminant. -/
def homOfCurve {T : Over EllipticCurve.Moduli.specInt} (W : WeierstrassCurve Γ(T.left, ⊤)) (hΔ : IsUnit W.Δ) :
    T ⟶ WeierstrassScheme.overInt :=
  Over.homMk
    ((homToSpecGlobalSectionsEquiv T.left (CommRingCat.of WeierstrassScheme.ring)).symm
      (CommRingCat.ofHom (homOfCurveRing (OverSpec.baseRingHom T).hom W hΔ)))
    (by exact homOfCurve_w W hΔ)

/-- The coordinate-ring map classified by a morphism into `W`. -/
def ringHomOfScheme {T : Over EllipticCurve.Moduli.specInt} (f : T ⟶ WeierstrassScheme.overInt) :
    WeierstrassScheme.ring →+* Γ(T.left, ⊤) :=
  (homToSpecGlobalSectionsEquiv T.left (CommRingCat.of WeierstrassScheme.ring) f.left).hom

/-- The Weierstrass curve classified by a morphism into `W`. -/
def curveOfHom {T : Over EllipticCurve.Moduli.specInt} (f : T ⟶ WeierstrassScheme.overInt) : WeierstrassCurve Γ(T.left, ⊤) where
  a₁ := ringHomOfScheme f
      (algebraMap WeierstrassScheme.coeffRing WeierstrassScheme.ring (MvPolynomial.X ⟨.a1⟩))
  a₂ := ringHomOfScheme f
      (algebraMap WeierstrassScheme.coeffRing WeierstrassScheme.ring (MvPolynomial.X ⟨.a2⟩))
  a₃ := ringHomOfScheme f
      (algebraMap WeierstrassScheme.coeffRing WeierstrassScheme.ring (MvPolynomial.X ⟨.a3⟩))
  a₄ := ringHomOfScheme f
      (algebraMap WeierstrassScheme.coeffRing WeierstrassScheme.ring (MvPolynomial.X ⟨.a4⟩))
  a₆ := ringHomOfScheme f
      (algebraMap WeierstrassScheme.coeffRing WeierstrassScheme.ring (MvPolynomial.X ⟨.a6⟩))

/-- A morphism into `W` classifies a Weierstrass curve with invertible discriminant. -/
theorem curveOfHom_isUnit {T : Over EllipticCurve.Moduli.specInt} (f : T ⟶ WeierstrassScheme.overInt) : IsUnit (curveOfHom f).Δ :=
  sorry

/-- The acted-on Weierstrass curve still has invertible discriminant. -/
theorem action_curve_isUnit {T : Over EllipticCurve.Moduli.specInt} (h : T ⟶ groupScheme) (w : T ⟶ WeierstrassScheme.overInt) :
    IsUnit ((variableChangeOfOver h • curveOfHom w).Δ) :=
  sorry

/-- The scheme-level action of an `H`-point on a `W`-point. -/
def actionHom {T : Over EllipticCurve.Moduli.specInt} (h : T ⟶ groupScheme) (w : T ⟶ WeierstrassScheme.overInt) : T ⟶ WeierstrassScheme.overInt :=
  homOfCurve (variableChangeOfOver h • curveOfHom w) (action_curve_isUnit h w)

/-- The scheme-level action morphism `H × W ⟶ W`. -/
def schemeAction : groupScheme ⊗ WeierstrassScheme.overInt ⟶ WeierstrassScheme.overInt :=
  actionHom (fst groupScheme WeierstrassScheme.overInt) (snd groupScheme WeierstrassScheme.overInt)

/-- `schemeAction` acts by `VariableChange` on classified Weierstrass curves. -/
theorem schemeAction_smul {T : Over EllipticCurve.Moduli.specInt} (h : T ⟶ groupScheme) (w : T ⟶ WeierstrassScheme.overInt) :
    lift h w ≫ schemeAction = actionHom h w :=
  sorry

/-- The algebraic space underlying `H`. -/
def groupOfScheme : AlgebraicSpace EllipticCurve.Moduli.specInt :=
  AlgebraicSpace.ofOver groupScheme

/-- `groupOfScheme` is `ofOver` of `groupScheme`. -/
theorem groupOfScheme_eq : groupOfScheme = AlgebraicSpace.ofOver groupScheme :=
  rfl

/-- The fibre product `Spec ℤ × H` as an algebraic space over `Spec ℤ`. -/
def groupSpaceObj : AlgebraicSpace EllipticCurve.Moduli.specInt :=
  AlgebraicSpace.product terminalSpace groupOfScheme

/-- The structure morphism of the group algebraic space `H`. -/
def groupHom : groupSpaceObj ⟶ terminalSpace :=
  AlgebraicSpace.productFst terminalSpace groupOfScheme

/-- `H` as an object of the slice over the terminal algebraic space. -/
def groupAsOver : Over terminalSpace :=
  Over.mk groupHom

/-- The underlying algebraic space of `groupAsOver` is `groupSpaceObj`. -/
theorem groupAsOver_left : groupAsOver.left = groupSpaceObj :=
  rfl

/-- Multiplication of `groupOfScheme`, transported from scheme-level multiplication on `H`. -/
def ofSchemeMul {E : AlgebraicSpace EllipticCurve.Moduli.specInt} (f g : E ⟶ groupOfScheme) : E ⟶ groupOfScheme where
  app T := ↾fun x ↦ lift (f.app T x) (g.app T x) ≫ μ[groupScheme]
  naturality := sorry

/-- The component of `ofSchemeMul f g` is postcomposition of the Cartesian pairing with
scheme-level multiplication. -/
theorem ofSchemeMul_app {E : AlgebraicSpace EllipticCurve.Moduli.specInt} (f g : E ⟶ groupOfScheme)
    (T : (Over EllipticCurve.Moduli.specInt)ᵒᵖ) (x : E.functorOfPoints.obj T) :
    (ofSchemeMul f g).app T x = lift (f.app T x) (g.app T x) ≫ μ[groupScheme] :=
  rfl

/-- The underlying algebraic-space map of the unit of `H`. -/
def oneHomLeft : (𝟙_ (Over terminalSpace)).left ⟶ groupAsOver.left :=
  AlgebraicSpace.productLift (𝟙 terminalSpace) (AlgebraicSpace.ofOverMap (η[groupScheme]))

/-- Compatibility of `oneHomLeft` with the structure morphisms over the terminal algebraic space. -/
private theorem oneHom_w : oneHomLeft ≫ groupHom = (𝟙_ (Over terminalSpace)).hom :=
  sorry

/-- The unit morphism of `H` over the terminal algebraic space. -/
def oneHom : 𝟙_ (Over terminalSpace) ⟶ groupAsOver :=
  Over.homMk oneHomLeft (by exact oneHom_w)

/-- The underlying algebraic-space map of multiplication of `H`. -/
def mulHomLeft : (groupAsOver ⊗ groupAsOver).left ⟶ groupAsOver.left :=
  AlgebraicSpace.productLift (groupAsOver ⊗ groupAsOver).hom
    (ofSchemeMul
      ((fst groupAsOver groupAsOver).left ≫
        AlgebraicSpace.productSnd terminalSpace groupOfScheme)
      ((snd groupAsOver groupAsOver).left ≫
        AlgebraicSpace.productSnd terminalSpace groupOfScheme))

/-- Compatibility of `mulHomLeft` with the structure morphisms over the terminal algebraic space. -/
private theorem mulHom_w : mulHomLeft ≫ groupHom = (groupAsOver ⊗ groupAsOver).hom :=
  sorry

/-- The multiplication morphism of `H` over the terminal algebraic space. -/
def mulHom : groupAsOver ⊗ groupAsOver ⟶ groupAsOver :=
  Over.homMk mulHomLeft (by exact mulHom_w)

/-- The underlying algebraic-space map of inversion of `H`. -/
def invHomLeft : groupAsOver.left ⟶ groupAsOver.left :=
  AlgebraicSpace.productLift groupHom
    (AlgebraicSpace.productSnd terminalSpace groupOfScheme ≫
      AlgebraicSpace.ofOverMap (ι[groupScheme]))

/-- Compatibility of `invHomLeft` with the structure morphisms over the terminal algebraic space. -/
private theorem invHom_w : invHomLeft ≫ groupHom = groupHom :=
  sorry

/-- The inverse morphism of `H` over the terminal algebraic space. -/
def invHom : groupAsOver ⟶ groupAsOver :=
  Over.homMk invHomLeft (by exact invHom_w)

/-- The canonical group-object structure on `groupAsOver`. -/
instance instGrpObj_groupAsOver : GrpObj groupAsOver where
  one := oneHom
  mul := mulHom
  inv := invHom
  one_mul := sorry
  mul_one := sorry
  mul_assoc := sorry
  left_inv := sorry
  right_inv := sorry

/-- The group algebraic space `H` of admissible changes of variables. -/
def group : GroupAlgebraicSpace terminalSpace :=
  ⟨groupAsOver⟩

/-- The underlying object of `group` is `groupAsOver`. -/
theorem group_X : group.X = groupAsOver :=
  rfl

/-- The `H`-factor of a point of `H × W`. -/
def actionPointGroup (T : (Over EllipticCurve.Moduli.specInt)ᵒᵖ)
    (x : ((group.X ⊗ schemeAsOver).left.functorOfPoints.obj T)) : T.unop ⟶ groupScheme :=
  (AlgebraicSpace.productSnd terminalSpace groupOfScheme).app T
    ((fst group.X schemeAsOver).left.app T x)

/-- The `W`-factor of a point of `H × W`. -/
def actionPointScheme (T : (Over EllipticCurve.Moduli.specInt)ᵒᵖ)
    (x : ((group.X ⊗ schemeAsOver).left.functorOfPoints.obj T)) : T.unop ⟶ WeierstrassScheme.overInt :=
  (snd group.X schemeAsOver).left.app T x

/-- The algebraic-space morphism `H × W → W` induced by the scheme-level action. -/
def actionSmulLeft : (group.X ⊗ schemeAsOver).left ⟶ AlgebraicSpace.ofOver WeierstrassScheme.overInt where
  app T := ↾fun x ↦ actionHom (actionPointGroup T x) (actionPointScheme T x)
  naturality := sorry

/-- Evaluating `actionSmulLeft` acts by the scheme-level action on paired points. -/
theorem actionSmulLeft_app (T : (Over EllipticCurve.Moduli.specInt)ᵒᵖ)
    (x : ((group.X ⊗ schemeAsOver).left.functorOfPoints.obj T)) :
    actionSmulLeft.app T x = actionHom (actionPointGroup T x) (actionPointScheme T x) :=
  rfl

/-- Compatibility of `actionSmulLeft` with the structure morphisms over the terminal algebraic
space. -/
private theorem actionSmul_w : actionSmulLeft ≫ schemeAsOver.hom = (group.X ⊗ schemeAsOver).hom :=
  sorry

/-- The action morphism in the slice over the terminal algebraic space. -/
def actionSmul : group.X ⊗ schemeAsOver ⟶ schemeAsOver :=
  Over.homMk actionSmulLeft (by exact actionSmul_w)

/-- The identity-action law for the algebraic-space action of `H` on `W`. -/
theorem actionSmul_one_smul :
    η[group.X] ⊵ₗ schemeAsOver ≫ actionSmul = (λₗ schemeAsOver).hom :=
  sorry

/-- The multiplication-action law for the algebraic-space action of `H` on `W`. -/
theorem actionSmul_mul_smul :
    μ[group.X] ⊵ₗ schemeAsOver ≫ actionSmul =
      (αₗ group.X group.X schemeAsOver).hom ≫ group.X ⊴ₗ actionSmul ≫ actionSmul :=
  sorry

/-- The module-object structure of the algebraic-space action of `H` on `W`. -/
@[reducible]
def actionModObj : ModObj group.X schemeAsOver where
  smul := actionSmul
  one_smul := actionSmul_one_smul
  mul_smul := actionSmul_mul_smul

/-- The action of `H` on the Weierstrass scheme `W`. -/
def action : GroupAlgebraicSpace.Action group where
  X := schemeAsOver
  mod := actionModObj

/-- The object underlying `action` is the Weierstrass scheme over the terminal algebraic space. -/
theorem action_X : action.X = schemeAsOver :=
  rfl

/-- The stored action morphism of `action` is `actionSmul`. -/
theorem action_smul : action.mod.smul = actionSmul :=
  rfl

/-- The underlying algebraic space of the action is `ofOver` of the Weierstrass scheme. -/
theorem action_left_eq : action.X.left = AlgebraicSpace.ofOver WeierstrassScheme.overInt :=
  rfl

end AlgebraicGeometry.AlgebraicStack.WeierstrassQuotient
