module

public import Mathlib.Algebra.MvPolynomial.Equiv
public import Mathlib.Algebra.Category.Grp.EquivalenceGroupAddGroup
public import ReasLib.AlgebraicGeometry.AffineSpace.AdditiveGroup

/-!
# The additive group scheme

This module constructs the additive affine line as a commutative group scheme, identifies its
integral polynomial model, and describes its relative functor of points by global sections.
-/

@[expose] public noncomputable section

open CategoryTheory Opposite
open CategoryTheory.Limits CategoryTheory.MonoidalCategory
  CategoryTheory.CartesianMonoidalCategory
open scoped AlgebraicGeometry CategoryTheory.MonObj

namespace AlgebraicGeometry.AdditiveGroup

universe u

/-- The additive group scheme over `S`, with underlying scheme the affine line over `S`. -/
def groupScheme (S : Scheme.{u}) : CommGrp (Over S) :=
  { X := Scheme.asOver (𝔸(PUnit.{u + 1}; S)) S }

/-- Notation for the additive group scheme over a base scheme. -/
scoped[AlgebraicGeometry] notation3:max "𝔾ₐ[" S "]" =>
  AlgebraicGeometry.AdditiveGroup.groupScheme S

/-- Formation of the additive group scheme commutes with change of base. -/
def baseChangeIso {S T : Scheme.{u}} (f : S ⟶ T) :
    groupScheme S ≅ (Over.pullback f).mapCommGrp.obj (groupScheme T) :=
  AffineSpace.baseChangeCommGroupIso PUnit f

/-- The integral additive group scheme is the spectrum of the polynomial ring `ℤ[X]`. -/
def integralModelIso :
    (groupScheme (Spec (.of ℤ))).X.left ≅ Spec (.of (Polynomial ℤ)) :=
  AffineSpace.SpecIso PUnit (.of ℤ) ≪≫
    Scheme.Spec.mapIso
      (MvPolynomial.uniqueAlgEquiv ℤ PUnit).toRingEquiv.toCommRingCatIso.symm.op

/-- The integral-model isomorphism identifies `Polynomial.X` with the affine-line coordinate. -/
theorem integralModelIso_hom_appTop_coord :
    integralModelIso.hom.appTop
        ((Scheme.ΓSpecIso (.of (Polynomial ℤ))).inv Polynomial.X) =
      AffineSpace.coord (Spec (.of ℤ)) default := sorry

/-- A point of the additive group scheme determines its value at the affine coordinate. -/
def homToSection (S : Scheme.{u}) (T : Over S) (f : T ⟶ (groupScheme S).X) :
    Multiplicative Γ(T.left, ⊤) :=
  Multiplicative.ofAdd (f.left.appTop (AffineSpace.coord S default))

/-- The affine-space map determined by a section is compatible with the structure maps. -/
theorem homOfSection_w (S : Scheme.{u}) (T : Over S)
    (x : Multiplicative Γ(T.left, ⊤)) :
    AffineSpace.homOfVector T.hom (fun _ ↦ Multiplicative.toAdd x) ≫
        (groupScheme S).X.hom =
      T.hom := sorry

/-- A global section determines a point of the additive group scheme. -/
def homOfSection (S : Scheme.{u}) (T : Over S)
    (x : Multiplicative Γ(T.left, ⊤)) : T ⟶ (groupScheme S).X :=
  Over.homMk (AffineSpace.homOfVector T.hom (fun _ ↦ Multiplicative.toAdd x))
    (homOfSection_w S T x)

/-- Constructing a point from the coordinate of a point recovers the original point. -/
theorem homOfSection_homToSection (S : Scheme.{u}) (T : Over S)
    (f : T ⟶ (groupScheme S).X) :
    homOfSection S T (homToSection S T f) = f := sorry

/-- Evaluating the point associated to a section recovers that section. -/
theorem homToSection_homOfSection (S : Scheme.{u}) (T : Over S)
    (x : Multiplicative Γ(T.left, ⊤)) :
    homToSection S T (homOfSection S T x) = x := sorry

/-- Evaluation at the affine coordinate sends pointwise multiplication to addition of sections. -/
theorem homToSection_mul (S : Scheme.{u}) (T : Over S)
    (f g : T ⟶ (groupScheme S).X) :
    homToSection S T (f * g) = homToSection S T f * homToSection S T g := sorry

/-- Points of the additive group scheme are multiplicatively equivalent to additive global
sections. -/
def homMulEquiv (S : Scheme.{u}) (T : Over S) :
    (T ⟶ (groupScheme S).X) ≃* Multiplicative Γ(T.left, ⊤) where
  toFun := homToSection S T
  invFun := homOfSection S T
  left_inv := homOfSection_homToSection S T
  right_inv := homToSection_homOfSection S T
  map_mul' := homToSection_mul S T

/-- The points equivalence evaluates a morphism at the standard affine coordinate. -/
theorem homMulEquiv_apply (S : Scheme.{u}) (T : Over S)
    (f : T ⟶ (groupScheme S).X) :
    homMulEquiv S T f =
      Multiplicative.ofAdd (f.left.appTop (AffineSpace.coord S default)) := sorry

/-- The group-valued functor of additive global sections over a base scheme. -/
def points (S : Scheme.{u}) : (Over S)ᵒᵖ ⥤ GrpCat.{u} :=
  (Over.forget S).op ⋙ Scheme.Γ ⋙ forget₂ CommRingCat RingCat ⋙
    forget₂ RingCat AddCommGrpCat ⋙ AddCommGrpCat.toCommGrp ⋙
      forget₂ CommGrpCat GrpCat

/-- The objectwise group isomorphism from points of the additive group scheme to global
sections. -/
def componentIso (S : Scheme.{u}) (T : (Over S)ᵒᵖ) :
    (CategoryTheory.yonedaGrp.obj (groupScheme S).toGrp).obj T ≅ (points S).obj T :=
  MulEquiv.toGrpIso (homMulEquiv S T.unop)

/-- The pointwise global-sections isomorphisms are natural in the test scheme. -/
theorem componentIso_naturality (S : Scheme.{u}) {T T' : (Over S)ᵒᵖ}
    (f : T ⟶ T') :
    (CategoryTheory.yonedaGrp.obj (groupScheme S).toGrp).map f ≫
        (componentIso S T').hom =
      (componentIso S T).hom ≫ (points S).map f := sorry

/-- The additive group scheme represents the group-valued functor of global sections. -/
def representingIso (S : Scheme.{u}) :
    CategoryTheory.yonedaGrp.obj (groupScheme S).toGrp ≅ points S :=
  NatIso.ofComponents (componentIso S) (fun f ↦ componentIso_naturality S f)

/-- A component of the representing isomorphism is evaluation at the affine coordinate. -/
theorem representingIso_hom_app (S : Scheme.{u}) (T : Over S)
    (f : T ⟶ (groupScheme S).X) :
    (representingIso S).hom.app (op T) f = homMulEquiv S T f := sorry

end AlgebraicGeometry.AdditiveGroup
