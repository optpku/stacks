module

public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.Algebra.Category.Grp.Adjunctions
public import Mathlib.CategoryTheory.Monoidal.Cartesian.CommGrp_
public import Mathlib.RingTheory.HopfAlgebra.MonoidAlgebra
public import ReasLib.AlgebraicGeometry.Scheme.OverSpec

/-!
# The multiplicative group scheme

This module constructs the integral multiplicative group scheme from the Laurent-polynomial
Hopf algebra, its canonical base changes, and its units-valued functor of points.
-/

@[expose] public section

open CategoryTheory Opposite
open CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory
open scoped AlgebraicGeometry MonObj TensorProduct

noncomputable section

universe u

namespace AlgebraicGeometry.MultiplicativeGroup

/-- The multiplicative group scheme over `Spec (ULift ℤ)`, with coordinate ring
`LaurentPolynomial (ULift ℤ)`. -/
def overInt : Over (Spec (CommRingCat.of (ULift.{u} ℤ))) :=
  Over.mk (Spec.map (CommRingCat.ofHom LaurentPolynomial.C))

/-- The underlying scheme of `overInt` is the spectrum of the Laurent-polynomial ring. -/
theorem overInt_left :
    overInt.left = Spec (CommRingCat.of (LaurentPolynomial (ULift.{u} ℤ))) := sorry

/-- The structure morphism of `overInt` is induced by the constant-polynomial map. -/
theorem overInt_hom : overInt.hom = Spec.map (CommRingCat.ofHom LaurentPolynomial.C) := sorry

/-- The underlying scheme map of the unit of the integral multiplicative group. -/
def oneLeft :
    (𝟙_ (Over (Spec (CommRingCat.of (ULift.{u} ℤ))))).left ⟶ overInt.left :=
  Spec.map (CommRingCat.ofHom
    (Bialgebra.counitAlgHom (ULift.{u} ℤ) (LaurentPolynomial (ULift.{u} ℤ))).toRingHom)

/-- The unit map is compatible with the structure maps to `Spec (ULift ℤ)`. -/
theorem oneLeft_w : oneLeft ≫ overInt.hom =
    (𝟙_ (Over (Spec (CommRingCat.of (ULift.{u} ℤ))))).hom := sorry

/-- The unit morphism of the integral multiplicative group scheme. -/
def one : 𝟙_ (Over (Spec (CommRingCat.of (ULift.{u} ℤ)))) ⟶ overInt :=
  Over.homMk oneLeft oneLeft_w

/-- The underlying scheme map of multiplication, induced by Laurent comultiplication. -/
def mulLeft : (overInt ⊗ overInt).left ⟶ overInt.left :=
  (pullbackSpecIso (ULift.{u} ℤ)
      (LaurentPolynomial (ULift.{u} ℤ)) (LaurentPolynomial (ULift.{u} ℤ))).hom ≫
    Spec.map (CommRingCat.ofHom
      (Bialgebra.comulAlgHom (ULift.{u} ℤ) (LaurentPolynomial (ULift.{u} ℤ))).toRingHom)

/-- The multiplication map is compatible with the structure maps to `Spec (ULift ℤ)`. -/
theorem mulLeft_w : mulLeft ≫ overInt.hom = (overInt ⊗ overInt).hom := sorry

/-- Multiplication on the integral multiplicative group scheme. -/
def mul : overInt ⊗ overInt ⟶ overInt := Over.homMk mulLeft mulLeft_w

/-- The underlying scheme map of inversion, induced by `T n ↦ T (-n)`. -/
def invLeft : overInt.left ⟶ overInt.left :=
  Spec.map (CommRingCat.ofHom
    ((LaurentPolynomial.invert :
        LaurentPolynomial (ULift.{u} ℤ) ≃ₐ[ULift.{u} ℤ]
          LaurentPolynomial (ULift.{u} ℤ)).toAlgHom.toRingHom))

/-- The inversion map is compatible with the structure map to `Spec (ULift ℤ)`. -/
theorem invLeft_w : invLeft ≫ overInt.hom = overInt.hom := sorry

/-- Inversion on the integral multiplicative group scheme. -/
def inv : overInt ⟶ overInt := Over.homMk invLeft invLeft_w

/-- The left unit law for the integral multiplicative group scheme. -/
theorem one_mul : one ▷ overInt ≫ mul = (λ_ overInt).hom := sorry

/-- The right unit law for the integral multiplicative group scheme. -/
theorem mul_one : overInt ◁ one ≫ mul = (ρ_ overInt).hom := sorry

/-- Associativity of multiplication on the integral multiplicative group scheme. -/
theorem mul_assoc :
    (mul ▷ overInt) ≫ mul = (α_ overInt overInt overInt).hom ≫ (overInt ◁ mul) ≫ mul := sorry

/-- The left inverse law for the integral multiplicative group scheme. -/
theorem left_inv : lift inv (𝟙 overInt) ≫ mul = toUnit _ ≫ one := sorry

/-- The right inverse law for the integral multiplicative group scheme. -/
theorem right_inv : lift (𝟙 overInt) inv ≫ mul = toUnit _ ≫ one := sorry

/-- Multiplication on the integral multiplicative group scheme is commutative. -/
theorem mul_comm : (β_ overInt overInt).hom ≫ mul = mul := sorry

/-- On coordinate rings, multiplication sends `T 1` to `T 1 ⊗ₜ T 1`. -/
theorem mul_coordinate :
    Bialgebra.comulAlgHom (ULift.{u} ℤ) (LaurentPolynomial (ULift.{u} ℤ))
        (LaurentPolynomial.T 1) =
      LaurentPolynomial.T 1 ⊗ₜ[ULift.{u} ℤ] LaurentPolynomial.T 1 := sorry

/-- The universal Laurent coordinate multiplied by its inverse is one. -/
theorem coordinateUnit_val_inv :
    (LaurentPolynomial.T 1 : LaurentPolynomial (ULift.{u} ℤ)) *
      LaurentPolynomial.T (-1) = 1 := sorry

/-- The inverse of the universal Laurent coordinate multiplied by it is one. -/
theorem coordinateUnit_inv_val :
    (LaurentPolynomial.T (-1) : LaurentPolynomial (ULift.{u} ℤ)) *
      LaurentPolynomial.T 1 = 1 := sorry

/-- The universal Laurent coordinate and its explicit inverse. -/
def coordinateUnit : (LaurentPolynomial (ULift.{u} ℤ))ˣ where
  val := LaurentPolynomial.T 1
  inv := LaurentPolynomial.T (-1)
  val_inv := coordinateUnit_val_inv
  inv_val := coordinateUnit_inv_val

/-- The value of the universal Laurent coordinate is `T 1`. -/
theorem coordinateUnit_val : (coordinateUnit : LaurentPolynomial (ULift.{u} ℤ)) =
    LaurentPolynomial.T 1 := sorry

/-- A Laurent-polynomial ring map determines the image of the universal unit. -/
def ringHomToUnit (A : CommRingCat.{u})
    (f : CommRingCat.of (LaurentPolynomial (ULift.{u} ℤ)) ⟶ A) : Aˣ :=
  Units.map f.hom coordinateUnit

/-- The underlying value of `ringHomToUnit A f` is `f (T 1)`. -/
theorem ringHomToUnit_val (A : CommRingCat.{u})
    (f : CommRingCat.of (LaurentPolynomial (ULift.{u} ℤ)) ⟶ A) :
    (ringHomToUnit A f : A) = f (LaurentPolynomial.T 1) := sorry

/-- A unit determines the Laurent-polynomial evaluation homomorphism over `ULift ℤ`. -/
def ringHomOfUnit (A : CommRingCat.{u}) (x : Aˣ) :
    CommRingCat.of (LaurentPolynomial (ULift.{u} ℤ)) ⟶ A :=
  CommRingCat.ofHom (LaurentPolynomial.eval₂
    ((Int.castRingHom A).comp ULift.ringEquiv.toRingHom) x)

/-- The map `ringHomOfUnit A x` sends `T 1` to the value of `x`. -/
theorem ringHomOfUnit_T (A : CommRingCat.{u}) (x : Aˣ) :
    ringHomOfUnit A x (LaurentPolynomial.T 1) = x := sorry

/-- Laurent evaluation is left inverse to extracting the universal unit. -/
theorem ringHomOfUnit_ringHomToUnit (A : CommRingCat.{u})
    (f : CommRingCat.of (LaurentPolynomial (ULift.{u} ℤ)) ⟶ A) :
    ringHomOfUnit A (ringHomToUnit A f) = f := sorry

/-- Extracting `T 1` is left inverse to Laurent evaluation at a unit. -/
theorem ringHomToUnit_ringHomOfUnit (A : CommRingCat.{u}) (x : Aˣ) :
    ringHomToUnit A (ringHomOfUnit A x) = x := sorry

/-- Ring maps from the integral Laurent-polynomial ring are equivalent to units. -/
def ringHomEquivUnits (A : CommRingCat.{u}) :
    (CommRingCat.of (LaurentPolynomial (ULift.{u} ℤ)) ⟶ A) ≃ Aˣ where
  toFun := ringHomToUnit A
  invFun := ringHomOfUnit A
  left_inv := ringHomOfUnit_ringHomToUnit A
  right_inv := ringHomToUnit_ringHomOfUnit A

/-- The forward map of `ringHomEquivUnits` extracts the universal Laurent coordinate. -/
theorem ringHomEquivUnits_apply (A : CommRingCat.{u})
    (f : CommRingCat.of (LaurentPolynomial (ULift.{u} ℤ)) ⟶ A) :
    ringHomEquivUnits A f = ringHomToUnit A f := sorry

/-- The contravariant functor of units in global sections. -/
def unitsFunctor : Scheme.{u}ᵒᵖ ⥤ CommGrpCat.{u} :=
  Scheme.Γ ⋙ forget₂ CommRingCat CommMonCat ⋙ CommMonCat.units

/-- The value of `unitsFunctor` at a scheme is the group of units in its global sections. -/
theorem unitsFunctor_obj (T : Scheme.{u}ᵒᵖ) :
    unitsFunctor.obj T = CommGrpCat.of Γ(unop T, ⊤)ˣ := sorry

/-- Morphisms to the multiplicative group scheme are equivalent to global units. -/
def homEquiv (T : Scheme.{u}) :
    (T ⟶ overInt.left) ≃ Γ(T, ⊤)ˣ :=
  (Scheme.homToSpecGlobalSectionsEquiv T
    (CommRingCat.of (LaurentPolynomial (ULift.{u} ℤ)))).trans
      (ringHomEquivUnits (Scheme.Γ.obj (op T)))

/-- The representing equivalence evaluates the pulled-back Laurent coordinate `T 1`. -/
theorem homEquiv_apply (T : Scheme.{u}) (f : T ⟶ overInt.left) :
    homEquiv T f = ringHomToUnit (Scheme.Γ.obj (op T))
      (Scheme.homToSpecGlobalSectionsEquiv T
        (CommRingCat.of (LaurentPolynomial (ULift.{u} ℤ))) f) := sorry

/-- The relative functor of units over `S`. -/
def relativeUnitsFunctor (S : Scheme.{u}) : (Over S)ᵒᵖ ⥤ CommGrpCat.{u} :=
  (Over.forget S).op ⋙ unitsFunctor

/-- The group-valued functor of points of the multiplicative group scheme over `S`. -/
def points (S : Scheme.{u}) : (Over S)ᵒᵖ ⥤ GrpCat.{u} :=
  relativeUnitsFunctor S ⋙ forget₂ CommGrpCat GrpCat

/-- The relative units functor evaluates to units in the global sections of the source scheme. -/
theorem relativeUnitsFunctor_obj (S : Scheme.{u}) (U : (Over S)ᵒᵖ) :
    (relativeUnitsFunctor S).obj U =
      CommGrpCat.of Γ((unop U).left, ⊤)ˣ := sorry

/-- The group-valued points functor evaluates to units in the global sections of the source
scheme. -/
theorem points_obj (S : Scheme.{u}) (U : (Over S)ᵒᵖ) :
    (points S).obj U = GrpCat.of Γ((unop U).left, ⊤)ˣ := sorry

/-- Morphisms over `Spec (ULift ℤ)` into `overInt` are equivalent to morphisms of their
underlying schemes. -/
def homOverEquivLeftOverInt (T : Over (Spec (CommRingCat.of (ULift.{u} ℤ)))) :
    (T ⟶ overInt) ≃ (T.left ⟶ overInt.left) where
  toFun f := f.left
  invFun f :=
    Over.homMk f (by
      exact specULiftZIsTerminal.hom_ext (f ≫ overInt.hom) T.hom)
  left_inv := by
    intro f
    cases f
    rfl
  right_inv := by
    intro f
    rfl

/-- Morphisms over `Spec (ULift ℤ)` into `overInt` are equivalent to units in the global
sections of the source scheme. -/
def homOverEquivOverInt (T : Over (Spec (CommRingCat.of (ULift.{u} ℤ)))) :
    (T ⟶ overInt) ≃ Γ(T.left, ⊤)ˣ :=
  (homOverEquivLeftOverInt T).trans (homEquiv T.left)

/-- The forward map of `homOverEquivLeftOverInt` forgets the morphism compatibility proof. -/
theorem homOverEquivLeftOverInt_apply
    (T : Over (Spec (CommRingCat.of (ULift.{u} ℤ)))) (f : T ⟶ overInt) :
    homOverEquivLeftOverInt T f = f.left := sorry

/-- The absolute points equivalence is natural under precomposition over `Spec (ULift ℤ)`. -/
theorem homOverEquivOverInt_comp
    {T T' : Over (Spec (CommRingCat.of (ULift.{u} ℤ)))} (f : T ⟶ T')
    (g : T' ⟶ overInt) :
    homOverEquivOverInt T (f ≫ g) =
      (points (Spec (CommRingCat.of (ULift.{u} ℤ))) ⋙ forget GrpCat).map f.op
        (homOverEquivOverInt T' g) := sorry

/-- The multiplicative group scheme over `Spec (ULift ℤ)` represents the underlying set-valued
functor of global units. -/
def representedBy :
    (points (Spec (CommRingCat.of (ULift.{u} ℤ))) ⋙ forget GrpCat).RepresentableBy overInt where
  homEquiv := homOverEquivOverInt _
  homEquiv_comp := homOverEquivOverInt_comp

/-- The integral units functor is representable by `overInt` already at the commutative-group
level. -/
def representedByComm :
    (relativeUnitsFunctor (Spec (CommRingCat.of (ULift.{u} ℤ))) ⋙
      forget CommGrpCat).RepresentableBy overInt where
  homEquiv := homOverEquivOverInt _
  homEquiv_comp := homOverEquivOverInt_comp

/-- The representing equivalence supplied by `representedBy` is the canonical equivalence with
morphisms into `overInt`. -/
theorem representedBy_homEquiv (T : Over (Spec (CommRingCat.of (ULift.{u} ℤ)))) :
    representedBy.homEquiv = homOverEquivOverInt T := sorry

/-- The canonical commutative-group structure on the integral multiplicative group scheme. -/
noncomputable instance instCommGrpObjOverInt : CategoryTheory.CommGrpObj overInt :=
  CategoryTheory.CommGrpObj.ofRepresentableBy overInt
    (relativeUnitsFunctor (Spec (CommRingCat.of (ULift.{u} ℤ)))) representedByComm

/-- The multiplicative group scheme over `Spec (ULift ℤ)`. -/
def groupScheme : CommGrp (Over (Spec (CommRingCat.of (ULift.{u} ℤ)))) :=
  { X := overInt }

/-- The underlying group object of the multiplicative group scheme over `Spec (ULift ℤ)`. -/
def group : Grp (Over (Spec (CommRingCat.of (ULift.{u} ℤ)))) :=
  groupScheme.toGrp

notation3:max "𝔾ₘ" =>
  AlgebraicGeometry.MultiplicativeGroup.groupScheme

/-- The underlying object of `𝔾ₘ` is `overInt`. -/
theorem groupScheme_X : (𝔾ₘ).X = overInt := sorry

/-- The underlying object of `group` is `overInt`. -/
theorem group_X : group.X = overInt := sorry

/-- The explicit Hopf-algebra unit map is the canonical unit of `overInt`. -/
theorem one_eq_eta : one = η[overInt] := sorry

/-- The explicit Hopf-algebra multiplication is the canonical multiplication of `overInt`. -/
theorem mul_eq_mu : mul = μ[overInt] := sorry

/-- The explicit Hopf-algebra inversion is the canonical inversion of `overInt`. -/
theorem inv_eq_iota : inv = ι[overInt] := sorry

/-- Morphisms over `Spec (ULift ℤ)` to `𝔾ₘ` are equivalent to scheme maps to its underlying
integral model. -/
def homOverEquivLeft (T : Over (Spec (CommRingCat.of (ULift.{u} ℤ)))) :
    (T ⟶ (𝔾ₘ).X) ≃ (T.left ⟶ overInt.left) := by
  simpa [groupScheme] using homOverEquivLeftOverInt T

/-- Absolute points of the multiplicative group scheme are global units. -/
def homOverEquiv (T : Over (Spec (CommRingCat.of (ULift.{u} ℤ)))) :
    (T ⟶ (𝔾ₘ).X) ≃ Γ(T.left, ⊤)ˣ := by
  simpa [groupScheme] using homOverEquivOverInt T

/-- The forward map of `homOverEquivLeft` forgets the over-structure. -/
theorem homOverEquivLeft_apply (T : Over (Spec (CommRingCat.of (ULift.{u} ℤ))))
    (f : T ⟶ (𝔾ₘ).X) :
    homOverEquivLeft T f = f.left := sorry

/-- The absolute points equivalence is natural under precomposition over `Spec (ULift ℤ)`. -/
theorem homOverEquiv_comp
    {T T' : Over (Spec (CommRingCat.of (ULift.{u} ℤ)))} (f : T ⟶ T')
    (g : T' ⟶ (𝔾ₘ).X) :
    homOverEquiv T (f ≫ g) =
      (points (Spec (CommRingCat.of (ULift.{u} ℤ))) ⋙ forget GrpCat).map f.op
        (homOverEquiv T' g) := sorry

/-- The integral multiplicative group scheme represents global units as a group-valued functor of
points. -/
noncomputable def representingIso :
    CategoryTheory.yonedaGrp.obj (𝔾ₘ).toGrp ≅
      points (Spec (CommRingCat.of (ULift.{u} ℤ))) :=
  CategoryTheory.yonedaGrpObjIsoOfRepresentableBy overInt
    (points (Spec (CommRingCat.of (ULift.{u} ℤ)))) representedBy

/-- The forward component of `representingIso` is the absolute points equivalence. -/
theorem representingIso_hom_app (T : Over (Spec (CommRingCat.of (ULift.{u} ℤ))))
    (f : T ⟶ (𝔾ₘ).X) :
    representingIso.hom.app (op T) f = homOverEquiv T f := sorry

/-- Absolute points of `𝔾ₘ` carry the multiplicative equivalence induced by `representingIso`. -/
def homOverMulEquiv (T : Over (Spec (CommRingCat.of (ULift.{u} ℤ)))) :
    (T ⟶ (𝔾ₘ).X) ≃* Γ(T.left, ⊤)ˣ :=
  Iso.groupIsoToMulEquiv (representingIso.app (op T))

/-- The forward map of `homOverMulEquiv` is the units-valued absolute points equivalence. -/
theorem homOverMulEquiv_apply (T : Over (Spec (CommRingCat.of (ULift.{u} ℤ))))
    (f : T ⟶ (𝔾ₘ).X) :
    homOverMulEquiv T f = homOverEquiv T f := sorry

/-- The multiplicative group scheme over `S`, obtained by base change from `Spec (ULift ℤ)`. -/
def baseChange (S : Scheme.{u}) : CommGrp (Over S) :=
  (Over.pullback (specULiftZIsTerminal.from S)).mapCommGrp.obj 𝔾ₘ

notation3:max "𝔾ₘ[" S "]" =>
  AlgebraicGeometry.MultiplicativeGroup.baseChange S

/-- The underlying object of `baseChange S` is the canonical pullback of `overInt`. -/
theorem baseChange_X (S : Scheme.{u}) :
    (𝔾ₘ[S]).X = (Over.pullback (specULiftZIsTerminal.from S)).obj overInt := sorry

/-- The underlying scheme of `(𝔾ₘ[S]).X` is the defining fiber product. -/
theorem baseChange_left (S : Scheme.{u}) :
    (𝔾ₘ[S]).X.left = pullback overInt.hom (specULiftZIsTerminal.from S) := sorry

/-- The structure map of `(𝔾ₘ[S]).X` is the second pullback projection. -/
theorem baseChange_hom (S : Scheme.{u}) :
    (𝔾ₘ[S]).X.hom = pullback.snd overInt.hom (specULiftZIsTerminal.from S) := sorry

/-- The pullback adjunction identifies relative points with absolute points of `𝔾ₘ`. -/
def baseChangeHomEquivAbsolute (S : Scheme.{u}) (T : Over S) :
    (T ⟶ (𝔾ₘ[S]).X) ≃
      ((Over.map (specULiftZIsTerminal.from S)).obj T ⟶ (𝔾ₘ).X) := by
  simpa [baseChange, groupScheme] using
    ((Over.mapPullbackAdj (specULiftZIsTerminal.from S)).homEquiv T overInt).symm

/-- The forward map of `baseChangeHomEquivAbsolute` is the pullback-adjunction comparison. -/
theorem baseChangeHomEquivAbsolute_apply (S : Scheme.{u}) (T : Over S)
    (f : T ⟶ (𝔾ₘ[S]).X) :
    baseChangeHomEquivAbsolute S T f =
      ((Over.mapPullbackAdj (specULiftZIsTerminal.from S)).homEquiv T (𝔾ₘ).X).symm f := sorry

/-- Relative points of the base-changed multiplicative group are global units. -/
def baseChangeHomEquiv (S : Scheme.{u}) (T : Over S) :
    (T ⟶ (𝔾ₘ[S]).X) ≃ Γ(T.left, ⊤)ˣ :=
  (baseChangeHomEquivAbsolute S T).trans
    (homOverEquiv ((Over.map (specULiftZIsTerminal.from S)).obj T))

/-- The relative points equivalence is natural under precomposition over `S`. -/
theorem baseChangeHomEquiv_comp (S : Scheme.{u}) {T T' : Over S} (f : T ⟶ T')
    (g : T' ⟶ (baseChange S).X) :
    baseChangeHomEquiv S T (f ≫ g) =
      (points S ⋙ forget GrpCat).map f.op (baseChangeHomEquiv S T' g) := sorry

/-- The base-changed multiplicative group scheme represents the underlying set-valued functor of
relative global units. -/
def baseChangeRepresentedBy (S : Scheme.{u}) :
    (points S ⋙ forget GrpCat).RepresentableBy (𝔾ₘ[S]).X where
  homEquiv := baseChangeHomEquiv S _
  homEquiv_comp := baseChangeHomEquiv_comp S

/-- The relative units functor over `S` is representable by the pullback of `overInt`. -/
def baseChangeRepresentedByComm (S : Scheme.{u}) :
    (relativeUnitsFunctor S ⋙ forget CommGrpCat).RepresentableBy (𝔾ₘ[S]).X where
  homEquiv := baseChangeHomEquiv S _
  homEquiv_comp := baseChangeHomEquiv_comp S

/-- Relative points of `𝔾ₘ` carry the multiplicative equivalence induced by
`baseChangeHomEquiv`. -/
noncomputable def baseChangeHomMulEquiv (S : Scheme.{u}) (T : Over S) :
    (T ⟶ (𝔾ₘ[S]).X) ≃* Γ(T.left, ⊤)ˣ where
  toEquiv := baseChangeHomEquiv S T
  map_mul' := by
    sorry

/-- The forward map of `baseChangeHomMulEquiv` is `baseChangeHomEquiv`. -/
theorem baseChangeHomMulEquiv_apply (S : Scheme.{u}) (T : Over S)
    (f : T ⟶ (𝔾ₘ[S]).X) :
    baseChangeHomMulEquiv S T f = baseChangeHomEquiv S T f := sorry

/-- The objectwise group isomorphism between relative points and relative global units. -/
noncomputable def baseChangeComponentIso (S : Scheme.{u}) (T : (Over S)ᵒᵖ) :
    (CategoryTheory.yonedaGrp.obj (𝔾ₘ[S]).toGrp).obj T ≅ (points S).obj T :=
  MulEquiv.toGrpIso (baseChangeHomMulEquiv S T.unop)

/-- Naturality of the relative point description of the base-changed multiplicative group. -/
theorem baseChangeComponentIso_naturality (S : Scheme.{u}) {T T' : (Over S)ᵒᵖ}
    (f : T ⟶ T') :
    (CategoryTheory.yonedaGrp.obj (baseChange S).toGrp).map f ≫
        (baseChangeComponentIso S T').hom =
      (baseChangeComponentIso S T).hom ≫ (points S).map f := sorry

/-- The base-changed multiplicative group scheme represents relative global units as a
group-valued functor of points. -/
noncomputable def baseChangeRepresentingIso (S : Scheme.{u}) :
    CategoryTheory.yonedaGrp.obj (𝔾ₘ[S]).toGrp ≅ points S :=
  NatIso.ofComponents (baseChangeComponentIso S)
    (fun f ↦ baseChangeComponentIso_naturality S f)

/-- The forward component of the relative representing isomorphism is `baseChangeHomEquiv`. -/
theorem baseChangeRepresentingIso_hom_app (S : Scheme.{u}) (T : Over S)
    (f : T ⟶ (𝔾ₘ[S]).X) :
    (baseChangeRepresentingIso S).hom.app (op T) f = baseChangeHomEquiv S T f := sorry

end AlgebraicGeometry.MultiplicativeGroup
