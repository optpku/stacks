module

public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.CategoryTheory.Monoidal.Cartesian.CommGrp_
public import ReasLib.AlgebraicGeometry.RootsOfUnity.Scheme

/-!
# The roots-of-unity group scheme

This module represents the group-valued roots-of-unity functor by an affine commutative group
scheme, identifies its multiplication on coordinate rings, and constructs arbitrary base changes.
-/

@[expose] public section

noncomputable section

open CategoryTheory Opposite
open CategoryTheory.Limits
open scoped AlgebraicGeometry CategoryTheory.MonObj TensorProduct

universe u

namespace AlgebraicGeometry.RootsOfUnity

/-- The commutative group of `n`th roots of unity in the global sections of an object over `S`. -/
def functorOfPointsObj (S : Scheme.{u}) (n : ℕ) [NeZero n]
    (T : (Over S)ᵒᵖ) : CommGrpCat.{u} :=
  CommGrpCat.of (rootsOfUnity n Γ((unop T).left, ⊤))

/-- Pullback of global sections induces the map on groups of roots of unity. -/
def functorOfPointsMap (S : Scheme.{u}) (n : ℕ) [NeZero n]
    {T T' : (Over S)ᵒᵖ} (f : T ⟶ T') :
    functorOfPointsObj S n T ⟶ functorOfPointsObj S n T' :=
  CommGrpCat.ofHom
    (restrictRootsOfUnity (Scheme.Γ.map f.unop.left.op).hom n)

/-- Pullback of roots of unity preserves identity morphisms. -/
theorem functorOfPointsMap_id (S : Scheme.{u}) (n : ℕ) [NeZero n]
    (T : (Over S)ᵒᵖ) :
    functorOfPointsMap S n (𝟙 T) = 𝟙 (functorOfPointsObj S n T) := sorry

/-- Pullback of roots of unity preserves composition. -/
theorem functorOfPointsMap_comp (S : Scheme.{u}) (n : ℕ) [NeZero n]
    {T T' T'' : (Over S)ᵒᵖ} (f : T ⟶ T') (g : T' ⟶ T'') :
    functorOfPointsMap S n (f ≫ g) =
      functorOfPointsMap S n f ≫ functorOfPointsMap S n g := sorry

/-- The commutative-group-valued functor of `n`th roots of unity over a scheme. -/
def functorOfPoints (S : Scheme.{u}) (n : ℕ) [NeZero n] :
    (Over S)ᵒᵖ ⥤ CommGrpCat.{u} where
  obj := functorOfPointsObj S n
  map := functorOfPointsMap S n
  map_id := functorOfPointsMap_id S n
  map_comp := functorOfPointsMap_comp S n

/-- The roots-of-unity functor acts by restriction along pullback of global sections. -/
theorem functorOfPoints_map_apply (S : Scheme.{u}) (n : ℕ) [NeZero n]
    {T T' : (Over S)ᵒᵖ} (f : T ⟶ T')
    (ζ : rootsOfUnity n Γ((unop T).left, ⊤)) :
    (functorOfPoints S n).map f ζ =
      restrictRootsOfUnity (Scheme.Γ.map f.unop.left.op).hom n ζ := sorry

/-- Naturality of affine point classification for roots of unity over `Spec(ULift ℤ)`. -/
theorem functorOfPoints_homEquiv_comp (n : ℕ) [NeZero n]
    {T T' : Over (Spec (CommRingCat.of (ULift.{u} ℤ)))} (f : T ⟶ T')
    (g : T' ⟶ overInt.{u} n) :
    HomOver.equiv n T (f ≫ g) =
      (functorOfPoints (Spec (CommRingCat.of (ULift.{u} ℤ))) n ⋙
        forget CommGrpCat).map f.op (HomOver.equiv n T' g) := sorry

/-- The integral roots-of-unity functor is represented by its affine quotient scheme. -/
def functorOfPointsRepresentableBy (n : ℕ) [NeZero n] :
    (functorOfPoints (Spec (CommRingCat.of (ULift.{u} ℤ))) n ⋙
      forget CommGrpCat).RepresentableBy (overInt.{u} n) where
  homEquiv := HomOver.equiv n _
  homEquiv_comp := functorOfPoints_homEquiv_comp n

/-- The representing equivalence is distinguished-coordinate evaluation. -/
theorem functorOfPointsRepresentableBy_homEquiv (n : ℕ) [NeZero n]
    (T : Over (Spec (CommRingCat.of (ULift.{u} ℤ)))) :
    (functorOfPointsRepresentableBy.{u} n).homEquiv = HomOver.equiv n T := sorry

/-- The canonical commutative-group-object structure induced by representability. -/
noncomputable instance instCommGrpObjOverInt (n : ℕ) [NeZero n] :
    CommGrpObj (overInt.{u} n) :=
  CommGrpObj.ofRepresentableBy (overInt.{u} n)
    (functorOfPoints (Spec (CommRingCat.of (ULift.{u} ℤ))) n)
    (functorOfPointsRepresentableBy.{u} n)

/-- The commutative group scheme of `n`th roots of unity over `Spec(ULift ℤ)`. -/
def groupScheme (n : ℕ) [NeZero n] :
    CommGrp (Over (Spec (CommRingCat.of (ULift.{u} ℤ)))) :=
  { X := overInt.{u} n }

notation3:max "μₙ " n:arg => AlgebraicGeometry.RootsOfUnity.groupScheme n
notation3:max "μ₃" => AlgebraicGeometry.RootsOfUnity.groupScheme 3

/-- The underlying object of the integral roots-of-unity group scheme is `overInt n`. -/
theorem groupScheme_X (n : ℕ) [NeZero n] : (μₙ n : CommGrp _).X = overInt.{u} n := sorry

/-- The underlying scheme of the integral roots-of-unity group scheme is the quotient spectrum. -/
theorem groupScheme_left (n : ℕ) [NeZero n] :
    (μₙ n : CommGrp (Over (Spec (CommRingCat.of (ULift.{u} ℤ))))).X.left =
      Spec (CommRingCat.of (coordinateRing.{u} n)) := sorry

namespace HomOver

/-- Distinguished-coordinate evaluation respects multiplication of affine points. -/
theorem root_mul (n : ℕ) [NeZero n]
    (T : Over (Spec (CommRingCat.of (ULift.{u} ℤ))))
    (f g : T ⟶ overInt.{u} n) : root n T (f * g) = root n T f * root n T g := sorry

/-- Affine points of the roots-of-unity scheme are multiplicatively equivalent to roots of unity. -/
def mulEquiv (n : ℕ) [NeZero n]
    (T : Over (Spec (CommRingCat.of (ULift.{u} ℤ)))) :
    (T ⟶ overInt.{u} n) ≃* rootsOfUnity n Γ(T.left, ⊤) where
  toEquiv := equiv n T
  map_mul' := root_mul n T

/-- The forward map of `mulEquiv` is distinguished-coordinate evaluation. -/
theorem mulEquiv_apply (n : ℕ) [NeZero n]
    (T : Over (Spec (CommRingCat.of (ULift.{u} ℤ))))
    (f : T ⟶ overInt.{u} n) : mulEquiv n T f = root n T f := sorry

/-- The multiplicative affine point equivalence is natural under precomposition. -/
theorem mulEquiv_naturality (n : ℕ) [NeZero n]
    {T T' : Over (Spec (CommRingCat.of (ULift.{u} ℤ)))} (g : T' ⟶ T)
    (f : T ⟶ overInt.{u} n) :
    mulEquiv n T' (g ≫ f) =
      restrictRootsOfUnity (Scheme.Γ.map g.left.op).hom n (mulEquiv n T f) :=
  equiv_naturality n g f

end HomOver

/-- Categorical multiplication is dual to the comultiplication sending `X` to `X ⊗ₜ X`. -/
theorem mul_eq_specMap_comul (n : ℕ) [NeZero n] :
    μ[overInt.{u} n].left =
      (pullbackSpecIso (ULift.{u} ℤ) (coordinateRing.{u} n) (coordinateRing.{u} n)).hom ≫
        Spec.map (CommRingCat.ofHom (CoordinateRing.comul.{u} n)) := sorry

/-- Base change of the integral roots-of-unity group scheme to a scheme `S`. -/
def baseChange (n : ℕ) [NeZero n] (S : Scheme.{u}) : CommGrp (Over S) :=
  (Over.pullback (specULiftZIsTerminal.from S)).mapCommGrp.obj (groupScheme.{u} n)

notation3:arg "μₙ " n:arg " over " S:arg =>
  AlgebraicGeometry.RootsOfUnity.baseChange n S
notation3:arg "μ₃" " over " S:arg =>
  AlgebraicGeometry.RootsOfUnity.baseChange 3 S

/-- The underlying object after base change is the canonical pullback of `overInt n`. -/
theorem baseChange_X (n : ℕ) [NeZero n] (S : Scheme.{u}) :
    (μₙ n over S).X =
      (Over.pullback (specULiftZIsTerminal.from S)).obj (μₙ n : CommGrp _).X := sorry

namespace BaseChange

/-- The pullback adjunction identifies base-changed points with integral points. -/
def pullbackHomEquiv (n : ℕ) [NeZero n] (S : Scheme.{u}) (T : Over S) :
    (T ⟶ (μₙ n over S).X) ≃
      ((Over.map (specULiftZIsTerminal.from S)).obj T ⟶ (μₙ n : CommGrp _).X) :=
  (Over.mapPullbackAdj (specULiftZIsTerminal.from S)).homEquiv
    T (μₙ n : CommGrp _).X |>.symm

/-- The pullback-adjunction equivalence preserves multiplication of points. -/
theorem pullbackHomEquiv_map_mul (n : ℕ) [NeZero n] (S : Scheme.{u}) (T : Over S)
    (f g : T ⟶ (μₙ n over S).X) :
    pullbackHomEquiv n S T (f * g) =
      pullbackHomEquiv n S T f * pullbackHomEquiv n S T g := sorry

/-- The multiplicative point equivalence supplied by the pullback adjunction. -/
def pullbackHomMulEquiv (n : ℕ) [NeZero n] (S : Scheme.{u}) (T : Over S) :
    (T ⟶ (μₙ n over S).X) ≃*
      ((Over.map (specULiftZIsTerminal.from S)).obj T ⟶ (μₙ n : CommGrp _).X) where
  toEquiv := pullbackHomEquiv n S T
  map_mul' := pullbackHomEquiv_map_mul n S T

/-- Points of the base-changed group scheme are roots of unity in global sections. -/
def homMulEquiv (n : ℕ) [NeZero n] (S : Scheme.{u}) (T : Over S) :
    (T ⟶ (μₙ n over S).X) ≃* rootsOfUnity n Γ(T.left, ⊤) :=
  (pullbackHomMulEquiv n S T).trans
    (HomOver.mulEquiv n ((Over.map (specULiftZIsTerminal.from S)).obj T))

/-- The base-changed point equivalence first projects to the integral model. -/
theorem homMulEquiv_apply (n : ℕ) [NeZero n] (S : Scheme.{u}) (T : Over S)
    (f : T ⟶ (μₙ n over S).X) :
    homMulEquiv n S T f =
      HomOver.mulEquiv n ((Over.map (specULiftZIsTerminal.from S)).obj T)
        (pullbackHomEquiv n S T f) := sorry

/-- The base-changed point equivalence is natural under precomposition over the base. -/
theorem homMulEquiv_naturality (n : ℕ) [NeZero n] (S : Scheme.{u})
    {T T' : Over S} (g : T' ⟶ T) (f : T ⟶ (μₙ n over S).X) :
    homMulEquiv n S T' (g ≫ f) =
      restrictRootsOfUnity (Scheme.Γ.map g.left.op).hom n (homMulEquiv n S T f) := sorry

/-- The roots-of-unity functor over `S` is represented by the base-changed affine scheme. -/
def representableBy (n : ℕ) [NeZero n] (S : Scheme.{u}) :
    (functorOfPoints S n ⋙ forget CommGrpCat).RepresentableBy (μₙ n over S).X where
  homEquiv := (homMulEquiv n S _).toEquiv
  homEquiv_comp := by
    intro T T' f g
    change homMulEquiv n S T (f ≫ g) =
      restrictRootsOfUnity (Scheme.Γ.map f.left.op).hom n (homMulEquiv n S T' g)
    exact homMulEquiv_naturality n S f g

/-- The representing equivalence after base change is the multiplicative point equivalence. -/
theorem representableBy_homEquiv (n : ℕ) [NeZero n] (S : Scheme.{u}) (T : Over S) :
    (representableBy n S).homEquiv = (homMulEquiv n S T).toEquiv := sorry

end BaseChange
end AlgebraicGeometry.RootsOfUnity
