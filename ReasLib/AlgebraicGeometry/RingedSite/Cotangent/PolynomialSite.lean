/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Ring.ULift
public import Mathlib.CategoryTheory.CommSq
public import Mathlib.CategoryTheory.PUnit
public import Mathlib.CategoryTheory.Sites.Sheaf
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.RingTheory.TensorProduct.Maps
public import ReasLib.AlgebraicGeometry.RingedSite.Basic
public import ReasLib.AlgebraicGeometry.RingedSite.Topos.HomOfCocontinuous
public import ReasLib.CategoryTheory.Sites.Chaotic
public import Mathlib.Algebra.Category.CommAlgCat.Basic
public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
public import ReasLib.RingTheory.Algebra.TensorProduct.RightAlgebra

/-!
# Base change of the polynomial site `C_{B/A}`

Polynomial presentations form a full subcategory of the category of algebras over `B`.
A commutative square of rings induces the covariant functor sending a polynomial `A`-algebra map `P ⟶ B` to
`P ⊗[A] A' ⟶ B'`.
-/

@[expose] public section

open CategoryTheory Opposite
open Algebra.TensorProduct
open scoped TensorProduct Algebra.TensorProduct.Right

noncomputable section

universe u

namespace RingedSite.Cotangent

variable {A A' B B' : CommRingCat.{u}}

/-- The algebra structure on the codomain of a homomorphism of commutative rings. -/
@[reducible]
def algebraOfHom (f : A ⟶ B) : Algebra A B :=
  RingHom.toAlgebra f.hom

/-- The `A`-algebra structure on `B'` induced by the composite `α ≫ φ`. -/
@[reducible]
def algebraOfComp (α : A ⟶ B) (φ : B ⟶ B') : Algebra A B' :=
  RingHom.toAlgebra (φ.hom.comp α.hom)

/-- Unfolding `algebraOfComp` recovers the algebra of the composite ring homomorphism. -/
theorem algebraOfComp_eq (α : A ⟶ B) (φ : B ⟶ B') :
    algebraOfComp α φ = RingHom.toAlgebra (φ.hom.comp α.hom) :=
  sorry

/-- The full subcategory of algebra maps to `B` whose sources are polynomial over `A`. -/
abbrev PolynomialOver (A B : Type u) [CommRing A] [CommRing B] [Algebra A B] :=
  ObjectProperty.FullSubcategory (fun P : Over (CommAlgCat.of A B) ↦
    ∃ σ : Type u, Nonempty (P.left ≃ₐ[A] MvPolynomial σ A))

/-- The category of polynomial `A`-algebra maps to `B` for the algebra structure of `α`. -/
abbrev polynomialOver (α : A ⟶ B) :=
  @PolynomialOver A B _ _ (algebraOfHom α)

/-- The polynomial presentation category uses the algebra structure induced by `α`. -/
theorem polynomialOver_eq (α : A ⟶ B) :
    polynomialOver α = @PolynomialOver A B _ _ (algebraOfHom α) :=
  rfl

/-- The opposite polynomial presentation category attached to a ring map `α`. -/
abbrev polynomialSite (α : A ⟶ B) :=
  (polynomialOver α)ᵒᵖ

/-- The polynomial site is the opposite of the polynomial presentation category. -/
theorem polynomialSite_eq (α : A ⟶ B) :
    polynomialSite α = (polynomialOver α)ᵒᵖ :=
  rfl

/-- Universe lift of commutative rings, used as coefficients on the large site `C_{B/A}`. -/
def uliftCommRing : CommRingCat.{u} ⥤ CommRingCat.{u + 1} where
  obj R := CommRingCat.of (ULift.{u + 1} R)
  map f :=
    CommRingCat.ofHom
      (ULift.ringEquiv.symm.toRingHom.comp (f.hom.comp ULift.ringEquiv.toRingHom))

/-- The constant sheaf of a commutative ring on `C_{B/A}`. -/
def constSheaf (α : A ⟶ B) (R : CommRingCat.{u}) :
    Sheaf (⊥ : GrothendieckTopology (polynomialSite α)) CommRingCat.{u} :=
  ⟨(Functor.const _).obj R, Presheaf.isSheaf_bot _⟩

/-- Evaluation of the constant sheaf is constantly the given ring. -/
theorem constSheaf_obj (α : A ⟶ B) (R : CommRingCat.{u}) (X : (polynomialSite α)ᵒᵖ) :
    (constSheaf α R).obj.obj X = R :=
  rfl

/-- The morphism of constant sheaves induced by a ring map. -/
def constSheafMap (α : A ⟶ B) {R S : CommRingCat.{u}} (ψ : R ⟶ S) :
    constSheaf α R ⟶ constSheaf α S :=
  ObjectProperty.homMk ((Functor.const _).map ψ)

/-- The constant sheaf, lifted to `CommRingCat.{u + 1}`. -/
def constSheafLift (α : A ⟶ B) (R : CommRingCat.{u}) :
    Sheaf (⊥ : GrothendieckTopology (polynomialSite α)) CommRingCat.{u + 1} :=
  (sheafCompose (⊥ : GrothendieckTopology (polynomialSite α)) uliftCommRing).obj
    (constSheaf α R)

/-- The lifted constant-sheaf map induced by a ring map. -/
def constSheafMapLift (α : A ⟶ B) {R S : CommRingCat.{u}} (ψ : R ⟶ S) :
    constSheafLift α R ⟶ constSheafLift α S :=
  (sheafCompose (⊥ : GrothendieckTopology (polynomialSite α)) uliftCommRing).map
    (constSheafMap α ψ)

/-- The ringed site `(Sh(C_{B/A}), underline{R})`. -/
abbrev constRingedSite (α : A ⟶ B) (R : CommRingCat.{u}) : RingedSite :=
  ofCommRingSheaf (⊥ : GrothendieckTopology (polynomialSite α)) (constSheafLift α R)

/-- The constant ringed site is the commutative-ring-sheaf presentation of the lifted
constant sheaf. -/
theorem constRingedSite_eq (α : A ⟶ B) (R : CommRingCat.{u}) :
    constRingedSite α R =
      ofCommRingSheaf (⊥ : GrothendieckTopology (polynomialSite α)) (constSheafLift α R) :=
  rfl

/-- The point category `*` as `Discrete PUnit`. -/
abbrev pointSite : Type (u + 1) := Discrete PUnit.{u + 2}

/-- The constant sheaf of rings `R` on the point, with lifted coefficients. -/
def pointRingSheaf (R : CommRingCat.{u}) :
    Sheaf (⊥ : GrothendieckTopology pointSite) CommRingCat.{u + 1} :=
  ⟨(Functor.const _).obj (CommRingCat.of (ULift.{u + 1} R)), Presheaf.isSheaf_bot _⟩

/-- The ringed site `(Sh(*), R)`. -/
abbrev point (R : CommRingCat.{u}) : RingedSite :=
  ofCommRingSheaf (⊥ : GrothendieckTopology pointSite) (pointRingSheaf R)

/-- The point ringed site is the commutative-ring-sheaf presentation of the lifted constant
sheaf of `R`. -/
theorem point_eq (R : CommRingCat.{u}) :
    point R = ofCommRingSheaf (⊥ : GrothendieckTopology pointSite) (pointRingSheaf R) :=
  rfl

/-- The morphism of constant sheaves on the point induced by a ring map. -/
def pointRingSheafMap {R S : CommRingCat.{u}} (ψ : R ⟶ S) :
    pointRingSheaf R ⟶ pointRingSheaf S :=
  ObjectProperty.homMk ((Functor.const _).map (uliftCommRing.map ψ))

/-- The unique functor from `C_{B/A}` to the point. -/
abbrev starFunctor (α : A ⟶ B) : polynomialSite α ⥤ pointSite :=
  Functor.star.{u + 1, u, u + 1} (polynomialSite α)

/-- The category-to-point functor of the constant ringed site `(Sh(C_{B/A}), underline{R})`. -/
def toPointBase (α : A ⟶ B) (R : CommRingCat.{u}) :
    (constRingedSite α R).carrier ⥤ (point R).carrier :=
  starFunctor α

/-- Every functor of chaotic sites is cocontinuous; in particular the category-to-point
functor is cocontinuous. -/
instance toPointBase_isCocontinuous (α : A ⟶ B) (R : CommRingCat.{u}) :
    (toPointBase α R).IsCocontinuous
      (constRingedSite α R).siteTopology (point R).siteTopology :=
  Functor.isCocontinuous_bot (toPointBase α R)

/-- The constant-to-constant comparison identifying the pullback of `R` along `star`
with `underline{R}`. -/
def toPointStructureMap (α : A ⟶ B) (R : CommRingCat.{u}) :
    (toPointBase α R).op ⋙ (point R).structureSheaf.obj ⟶
      (constRingedSite α R).structureSheaf.obj :=
  𝟙 _

/-- The morphism of ringed topoi `π : (Sh(C_{B/A}), underline{R}) ⟶ (Sh(*), R)`. -/
def toPoint (α : A ⟶ B) (R : CommRingCat.{u}) :
    ToposHom (constRingedSite α R) (point R) :=
  Cocontinuous.toRingedTopos (toPointBase α R) (toPointStructureMap α R)

/-- The underlying functor of `π` is `Functor.star`. -/
theorem toPoint_star (α : A ⟶ B) (R : CommRingCat.{u}) :
    toPointBase α R = Functor.star.{u + 1, u, u + 1} (polynomialSite α) :=
  rfl

namespace Functoriality

/-- A right-factor-compatible comparison induces an algebra map from a base-changed
polynomial presentation to the target algebra. -/
def mapObjHomWith [Algebra A B] [Algebra A A'] [Algebra A' B'] [Algebra A B']
    (c : B ⊗[A] A' →ₐ[A] B')
    (hc : ∀ a' : A', c (1 ⊗ₜ[A] a') = algebraMap A' B' a')
    (P : PolynomialOver A B) : P.obj.left ⊗[A] A' →ₐ[A'] B' :=
  { toRingHom :=
      c.toRingHom.comp (Algebra.TensorProduct.map P.obj.hom.hom (AlgHom.id A A')).toRingHom
    commutes' := sorry }

/-- Tensor extension along `A ⟶ A'` carries a polynomial presentation to a polynomial
presentation over `A'`, using a right-factor-compatible comparison to `B'`. -/
def mapObjWith [Algebra A B] [Algebra A A'] [Algebra A' B'] [Algebra A B']
    (c : B ⊗[A] A' →ₐ[A] B')
    (hc : ∀ a' : A', c (1 ⊗ₜ[A] a') = algebraMap A' B' a')
    (P : PolynomialOver A B) : PolynomialOver A' B' :=
  { obj := Over.mk (CommAlgCat.ofHom (mapObjHomWith c hc P))
    property := sorry }

-- Local declaration justification (metaprogramming implementation): expose the private tensor-map body to its public morphism construction under Lean's module system.
set_option backward.privateInPublic true in
/-- Tensoring an algebra map with the identity on `A'` preserves the right-factor
`A'`-algebra structure. -/
private def tensorMapRight [Algebra A A'] {P Q : CommAlgCat.{u} A}
    (f : P →ₐ[A] Q) : P ⊗[A] A' →ₐ[A'] Q ⊗[A] A' :=
  { toRingHom := (Algebra.TensorProduct.map f (AlgHom.id A A')).toRingHom
    commutes' := sorry }

-- Local declaration justification (metaprogramming implementation): the public morphism construction uses the private tensor-map implementation without publishing a second map API.
set_option backward.privateInPublic true in
/-- Tensor extension of a morphism of polynomial presentations respects their common
right-factor-compatible comparison to `B'`. -/
def mapHomWith [Algebra A B] [Algebra A A'] [Algebra A' B'] [Algebra A B']
    (c : B ⊗[A] A' →ₐ[A] B')
    (hc : ∀ a' : A', c (1 ⊗ₜ[A] a') = algebraMap A' B' a')
    {P Q : PolynomialOver A B} (f : P ⟶ Q) :
    mapObjWith c hc P ⟶ mapObjWith c hc Q :=
  ObjectProperty.homMk
    (Over.homMk (CommAlgCat.ofHom (tensorMapRight f.hom.left.hom)) sorry)

variable {α : A ⟶ B} {ρ : A ⟶ A'} {β : A' ⟶ B'} {φ : B ⟶ B'}

/-- The right map of a commutative square is an algebra map for the composite target
algebra structure. -/
def rightAlgHom (sq : CommSq ρ α β φ) :
    @AlgHom A B B' _ _ _ (algebraOfHom α) (algebraOfComp α φ) :=
  @AlgHom.mk A B B' _ _ _ (algebraOfHom α) (algebraOfComp α φ) φ.hom sorry

/-- The bottom map of a commutative square is an algebra map from the left-induced algebra
to the composite target algebra. -/
def bottomAlgHom (sq : CommSq ρ α β φ) :
    @AlgHom A A' B' _ _ _ (algebraOfHom ρ) (algebraOfComp α φ) :=
  @AlgHom.mk A A' B' _ _ _ (algebraOfHom ρ) (algebraOfComp α φ) β.hom sorry

/-- The tensor comparison of a commutative square multiplies the images of its right
and bottom ring maps. -/
def tensorCompare (sq : CommSq ρ α β φ) :=
  @Algebra.TensorProduct.productMap A B' B A' _ _ _ _
    (algebraOfHom α) (algebraOfHom ρ) (algebraOfComp α φ)
    (rightAlgHom sq) (bottomAlgHom sq)

/-- The tensor comparison restricts on the right tensor factor to the bottom ring map. -/
theorem tensorCompare_includeRight (sq : CommSq ρ α β φ) (a' : A') :
    tensorCompare sq
        (@TensorProduct.tmul A _ B A' _ _
          (algebraOfHom α).toModule (algebraOfHom ρ).toModule 1 a') =
      @algebraMap A' B' _ _ (algebraOfHom β) a' := sorry

/-- The structure map of a base-changed polynomial presentation is the tensor comparison
composed with the tensor extension of its original structure map. -/
def mapObjHom (sq : CommSq ρ α β φ) (P : polynomialOver α) :=
  @mapObjHomWith A A' B B' (algebraOfHom α) (algebraOfHom ρ) (algebraOfHom β)
    (algebraOfComp α φ) (tensorCompare sq) (tensorCompare_includeRight sq) P

/-- A commutative square base-changes a polynomial presentation with carrier
`P.obj.left ⊗[A] A'` and the right-factor algebra structure. -/
def mapObj (sq : CommSq ρ α β φ) (P : polynomialOver α) : polynomialOver β :=
  @mapObjWith A A' B B' (algebraOfHom α) (algebraOfHom ρ) (algebraOfHom β)
    (algebraOfComp α φ) (tensorCompare sq) (tensorCompare_includeRight sq) P

/-- A commutative square acts on polynomial presentation morphisms by tensor extension. -/
def mapHom (sq : CommSq ρ α β φ) {P Q : polynomialOver α} (f : P ⟶ Q) :
    mapObj sq P ⟶ mapObj sq Q :=
  @mapHomWith A A' B B' (algebraOfHom α) (algebraOfHom ρ) (algebraOfHom β)
    (algebraOfComp α φ) (tensorCompare sq) (tensorCompare_includeRight sq) P Q f

-- Local declaration justification (metaprogramming implementation): make the private identity law accessible to the public functor's proof field under Lean's module system.
set_option backward.privateInPublic true in
/-- Base change of polynomial presentation morphisms preserves identities. -/
private theorem map_id (sq : CommSq ρ α β φ) (P : polynomialOver α) :
    mapHom sq (𝟙 P) = 𝟙 (mapObj sq P) := sorry

-- Local declaration justification (metaprogramming implementation): make the private composition law accessible to the public functor's proof field under Lean's module system.
set_option backward.privateInPublic true in
/-- Base change of polynomial presentation morphisms preserves composition. -/
private theorem map_comp (sq : CommSq ρ α β φ) {P Q R : polynomialOver α}
    (first : P ⟶ Q) (second : Q ⟶ R) :
    mapHom sq (first ≫ second) = mapHom sq first ≫ mapHom sq second := sorry

-- Local declaration justification (metaprogramming implementation): the public functor uses its two private law declarations without exporting proof-only API.
set_option backward.privateInPublic true in
/-- The functor of polynomial presentations induced by a commutative square sends each
presentation to its tensor extension with the canonical comparison to the target ring. -/
def map (sq : CommSq ρ α β φ) : polynomialOver α ⥤ polynomialOver β where
  obj := mapObj sq
  map f := mapHom sq f
  map_id := map_id sq
  map_comp first second := map_comp sq first second

/-- The object function of polynomial base change is the tensor presentation construction. -/
theorem map_obj (sq : CommSq ρ α β φ) (P : polynomialOver α) :
    (map sq).obj P = mapObj sq P := sorry

/-- Polynomial base change induces the opposite functor on polynomial sites. -/
def mapOp (sq : CommSq ρ α β φ) : polynomialSite α ⥤ polynomialSite β :=
  (map sq).op

/-- The polynomial site functor is the opposite of polynomial base change. -/
theorem mapOp_eq (sq : CommSq ρ α β φ) :
    mapOp sq = (map sq).op := sorry

end Functoriality

end RingedSite.Cotangent
