module

public import Mathlib.CategoryTheory.Monoidal.Cartesian.Grp
public import ReasLib.CategoryTheory.Fibered.Inertia.Groupoids.RelativeFunctoriality.Stable.Computations
public import ReasLib.CategoryTheory.Inertia.Relative
public import ReasLib.AlgebraicGeometry.AlgebraicStack.Inertia
public import ReasLib.AlgebraicGeometry.AlgebraicStack.SpacesOver.Cartesian

/-!
# Group-object structure on relative inertia

Relative inertia of a morphism of algebraic stacks is a group object in the
homotopy 1-category of morphisms representable by algebraic spaces, with unit
the identity section, multiplication by conjugation-composition of fibre
automorphisms, and inversion of fibre automorphisms.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open FiberedCategoryOver.Groupoids
open FiberedCategoryOver.Groupoids.RelativeInertia
open AlgebraicGeometry.SpacesOver
open scoped Bicategory CategoryTheory.MonObj

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicStack.RelativeInertia

open FiberedCategoryOver.Groupoids.RelativeInertia
open AlgebraicGeometry.SpacesOver

/-- The relative inertia morphism `I_{X/Y} ⟶ X`, as an object of `SpacesOver X`. -/
def asSpacesOver {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) : SpacesOver X :=
  SpacesOver.mk (forget.{u + 1, u, u, u + 1} f)
    (Groupoids.Hom.LocallyOfFiniteType.relativelyRepresentable _)

/-- The domain of `asSpacesOver f` is the relative inertia stack of `f`. -/
theorem asSpacesOver_left {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) :
    SpacesOver.left (asSpacesOver f) = relativeInertia f :=
  sorry

/-- The structural morphism of `asSpacesOver f` is the relative-inertia forgetful
morphism. -/
theorem asSpacesOver_hom {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) :
    SpacesOver.hom (asSpacesOver f) = forget.{u + 1, u, u, u + 1} f :=
  sorry

/-- Packaged relative inertia has algebraic-stack domain, and its structure map
to `X` is representable by algebraic spaces. -/
theorem asSpacesOver_spec {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) :
    AlgebraicStack (SpacesOver.left (asSpacesOver f)) ∧
      relativelyRepresentableByAlgebraicSpaces (SpacesOver.hom (asSpacesOver f)) :=
  sorry

/-- Relative inertia as an object of the homotopy 1-category of algebraic-space
representable morphisms to `X`. -/
def asHomotopy {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) :
    Bicategory.HomotopyCategory (SpacesOver X) :=
  Bicategory.HomotopyCategory.mk (asSpacesOver f)

/-- The underlying `SpacesOver` object of `asHomotopy f` is `asSpacesOver f`. -/
theorem asHomotopy_as {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) :
    (asHomotopy f).as = asSpacesOver f :=
  sorry



/-- The chosen 2-fibre product `I_{X/Y} ×_X I_{X/Y}`. -/
abbrev inertiaApex {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) : GroupoidsOver S :=
  TwoFibreProduct.apex.{u + 1, u, u + 1, u}
    (forget.{u + 1, u, u, u + 1} f) (forget.{u + 1, u, u, u + 1} f)

section GroupImplementation

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

/-- The conjugation-composition automorphism has neutral image. -/
private theorem Implementation.compositionObj_mem {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y)
    (P : (inertiaApex f).total) :
    (toFunctor f).mapAut (BasedCategory.PseudoPullback.fstObj P).obj
      (let α := (BasedCategory.PseudoPullback.fstObj P).aut
      let α' := (BasedCategory.PseudoPullback.sndObj P).aut
      let β := BasedCategory.PseudoPullback.comparisonIsoApp P
      ((β.trans α').trans β.symm).trans α) = 1 := sorry

/-- The total object of relative-inertia multiplication, sending a 2-fibre-product
object `((x, α), (x', α'), β)` to `(x, α ∘ β⁻¹ ∘ α' ∘ β)`. -/
def compositionObj {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y)
    (P : (inertiaApex f).total) : CategoryTheory.RelativeInertia (toFunctor f) :=
  let α := (BasedCategory.PseudoPullback.fstObj P).aut
  let α' := (BasedCategory.PseudoPullback.sndObj P).aut
  let β := BasedCategory.PseudoPullback.comparisonIsoApp P
  CategoryTheory.RelativeInertia.mk
    (CategoryTheory.Inertia.mk (BasedCategory.PseudoPullback.fstObj P).obj
      (((β.trans α').trans β.symm).trans α)) (Implementation.compositionObj_mem f P)

/-- The first component arrow intertwines the multiplied automorphisms. -/
private theorem Implementation.compositionMap_naturality {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y)
    {P Q : (inertiaApex f).total} (φ : P ⟶ Q) :
    (compositionObj f P).aut.hom ≫ (CategoryTheory.RelativeInertia.hom
        (X := BasedCategory.PseudoPullback.fstObj P)
        (Y := BasedCategory.PseudoPullback.fstObj Q)
        (BasedCategory.PseudoPullback.fstMap φ)) =
      (CategoryTheory.RelativeInertia.hom
        (X := BasedCategory.PseudoPullback.fstObj P)
        (Y := BasedCategory.PseudoPullback.fstObj Q)
        (BasedCategory.PseudoPullback.fstMap φ)) ≫ (compositionObj f Q).aut.hom := sorry

/-- The total morphism of relative-inertia multiplication. -/
def compositionMap {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y)
    {P Q : (inertiaApex f).total} (φ : P ⟶ Q) :
    compositionObj f P ⟶ compositionObj f Q :=
  CategoryTheory.RelativeInertia.homMk (F := toFunctor f)
    (CategoryTheory.RelativeInertia.hom
      (X := BasedCategory.PseudoPullback.fstObj P)
      (Y := BasedCategory.PseudoPullback.fstObj Q)
      (BasedCategory.PseudoPullback.fstMap φ))
    (Implementation.compositionMap_naturality f φ)

/-- Multiplication preserves identity arrows. -/
private theorem Implementation.compositionFunctor_map_id {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) (P : (inertiaApex f).total) :
    compositionMap f (𝟙 P) = 𝟙 (compositionObj f P) := sorry

/-- Multiplication preserves composition of arrows. -/
private theorem Implementation.compositionFunctor_map_comp {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y)
    {P Q R : (inertiaApex f).total} (φ : P ⟶ Q) (ψ : Q ⟶ R) :
    compositionMap f (φ ≫ ψ) = compositionMap f φ ≫ compositionMap f ψ := sorry

/-- The total functor of relative-inertia multiplication. -/
def compositionFunctor {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) :
    (inertiaApex f).total ⥤ CategoryTheory.RelativeInertia (toFunctor f) where
  obj := compositionObj f
  map := compositionMap f
  map_id := Implementation.compositionFunctor_map_id f
  map_comp := Implementation.compositionFunctor_map_comp f

/-- Multiplication preserves the projection to the base scheme. -/
private theorem Implementation.composition_comm {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) :
    compositionFunctor f ⋙ (relativeInertia f).p = (inertiaApex f).p := sorry

/-- Multiplication `I_{X/Y} ×_X I_{X/Y} ⟶ I_{X/Y}` of relative inertia. -/
def composition {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) :
    inertiaApex f ⟶ relativeInertia f :=
  ofBasedFunctor
    { toFunctor := compositionFunctor f
      w := Implementation.composition_comm f }

/-- Multiplication of relative inertia retains the underlying object of the first
factor. -/
theorem composition_obj {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y)
    (P : (inertiaApex f).total) :
    ((toFunctor (composition f)).obj P).obj =
      (BasedCategory.PseudoPullback.fstObj P).obj :=
  sorry

/-- Multiplication of relative inertia sends `((x, α), (x', α'), β)` to the
automorphism `α ∘ β⁻¹ ∘ α' ∘ β`. -/
theorem composition_aut {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y)
    (P : (inertiaApex f).total) :
    ((toFunctor (composition f)).obj P).aut =
      let α := (BasedCategory.PseudoPullback.fstObj P).aut
      let α' := (BasedCategory.PseudoPullback.sndObj P).aut
      let β := BasedCategory.PseudoPullback.comparisonIsoApp P
      ((β.trans α').trans β.symm).trans α :=
  sorry

/-- The object component of `composition f ≫ forget f` agrees with `fst ≫ forget f`. -/
def composition_comp_forget_app {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) (a : (inertiaApex f).total) :
    (toFunctor
        (composition f ≫ forget.{u + 1, u, u, u + 1} f)).obj a ≅
      (toFunctor
        (TwoFibreProduct.fst.{u + 1, u, u + 1, u}
            (forget.{u + 1, u, u, u + 1} f)
            (forget.{u + 1, u, u, u + 1} f) ≫
          forget.{u + 1, u, u, u + 1} f)).obj a :=
  Iso.refl ((BasedCategory.PseudoPullback.fstObj a).obj)

/-- The structural comparison is natural in total-category arrows. -/
private theorem Implementation.composition_comp_forget_naturality {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y)
    {a b : (inertiaApex f).total} (φ : a ⟶ b) :
    (toFunctor (composition f ≫ forget.{u + 1, u, u, u + 1} f)).map φ ≫ (composition_comp_forget_app f b).hom =
      (composition_comp_forget_app f a).hom ≫ (toFunctor (TwoFibreProduct.fst.{u + 1, u, u + 1, u} (forget.{u + 1, u, u, u + 1} f) (forget.{u + 1, u, u, u + 1} f) ≫ forget.{u + 1, u, u, u + 1} f)).map φ := sorry

/-- The structural comparison is vertical over the base. -/
private theorem Implementation.composition_comp_forget_isHomLift {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) (a : (inertiaApex f).total) :
    X.p.IsHomLift (𝟙 ((inertiaApex f).p.obj a)) (composition_comp_forget_app f a).hom := sorry

/-- The comparison isomorphism `composition f ≫ forget f ≅ fst ≫ forget f`. -/
def composition_comp_forget_iso {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) :
    composition f ≫ forget.{u + 1, u, u, u + 1} f ≅
      TwoFibreProduct.fst.{u + 1, u, u + 1, u}
          (forget.{u + 1, u, u, u + 1} f)
          (forget.{u + 1, u, u, u + 1} f) ≫
        forget.{u + 1, u, u, u + 1} f :=
  Bicategory.InducedBicategory.isoMk
    (BasedNatIso.ofComponents (composition_comp_forget_app f)
      (Implementation.composition_comp_forget_naturality f)
      (Implementation.composition_comp_forget_isHomLift f))

/-- The inverse automorphism has neutral image. -/
private theorem Implementation.invObj_mem {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y)
    (ξ : CategoryTheory.RelativeInertia (toFunctor f)) :
    (toFunctor f).mapAut ξ.obj ξ.aut⁻¹ = 1 := sorry

/-- The total object of relative-inertia inversion, sending `(x, α)` to
`(x, α⁻¹)`. -/
def invObj {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y)
    (ξ : CategoryTheory.RelativeInertia (toFunctor f)) :
    CategoryTheory.RelativeInertia (toFunctor f) :=
  CategoryTheory.RelativeInertia.mk (CategoryTheory.Inertia.mk ξ.obj ξ.aut⁻¹)
    (Implementation.invObj_mem f ξ)

/-- The underlying arrow intertwines the inverse automorphisms. -/
private theorem Implementation.invMap_naturality {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y)
    {ξ ξ' : CategoryTheory.RelativeInertia (toFunctor f)} (φ : ξ ⟶ ξ') :
    (invObj f ξ).aut.hom ≫ (CategoryTheory.RelativeInertia.hom (X := ξ) (Y := ξ') φ) =
      (CategoryTheory.RelativeInertia.hom (X := ξ) (Y := ξ') φ) ≫ (invObj f ξ').aut.hom := sorry

/-- The total morphism of relative-inertia inversion. -/
def invMap {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y)
    {ξ ξ' : CategoryTheory.RelativeInertia (toFunctor f)} (φ : ξ ⟶ ξ') :
    invObj f ξ ⟶ invObj f ξ' :=
  CategoryTheory.RelativeInertia.homMk (F := toFunctor f)
    (CategoryTheory.RelativeInertia.hom (X := ξ) (Y := ξ') φ)
    (Implementation.invMap_naturality f φ)

/-- Inversion preserves identity arrows. -/
private theorem Implementation.invFunctor_map_id {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) (ξ : CategoryTheory.RelativeInertia (toFunctor f)) :
    invMap f (𝟙 ξ) = 𝟙 (invObj f ξ) := sorry

/-- Inversion preserves composition of arrows. -/
private theorem Implementation.invFunctor_map_comp {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y)
    {ξ ξ' ξ'' : CategoryTheory.RelativeInertia (toFunctor f)}
    (φ : ξ ⟶ ξ') (ψ : ξ' ⟶ ξ'') :
    invMap f (φ ≫ ψ) = invMap f φ ≫ invMap f ψ := sorry

/-- The total functor of relative-inertia inversion. -/
def invFunctor {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) :
    CategoryTheory.RelativeInertia (toFunctor f) ⥤
      CategoryTheory.RelativeInertia (toFunctor f) where
  obj := invObj f
  map := invMap f
  map_id := Implementation.invFunctor_map_id f
  map_comp := Implementation.invFunctor_map_comp f

/-- Inversion preserves the projection to the base scheme. -/
private theorem Implementation.inv_comm {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) :
    invFunctor f ⋙ (relativeInertia f).p = (relativeInertia f).p := sorry

/-- Inversion `I_{X/Y} ⟶ I_{X/Y}` of relative inertia. -/
def inv {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) :
    relativeInertia f ⟶ relativeInertia f :=
  ofBasedFunctor
    { toFunctor := invFunctor f
      w := Implementation.inv_comm f }

/-- Inversion of relative inertia retains the underlying object. -/
theorem inv_obj_eq {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y)
    (ξ : CategoryTheory.RelativeInertia (toFunctor f)) :
    (invObj f ξ).obj = ξ.obj :=
  sorry

/-- Inversion of relative inertia sends `(x, α)` to `(x, α⁻¹)`. -/
theorem inv_aut {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y)
    (ξ : CategoryTheory.RelativeInertia (toFunctor f)) :
    (invObj f ξ).aut = ξ.aut⁻¹ :=
  sorry

/-- The object component of `inv f ≫ forget f` agrees with `forget f`. -/
def inv_comp_forget_app {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y)
    (ξ : (relativeInertia f).total) :
    (toFunctor (inv f ≫ forget.{u + 1, u, u, u + 1} f)).obj ξ ≅
      (toFunctor (forget.{u + 1, u, u, u + 1} f)).obj ξ :=
  Iso.refl ((toFunctor (forget.{u + 1, u, u, u + 1} f)).obj ξ)

/-- The structural comparison is natural in total-category arrows. -/
private theorem Implementation.inv_comp_forget_naturality {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y)
    {a b : (relativeInertia f).total} (φ : a ⟶ b) :
    (toFunctor (inv f ≫ forget.{u + 1, u, u, u + 1} f)).map φ ≫ (inv_comp_forget_app f b).hom =
      (inv_comp_forget_app f a).hom ≫ (toFunctor (forget.{u + 1, u, u, u + 1} f)).map φ := sorry

/-- The structural comparison is vertical over the base. -/
private theorem Implementation.inv_comp_forget_isHomLift {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) (a : (relativeInertia f).total) :
    X.p.IsHomLift (𝟙 ((relativeInertia f).p.obj a)) (inv_comp_forget_app f a).hom := sorry

/-- The comparison isomorphism `inv f ≫ forget f ≅ forget f`. -/
def inv_comp_forget_iso {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) :
    inv f ≫ forget.{u + 1, u, u, u + 1} f ≅
      forget.{u + 1, u, u, u + 1} f :=
  Bicategory.InducedBicategory.isoMk
    (BasedNatIso.ofComponents (inv_comp_forget_app f)
      (Implementation.inv_comp_forget_naturality f)
      (Implementation.inv_comp_forget_isHomLift f))

/-- The comparison isomorphism `identitySection f ≫ forget f ≅ 𝟙 X`. -/
def identitySection_comp_forget_iso {S : Scheme.{u}} {X Y : GroupoidsOver S}
    (f : X ⟶ Y) :
    identitySection.{u + 1, u, u, u + 1} f ≫
        forget.{u + 1, u, u, u + 1} f ≅
      𝟙 X :=
  eqToIso (identitySection.comp_forget f)

/-- The unit 1-morphism `X ⟶ I_{X/Y}` in `SpacesOver X`. -/
def oneHom {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) :
    SpacesOver.id X ⟶ asSpacesOver f :=
  SpacesOver.homMk (identitySection.{u + 1, u, u, u + 1} f)
    (identitySection_comp_forget_iso f).symm

/-- The multiplication 1-morphism of relative inertia in `SpacesOver X`. -/
def mulHom {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) :
    tensor (asSpacesOver f) (asSpacesOver f) ⟶ asSpacesOver f :=
  SpacesOver.homMk (composition f) (composition_comp_forget_iso f).symm

/-- The inversion 1-morphism of relative inertia in `SpacesOver X`. -/
def invHom {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) :
    asSpacesOver f ⟶ asSpacesOver f :=
  SpacesOver.homMk (inv f) (inv_comp_forget_iso f).symm

open scoped MonoidalCategory

/-- The identity section is a left unit for multiplication. -/
private theorem Implementation.group_one_mul {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) :
    (Bicategory.HomotopyCategory.mkHom (oneHom f)) ▷ (asHomotopy f) ≫ Bicategory.HomotopyCategory.mkHom (mulHom f) = (λ_ (asHomotopy f)).hom := sorry

/-- The identity section is a right unit for multiplication. -/
private theorem Implementation.group_mul_one {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) :
    (asHomotopy f) ◁ (Bicategory.HomotopyCategory.mkHom (oneHom f)) ≫ Bicategory.HomotopyCategory.mkHom (mulHom f) = (ρ_ (asHomotopy f)).hom := sorry

/-- Multiplication of relative inertia is associative. -/
private theorem Implementation.group_mul_assoc {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) :
    ((Bicategory.HomotopyCategory.mkHom (mulHom f)) ▷ (asHomotopy f)) ≫ Bicategory.HomotopyCategory.mkHom (mulHom f) =
      (α_ (asHomotopy f) (asHomotopy f) (asHomotopy f)).hom ≫ ((asHomotopy f) ◁ (Bicategory.HomotopyCategory.mkHom (mulHom f))) ≫ Bicategory.HomotopyCategory.mkHom (mulHom f) := sorry

/-- Inversion is a left inverse for multiplication. -/
private theorem Implementation.group_left_inv {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) :
    CartesianMonoidalCategory.lift (Bicategory.HomotopyCategory.mkHom (invHom f)) (𝟙 (asHomotopy f)) ≫ Bicategory.HomotopyCategory.mkHom (mulHom f) =
      CartesianMonoidalCategory.toUnit (asHomotopy f) ≫ Bicategory.HomotopyCategory.mkHom (oneHom f) := sorry

/-- Inversion is a right inverse for multiplication. -/
private theorem Implementation.group_right_inv {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) :
    CartesianMonoidalCategory.lift (𝟙 (asHomotopy f)) (Bicategory.HomotopyCategory.mkHom (invHom f)) ≫ Bicategory.HomotopyCategory.mkHom (mulHom f) =
      CartesianMonoidalCategory.toUnit (asHomotopy f) ≫ Bicategory.HomotopyCategory.mkHom (oneHom f) := sorry

/-- Relative inertia of a morphism of algebraic stacks is a group object among
algebraic-space-representable morphisms to the source stack, with composition of
fibre automorphisms as multiplication and the identity section as unit. -/
instance instGrpObj {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) :
    GrpObj (asHomotopy f) where
  one := Bicategory.HomotopyCategory.mkHom (oneHom f)
  mul := Bicategory.HomotopyCategory.mkHom (mulHom f)
  inv := Bicategory.HomotopyCategory.mkHom (invHom f)
  one_mul := Implementation.group_one_mul f
  mul_one := Implementation.group_mul_one f
  mul_assoc := Implementation.group_mul_assoc f
  left_inv := Implementation.group_left_inv f
  right_inv := Implementation.group_right_inv f

end GroupImplementation

end AlgebraicGeometry.AlgebraicStack.RelativeInertia
