module

public import Mathlib.CategoryTheory.Monoidal.Cartesian.Grp
public import ReasLib.CategoryTheory.Fibered.Inertia.Groupoids.RelativeFunctoriality.Stable.Computations
public import ReasLib.CategoryTheory.Inertia.Relative
public import stacks_project.Chap101.Remark_101_5_2_SpacesOver

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

/-- The chosen 2-fibre product `I_{X/Y} ×_X I_{X/Y}`. -/
abbrev inertiaApex {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) : GroupoidsOver S :=
  TwoFibreProduct.apex.{u + 1, u, u + 1, u}
    (forget.{u + 1, u, u, u + 1} f) (forget.{u + 1, u, u, u + 1} f)

/-- The total object of relative-inertia multiplication, sending a 2-fibre-product
object `((x, α), (x', α'), β)` to `(x, α ∘ β⁻¹ ∘ α' ∘ β)`. -/
def compositionObj {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y)
    (P : (inertiaApex f).total) : CategoryTheory.RelativeInertia (toFunctor f) where
  obj := (BasedCategory.PseudoPullback.fstObj P).obj
  aut :=
    let α := (BasedCategory.PseudoPullback.fstObj P).aut
    let α' := (BasedCategory.PseudoPullback.sndObj P).aut
    let β := BasedCategory.PseudoPullback.comparisonIsoApp P
    ((β.trans α').trans β.symm).trans α
  mapAut_eq_one := sorry

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
    sorry

/-- The total functor of relative-inertia multiplication. -/
def compositionFunctor {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) :
    (inertiaApex f).total ⥤ CategoryTheory.RelativeInertia (toFunctor f) where
  obj := compositionObj f
  map := compositionMap f
  map_id := sorry
  map_comp := sorry

/-- Multiplication `I_{X/Y} ×_X I_{X/Y} ⟶ I_{X/Y}` of relative inertia. -/
def composition {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) :
    inertiaApex f ⟶ relativeInertia f :=
  ofBasedFunctor
    { toFunctor := compositionFunctor f
      w := sorry }

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
      (fun _ ↦ sorry) (fun _ ↦ sorry))

/-- Multiplication of relative inertia commutes with the structure map to `X`. -/
theorem composition_comp_forget {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) :
    composition f ≫ forget.{u + 1, u, u, u + 1} f =
      TwoFibreProduct.fst.{u + 1, u, u + 1, u}
          (forget.{u + 1, u, u, u + 1} f)
          (forget.{u + 1, u, u, u + 1} f) ≫
        forget.{u + 1, u, u, u + 1} f :=
  sorry

/-- The total object of relative-inertia inversion, sending `(x, α)` to
`(x, α⁻¹)`. -/
def invObj {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y)
    (ξ : CategoryTheory.RelativeInertia (toFunctor f)) :
    CategoryTheory.RelativeInertia (toFunctor f) where
  obj := ξ.obj
  aut := ξ.aut⁻¹
  mapAut_eq_one := sorry

/-- The total morphism of relative-inertia inversion. -/
def invMap {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y)
    {ξ ξ' : CategoryTheory.RelativeInertia (toFunctor f)} (φ : ξ ⟶ ξ') :
    invObj f ξ ⟶ invObj f ξ' :=
  CategoryTheory.RelativeInertia.homMk (F := toFunctor f)
    (CategoryTheory.RelativeInertia.hom (X := ξ) (Y := ξ') φ) sorry

/-- The total functor of relative-inertia inversion. -/
def invFunctor {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) :
    CategoryTheory.RelativeInertia (toFunctor f) ⥤
      CategoryTheory.RelativeInertia (toFunctor f) where
  obj := invObj f
  map := invMap f
  map_id := sorry
  map_comp := sorry

/-- Inversion `I_{X/Y} ⟶ I_{X/Y}` of relative inertia. -/
def inv {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) :
    relativeInertia f ⟶ relativeInertia f :=
  ofBasedFunctor
    { toFunctor := invFunctor f
      w := sorry }

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

/-- The comparison isomorphism `inv f ≫ forget f ≅ forget f`. -/
def inv_comp_forget_iso {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) :
    inv f ≫ forget.{u + 1, u, u, u + 1} f ≅
      forget.{u + 1, u, u, u + 1} f :=
  Bicategory.InducedBicategory.isoMk
    (BasedNatIso.ofComponents (inv_comp_forget_app f)
      (fun _ ↦ sorry) (fun _ ↦ sorry))

/-- The object component of `identitySection f ≫ forget f` agrees with `𝟙 X`. -/
def identitySection_comp_forget_app {S : Scheme.{u}} {X Y : GroupoidsOver S}
    (f : X ⟶ Y) (x : X.total) :
    (toFunctor
        (identitySection.{u + 1, u, u, u + 1} f ≫
          forget.{u + 1, u, u, u + 1} f)).obj x ≅
      (toFunctor (𝟙 X)).obj x :=
  Iso.refl x

/-- The comparison isomorphism `identitySection f ≫ forget f ≅ 𝟙 X`. -/
def identitySection_comp_forget_iso {S : Scheme.{u}} {X Y : GroupoidsOver S}
    (f : X ⟶ Y) :
    identitySection.{u + 1, u, u, u + 1} f ≫
        forget.{u + 1, u, u, u + 1} f ≅
      𝟙 X :=
  Bicategory.InducedBicategory.isoMk
    (BasedNatIso.ofComponents (identitySection_comp_forget_app f)
      (fun _ ↦ sorry) (fun _ ↦ sorry))

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

/-- The identity section of relative inertia retains the underlying object. -/
theorem one_obj {S : Scheme.{u}} {X Y : GroupoidsOver S} (f : X ⟶ Y)
    (x : X.total) :
    ((toFunctor (identitySection.{u + 1, u, u, u + 1} f)).obj x).obj = x :=
  sorry

/-- The identity section of relative inertia selects the identity automorphism. -/
theorem one_aut {S : Scheme.{u}} {X Y : GroupoidsOver S} (f : X ⟶ Y)
    (x : X.total) :
    ((toFunctor (identitySection.{u + 1, u, u, u + 1} f)).obj x).aut = 1 :=
  sorry

end AlgebraicGeometry.AlgebraicStack.RelativeInertia
