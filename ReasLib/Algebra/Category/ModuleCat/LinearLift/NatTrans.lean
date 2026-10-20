module

public import ReasLib.Algebra.Category.ModuleCat.LinearLift

/-!
# Natural transformations of linear lifts

A natural transformation of finite-product-preserving functors to types,
each sending the zero object to a singleton, induces a morphism of their
canonical module-valued lifts with the same underlying components.
-/

@[expose] public section

open CategoryTheory hiding Linear
open Limits ZeroObject

noncomputable section

universe u v w

namespace CategoryTheory.Functor

variable {C : Type w} [Category.{v} C] [Preadditive C] [HasBinaryProducts C]
variable {R : Type u} [CommRing R]
variable [CategoryTheory.Linear R C] [HasFiniteProducts C] [HasZeroObject C]
variable {L₁ L₂ : C ⥤ Type v}
variable [PreservesFiniteProducts L₁] [Unique (L₁.obj 0)]
variable [PreservesFiniteProducts L₂] [Unique (L₂.obj 0)]

/-- A natural transformation preserves the canonical addition on functor values. -/
theorem linearLiftApp_map_add (t : L₁ ⟶ L₂) (M : C) (x y : L₁.obj M) :
    t.app M (x + y) = t.app M x + t.app M y := sorry

/-- A natural transformation preserves the canonical scalar action on functor values. -/
theorem linearLiftApp_map_smul (t : L₁ ⟶ L₂) (M : C) (r : R) (x : L₁.obj M) :
    t.app M (r • x) = r • t.app M x := sorry

/-- The component `t.app M` as an `R`-linear map between the values of the
linear lifts of `L₁` and `L₂`. -/
def linearLiftApp (t : L₁ ⟶ L₂) (M : C) : L₁.obj M →ₗ[R] L₂.obj M where
  toFun := t.app M
  map_add' := linearLiftApp_map_add t M
  map_smul' := linearLiftApp_map_smul t M

/-- The linear components of a natural transformation commute with lifted morphisms. -/
theorem linearLiftNatTrans_naturality (t : L₁ ⟶ L₂) {M N : C} (f : M ⟶ N) :
    (linearLift L₁ : C ⥤ ModuleCat.{v} R).map f ≫ ModuleCat.ofHom (linearLiftApp t N) =
      ModuleCat.ofHom (linearLiftApp t M) ≫ (linearLift L₂).map f := sorry

/-- The morphism of `R`-linear lifts induced by a natural transformation of
finite-product-preserving functors to types. -/
def linearLiftNatTrans (t : L₁ ⟶ L₂) :
    (linearLift L₁ : C ⥤ ModuleCat.{v} R) ⟶ (linearLift L₂ : C ⥤ ModuleCat.{v} R) where
  app M := ModuleCat.ofHom (linearLiftApp t M)
  naturality {_ _} f := linearLiftNatTrans_naturality t f

/-- The underlying function of `linearLiftApp t M` is `t.app M`. -/
theorem linearLiftApp_apply (t : L₁ ⟶ L₂) (M : C) (x : L₁.obj M) :
    (linearLiftApp t M : L₁.obj M →ₗ[R] L₂.obj M) x = t.app M x := rfl

/-- The component of `linearLiftNatTrans t` at `M` is the `ModuleCat` packaging of
`linearLiftApp t M`. -/
theorem linearLiftNatTrans_app (t : L₁ ⟶ L₂) (M : C) :
    (linearLiftNatTrans t : (linearLift L₁ : C ⥤ ModuleCat.{v} R) ⟶ linearLift L₂).app M =
      ModuleCat.ofHom (linearLiftApp t M) := rfl

/-- The component of `linearLiftNatTrans t` at `M` agrees with `t.app M` on
underlying elements. -/
theorem linearLiftNatTrans_apply (t : L₁ ⟶ L₂) (M : C) (x : L₁.obj M) :
    (linearLiftNatTrans t : (linearLift L₁ : C ⥤ ModuleCat.{v} R) ⟶ linearLift L₂).app M x =
      t.app M x := rfl

/-- The forgetful functor sends the component of `linearLiftNatTrans t` at `M` to
`t.app M`. -/
theorem forget_map_linearLiftNatTrans_app (t : L₁ ⟶ L₂) (M : C) :
    (forget (ModuleCat.{v} R)).map ((linearLiftNatTrans t).app M) = t.app M := rfl

/-- A morphism of linear lifts whose underlying maps are the components of `t`
equals `linearLiftNatTrans t`. -/
theorem linearLiftNatTrans_unique (t : L₁ ⟶ L₂)
    (α : (linearLift L₁ : C ⥤ ModuleCat.{v} R) ⟶ linearLift L₂)
    (h_forget : ∀ M, (forget (ModuleCat.{v} R)).map (α.app M) = t.app M) :
    α = linearLiftNatTrans t := sorry

end CategoryTheory.Functor
