module

public import stacks_project.Chap90.Lemma_90_11_4_LinearLift

/-!
# Morphisms of linear lifts

A natural transformation of finite-product-preserving functors to types,
each sending the zero object to a singleton, induces a morphism of the
associated `R`-linear lifts, with the same underlying components.
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

/-- The component `t.app M` as an `R`-linear map between the values of the
linear lifts of `L₁` and `L₂`. -/
def linearLiftApp (t : L₁ ⟶ L₂) (M : C) : L₁.obj M →ₗ[R] L₂.obj M where
  toFun := t.app M
  map_add' := sorry
  map_smul' := sorry

/-- The morphism of `R`-linear lifts induced by a natural transformation of
finite-product-preserving functors to types. -/
def linearLiftNatTrans (t : L₁ ⟶ L₂) :
    (linearLift L₁ : C ⥤ ModuleCat.{v} R) ⟶ (linearLift L₂ : C ⥤ ModuleCat.{v} R) where
  app M := ModuleCat.ofHom (linearLiftApp t M)
  naturality := sorry

/-- The underlying function of `linearLiftApp t M` is `t.app M`. -/
theorem linearLiftApp_apply (t : L₁ ⟶ L₂) (M : C) (x : L₁.obj M) :
    (linearLiftApp t M : L₁.obj M →ₗ[R] L₂.obj M) x = t.app M x := sorry

/-- The component of `linearLiftNatTrans t` at `M` is the `ModuleCat` packaging of
`linearLiftApp t M`. -/
theorem linearLiftNatTrans_app (t : L₁ ⟶ L₂) (M : C) :
    (linearLiftNatTrans t : (linearLift L₁ : C ⥤ ModuleCat.{v} R) ⟶ linearLift L₂).app M =
      ModuleCat.ofHom (linearLiftApp t M) := sorry

/-- The component of `linearLiftNatTrans t` at `M` agrees with `t.app M` on
underlying elements. -/
theorem linearLiftNatTrans_apply (t : L₁ ⟶ L₂) (M : C) (x : L₁.obj M) :
    (linearLiftNatTrans t : (linearLift L₁ : C ⥤ ModuleCat.{v} R) ⟶ linearLift L₂).app M x =
      t.app M x := sorry

/-- The forgetful functor sends the component of `linearLiftNatTrans t` at `M` to
`t.app M`. -/
theorem forget_map_linearLiftNatTrans_app (t : L₁ ⟶ L₂) (M : C) :
    (forget (ModuleCat.{v} R)).map ((linearLiftNatTrans t).app M) = t.app M := sorry

/-- A morphism of linear lifts whose underlying maps are the components of `t`
equals `linearLiftNatTrans t`. -/
theorem linearLiftNatTrans_unique (t : L₁ ⟶ L₂)
    (α : (linearLift L₁ : C ⥤ ModuleCat.{v} R) ⟶ linearLift L₂)
    (h_forget : ∀ M, (forget (ModuleCat.{v} R)).map (α.app M) = t.app M) :
    α = linearLiftNatTrans t := sorry

end CategoryTheory.Functor
