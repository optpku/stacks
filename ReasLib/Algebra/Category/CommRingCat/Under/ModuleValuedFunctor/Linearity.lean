module

public import ReasLib.Algebra.Category.CommRingCat.Under.ModuleValuedFunctor
public import Mathlib.Algebra.Category.ModuleCat.Descent

@[expose] public section

open CategoryTheory RingHom

universe u

namespace ModuleValuedFunctor

variable {A : CommRingCat.{u}} {F G : ModuleValuedFunctor.{u, u} A}

/-- A natural transformation between module-valued functors respects multiplication by units when
each component commutes with scalar multiplication by every unit of the algebra. -/
def RespectsUnitScalars (φ : F.toFunctor ⟶ G.toFunctor) : Prop :=
  ∀ (B : Under A) (u : B.rightˣ) (x : F.obj B),
    let y : G.obj B := φ.app B x
    φ.app B ((u : B.right) • x) = (u : B.right) • y

/-- A module-valued functor has flat base change when its canonical extension-of-scalars map is an
isomorphism for every flat morphism of algebras. -/
def HasFlatBaseChange (G : ModuleValuedFunctor.{u, u} A) : Prop :=
  ∀ {B B' : Under A} (f : B ⟶ B'), Flat f.right.hom →
    IsIso (((ModuleCat.extendRestrictScalarsAdj f.right.hom).homEquiv
      (G.obj B) (G.obj B')).symm (G.map f))

end ModuleValuedFunctor

/-- An additive natural transformation respecting unit scalars gives a bundled module-valued
morphism when the target has flat base change. -/
noncomputable def ModuleValuedFunctor.Hom.ofUnitCompatibleOfFlatBaseChange
    {A : CommRingCat.{u}} {F G : ModuleValuedFunctor.{u, u} A}
    (φ : F.toFunctor ⟶ G.toFunctor)
    (h_units : ModuleValuedFunctor.RespectsUnitScalars φ)
    (h_flat : ModuleValuedFunctor.HasFlatBaseChange G) :
    ModuleValuedFunctor.Hom F G where
  app B :=
    ModuleCat.ofHom
      (LinearMap.mk ((φ.app B).hom.toAddHom : F.obj B →ₙ+ G.obj B) sorry)
  naturality := sorry

/-- The underlying additive natural transformation of the unit-compatible flat-base-change
morphism is the original natural transformation. -/
theorem ModuleValuedFunctor.Hom.ofUnitCompatibleOfFlatBaseChange_toNatTrans
    {A : CommRingCat.{u}} {F G : ModuleValuedFunctor.{u, u} A}
    (φ : F.toFunctor ⟶ G.toFunctor)
    (h_units : ModuleValuedFunctor.RespectsUnitScalars φ)
    (h_flat : ModuleValuedFunctor.HasFlatBaseChange G) :
    (ModuleValuedFunctor.Hom.ofUnitCompatibleOfFlatBaseChange φ h_units h_flat).toNatTrans = φ := sorry
