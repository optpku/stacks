/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Bicategory.Pseudofunctor.IndexedFunctor.StrongTrans.ToIndexed

/-!
# From identity-base indexed functors to strong transformations

An indexed functor over `𝟭 C` contains exactly the component data of a strong transformation on
`LocallyDiscrete Cᵒᵖ`. This leaf supplies the reverse conversion and records that the two
presentations are equivalent.
-/

@[expose] public section

universe uC vC uF vF

namespace CategoryTheory

open Bicategory Opposite
open scoped CategoryTheory.Bicategory Pseudofunctor.StrongTrans

namespace Pseudofunctor.LocallyDiscreteOpToCat.IndexedFunctor

variable {C : Type uC} [Category.{vC} C]
variable {F G : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{vF, uF}}

/-- The strong naturality isomorphism underlying an identity-base indexed functor. -/
noncomputable def toStrongTransNaturality
    (H : IndexedFunctor (𝟭 C) F G)
    {a b : LocallyDiscrete Cᵒᵖ} (f : a ⟶ b) :
    F.map f ≫ (H.app (unop b.as)).toCatHom ≅
      (H.app (unop a.as)).toCatHom ≫ G.map f :=
  Cat.Hom.isoMk (H.naturality f.as.unop)

/-- Naturality of the identity-base indexed comparison with respect to base `2`-morphisms. -/
theorem toStrongTransNaturality.naturality₂
    (H : IndexedFunctor (𝟭 C) F G)
    {a b : LocallyDiscrete Cᵒᵖ} {f g : a ⟶ b} (eta : f ⟶ g) :
    F.map₂ eta ▷ (H.app (unop b.as)).toCatHom ≫
        (toStrongTransNaturality H g).hom =
      (toStrongTransNaturality H f).hom ≫
        (H.app (unop a.as)).toCatHom ◁ G.map₂ eta := sorry

/-- Identity coherence for the strong comparison underlying an identity-base indexed functor. -/
theorem toStrongTransNaturality.identity
    (H : IndexedFunctor (𝟭 C) F G) (a : LocallyDiscrete Cᵒᵖ) :
    (toStrongTransNaturality H (𝟙 a)).hom ≫
        (H.app (unop a.as)).toCatHom ◁ (G.mapId a).hom =
      (F.mapId a).hom ▷ (H.app (unop a.as)).toCatHom ≫
        (λ_ ((H.app (unop a.as)).toCatHom)).hom ≫
          (ρ_ ((H.app (unop a.as)).toCatHom)).inv := sorry

/-- Composition coherence for the strong comparison underlying an identity-base indexed
functor. -/
theorem toStrongTransNaturality.composition
    (H : IndexedFunctor (𝟭 C) F G)
    {a b c : LocallyDiscrete Cᵒᵖ} (f : a ⟶ b) (g : b ⟶ c) :
    (toStrongTransNaturality H (f ≫ g)).hom ≫
        (H.app (unop a.as)).toCatHom ◁ (G.mapComp f g).hom =
      (F.mapComp f g).hom ▷ (H.app (unop c.as)).toCatHom ≫
        (α_ _ _ _).hom ≫
          F.map f ◁ (toStrongTransNaturality H g).hom ≫
          (α_ _ _ _).inv ≫
            (toStrongTransNaturality H f).hom ▷ G.map g ≫
            (α_ _ _ _).hom := sorry

/-- Convert an indexed functor over `𝟭 C` into a strong transformation. All component and
naturality data is retained literally; only the three coherence fields are proof-valued. -/
noncomputable def toStrongTrans
    (H : IndexedFunctor (𝟭 C) F G) : Pseudofunctor.StrongTrans F G where
  app a := (H.app (unop a.as)).toCatHom
  naturality f := toStrongTransNaturality H f
  naturality_naturality eta := toStrongTransNaturality.naturality₂ H eta
  naturality_id a := toStrongTransNaturality.identity H a
  naturality_comp f g := toStrongTransNaturality.composition H f g

/-- Components of the recovered strong transformation are the indexed-functor components. -/
@[simp]
theorem toStrongTrans.app
    (H : IndexedFunctor (𝟭 C) F G) (a : LocallyDiscrete Cᵒᵖ) :
    H.toStrongTrans.app a = (H.app (unop a.as)).toCatHom := sorry

/-- Naturality of the recovered strong transformation is the `Cat`-bundled indexed
naturality isomorphism. -/
@[simp]
theorem toStrongTrans.naturality
    (H : IndexedFunctor (𝟭 C) F G)
    {a b : LocallyDiscrete Cᵒᵖ} (f : a ⟶ b) :
    H.toStrongTrans.naturality f = toStrongTransNaturality H f := sorry

/-- Objectwise forward naturality of the recovered strong transformation is indexed
naturality. -/
@[simp]
theorem toStrongTrans.naturality.hom.app
    (H : IndexedFunctor (𝟭 C) F G)
    {a b : LocallyDiscrete Cᵒᵖ} (f : a ⟶ b) (x : F.obj a) :
    (H.toStrongTrans.naturality f).hom.toNatTrans.app x =
      (H.naturality f.as.unop).hom.app x := sorry

/-- Objectwise inverse naturality of the recovered strong transformation is inverse indexed
naturality. -/
@[simp]
theorem toStrongTrans.naturality.inv.app
    (H : IndexedFunctor (𝟭 C) F G)
    {a b : LocallyDiscrete Cᵒᵖ} (f : a ⟶ b) (x : F.obj a) :
    (H.toStrongTrans.naturality f).inv.toNatTrans.app x =
      (H.naturality f.as.unop).inv.app x := sorry

/-- Converting an identity-base indexed functor to a strong transformation and back recovers
the indexed functor. -/
@[simp]
theorem toStrongTrans.toIndexedFunctor
    (H : IndexedFunctor (𝟭 C) F G) :
    H.toStrongTrans.toIndexedFunctor = H := sorry

end Pseudofunctor.LocallyDiscreteOpToCat.IndexedFunctor

namespace Pseudofunctor.StrongTrans

variable {C : Type uC} [Category.{vC} C]
variable {F G : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{vF, uF}}

/-- Converting a strong transformation to an indexed functor and back recovers the strong
transformation. -/
@[simp]
theorem toIndexedFunctor.toStrongTrans (eta : StrongTrans F G) :
    eta.toIndexedFunctor.toStrongTrans = eta := sorry

/-- Strong transformations on `LocallyDiscrete Cᵒᵖ` are equivalent to indexed functors over
the identity of `C`. -/
noncomputable def indexedFunctorEquiv :
    StrongTrans F G ≃
      Pseudofunctor.LocallyDiscreteOpToCat.IndexedFunctor (𝟭 C) F G where
  toFun := toIndexedFunctor
  invFun := Pseudofunctor.LocallyDiscreteOpToCat.IndexedFunctor.toStrongTrans
  left_inv := toIndexedFunctor.toStrongTrans
  right_inv :=
    Pseudofunctor.LocallyDiscreteOpToCat.IndexedFunctor.toStrongTrans.toIndexedFunctor

/-- The forward map of the representation equivalence is `toIndexedFunctor`. -/
@[simp]
theorem indexedFunctorEquiv_apply (eta : StrongTrans F G) :
    indexedFunctorEquiv eta = eta.toIndexedFunctor := sorry

/-- The inverse map of the representation equivalence is `toStrongTrans`. -/
@[simp]
theorem indexedFunctorEquiv_symm_apply
    (H : Pseudofunctor.LocallyDiscreteOpToCat.IndexedFunctor (𝟭 C) F G) :
    indexedFunctorEquiv.symm H = H.toStrongTrans := sorry

end Pseudofunctor.StrongTrans

end CategoryTheory
