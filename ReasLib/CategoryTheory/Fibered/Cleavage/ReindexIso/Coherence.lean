module

public import ReasLib.CategoryTheory.Fibered.Cleavage.ReindexIso.Transport
public import ReasLib.CategoryTheory.Fibered.Cleavage.ReindexIso.Identity

/-!
# Coherence for cleavage reindexing comparisons

This leaf provides the objectwise pentagon and equality-of-base-arrow calculations needed when
downstream proofs normalize iterated reindexing without unfolding chosen lifts.
-/

@[expose] public section

universe v₁ v₂ u₁ u₂

namespace CategoryTheory

open Functor

variable {C : Type u₁} [Category.{v₁} C]
variable {S : Type u₂} [Category.{v₂} S]

namespace Functor.Cleavage

variable {p : S ⥤ C} (χ : p.Cleavage)

/-- Reindexing along an endomorphism identified with the identity is canonically isomorphic to
the identity action on the fiber. -/
@[stacks 02XN]
noncomputable def Reindex.eqId.isoApp
    {U : C} (f : U ⟶ U) (hf : f = 𝟙 U) (x : Fiber p U) :
    (χ.reindex f).obj x ≅ x :=
  Reindex.congrIsoApp χ hf x ≪≫ (Reindex.idIsoApp χ U x).symm

/-- The identity-specialized reindexing comparison is natural in the fiber object. -/
theorem Reindex.eqId.isoApp.hom.naturality
    {U : C} (f : U ⟶ U) (hf : f = 𝟙 U)
    {x y : Fiber p U} (φ : x ⟶ y) :
    (χ.reindex f).map φ ≫ (Reindex.eqId.isoApp χ f hf y).hom =
      (Reindex.eqId.isoApp χ f hf x).hom ≫ φ := sorry

/-- The underlying arrow of the identity-specialized comparison is the cleavage's cartesian
arrow over the given endomorphism. -/
theorem Reindex.eqId.isoApp.hom.eq_cartesianHom
    {U : C} (f : U ⟶ U) (hf : f = 𝟙 U) (x : Fiber p U) :
    (Reindex.eqId.isoApp χ f hf x).hom.1 = χ.cartesianHom f x := sorry

/-- Reindexing along an endomorphism equal to the identity is naturally isomorphic to the
identity functor of the fiber. -/
@[stacks 02XN]
noncomputable def Reindex.eqId.iso
    {U : C} (f : U ⟶ U) (hf : f = 𝟙 U) :
    χ.reindex f ≅ 𝟭 (Fiber p U) :=
  Reindex.congrIso χ hf ≪≫ (Reindex.idIso χ U).symm

/-- If `q` is identified with an identity, compare direct reindexing along `f` with first
reindexing along `q` and then along `f`. -/
noncomputable def Reindex.eqId.compIsoApp
    {U V : C} (q : U ⟶ U) (hq : q = 𝟙 U) (f : V ⟶ U) (x : Fiber p U) :
    (χ.reindex f).obj x ≅ (χ.reindex f).obj ((χ.reindex q).obj x) :=
  Reindex.congrIsoApp χ
      ((congrArg (fun e ↦ f ≫ e) hq).trans (Category.comp_id f)).symm x ≪≫
    Reindex.compIsoApp χ q f x

/-- The composition comparison with an identity-like first arrow cancels the corresponding
identity-specialized reindexing comparison. -/
theorem Reindex.eqId.compIsoApp.hom.cancellation
    {U V : C} (q : U ⟶ U) (hq : q = 𝟙 U) (f : V ⟶ U) (x : Fiber p U) :
    (Reindex.eqId.compIsoApp χ q hq f x).hom ≫
        (χ.reindex f).map (Reindex.eqId.isoApp χ q hq x).hom =
      𝟙 ((χ.reindex f).obj x) := sorry

/-- Inverse form of cancellation between composition with an identity-like arrow and its
identity-specialized comparison. -/
theorem Reindex.eqId.compIsoApp.inv.cancellation
    {U V : C} (q : U ⟶ U) (hq : q = 𝟙 U) (f : V ⟶ U) (x : Fiber p U) :
    (Reindex.eqId.compIsoApp χ q hq f x).inv =
      (χ.reindex f).map (Reindex.eqId.isoApp χ q hq x).hom := sorry

/-- The vertical factor of an identity is the inverse identity-reindexing comparison. -/
@[stacks 02XN]
theorem verticalFactor.id (x : S) :
    χ.verticalFactor (𝟙 x) =
      (Reindex.eqId.isoApp χ (p.map (𝟙 x)) (p.map_id x)
        (Fiber.mk (p := p) (a := x) rfl : Fiber p (p.obj x))).inv := sorry

/-- The vertical factor of a composite is obtained by composing the first vertical factor,
the reindexing of the second, and the inverse composition comparison. -/
@[stacks 02XN]
theorem verticalFactor.comp {x y z : S} (φ : x ⟶ y) (ψ : y ⟶ z) :
    χ.verticalFactor (φ ≫ ψ) =
      χ.verticalFactor φ ≫
        (χ.reindex (p.map φ)).map (χ.verticalFactor ψ) ≫
        (Reindex.specifiedCompIsoApp χ
          (p.map ψ) (p.map φ) (p.map (φ ≫ ψ))
          (p.map_comp φ ψ).symm
          (Fiber.mk (p := p) (a := z) rfl : Fiber p (p.obj z))).inv := sorry

/-- Pulling a composition comparison back along a third base arrow satisfies the objectwise
pentagon, with the unique explicit transport recording associativity of base composition.

This is the application-level readout of the associator coherence of
`Cleavage.toPseudofunctor`; it lets downstream reindexing calculations avoid unfolding the
bicategorical presentation. -/
theorem Reindex.compIsoApp.pentagon.hom
    {T V W Z : C} (f : V ⟶ T) (g : W ⟶ V) (h : Z ⟶ W)
    (x : Fiber p T) :
    (χ.reindex h).map ((Reindex.compIsoApp χ f g x).hom) =
      (Reindex.compIsoApp χ (g ≫ f) h x).inv ≫
        eqToHom
          (congrArg (fun r ↦ χ.reindexObj r x) (Category.assoc h g f).symm) ≫
        (Reindex.compIsoApp χ f (h ≫ g) x).hom ≫
        (Reindex.compIsoApp χ g h ((χ.reindex f).obj x)).hom := sorry

/-- Inverse form of the objectwise reindexing pentagon. It rewrites the pullback of an inverse
composition comparison without requiring downstream cancellation of four comparison maps. -/
theorem Reindex.compIsoApp.pentagon.inv
    {T V W Z : C} (f : V ⟶ T) (g : W ⟶ V) (h : Z ⟶ W)
    (x : Fiber p T) :
    (χ.reindex h).map ((Reindex.compIsoApp χ f g x).inv) =
      (Reindex.compIsoApp χ g h ((χ.reindex f).obj x)).inv ≫
        (Reindex.compIsoApp χ f (h ≫ g) x).inv ≫
        eqToHom
          (congrArg (fun r ↦ χ.reindexObj r x) (Category.assoc h g f)) ≫
        (Reindex.compIsoApp χ (g ≫ f) h x).hom := sorry

/-- The forward composition comparison is natural under equality of its second base arrow.
Both dependent object transports are displayed explicitly, so users can rewrite without
unfolding `reindexObj`. -/
theorem Reindex.compIsoApp.baseCongr.hom
    {T V W : C} (f : V ⟶ T) {g g' : W ⟶ V} (h : g = g')
    (x : Fiber p T) :
    (Reindex.compIsoApp χ f g x).hom ≫
        eqToHom
          (congrArg (fun r ↦ χ.reindexObj r ((χ.reindex f).obj x)) h) =
      eqToHom
          (congrArg (fun r ↦ χ.reindexObj r x)
            (congrArg (fun r ↦ r ≫ f) h)) ≫
        (Reindex.compIsoApp χ f g' x).hom := sorry

/-- The inverse composition comparison is natural under equality of its second base arrow. -/
theorem Reindex.compIsoApp.baseCongr.inv
    {T V W : C} (f : V ⟶ T) {g g' : W ⟶ V} (h : g = g')
    (x : Fiber p T) :
    (Reindex.compIsoApp χ f g' x).inv ≫
        eqToHom
          (congrArg (fun r ↦ χ.reindexObj r x)
            (congrArg (fun r ↦ r ≫ f) h)).symm =
      eqToHom
          (congrArg (fun r ↦ χ.reindexObj r ((χ.reindex f).obj x)) h).symm ≫
        (Reindex.compIsoApp χ f g x).inv := sorry

end Functor.Cleavage

end CategoryTheory
