module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackFree
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Site
public import ReasLib.AlgebraicGeometry.Scheme.Module.FiniteLocallyFree.Rank

/-!
# The Grassmannian functor

This file defines the contravariant functor of locally free quotients of a fixed free module
sheaf on schemes.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.Grassmannian

/-- A rank-`n - k` locally free quotient of the free rank-`n` module sheaf on a scheme. -/
structure Quotient (k n : ℕ) (S : Scheme.{u}) where
  /-- The target module sheaf of the quotient. -/
  module : S.Modules
  /-- The target is finite locally free of rank `n - k`. -/
  isLocallyFree : Scheme.Modules.IsFiniteLocallyFreeOfRank (n - k) module
  /-- The morphism from the free rank-`n` module sheaf to the target. -/
  map : (SheafOfModules.free.{u} (ULift.{u} (Fin n)) : S.Modules) ⟶ module
  /-- The quotient morphism is an epimorphism. -/
  map_epi : Epi map

namespace Quotient

/-- The defining local-freeness and epimorphism properties of a Grassmannian quotient. -/
theorem spec {k n : ℕ} {S : Scheme.{u}}
    (Q : _root_.AlgebraicGeometry.Grassmannian.Quotient k n S) :
    Scheme.Modules.IsFiniteLocallyFreeOfRank (n - k) Q.module ∧ Epi Q.map := sorry

/-- Two quotient data are related when their target module sheaves are isomorphic compatibly
with the quotient morphisms. -/
def Rel {k n : ℕ} {S : Scheme.{u}}
    (Q₁ Q₂ : _root_.AlgebraicGeometry.Grassmannian.Quotient k n S) : Prop :=
  ∃ e : Q₁.module ≅ Q₂.module, Q₁.map ≫ e.hom = Q₂.map

/-- Compatible target isomorphism defines an equivalence relation on Grassmannian quotients. -/
theorem rel_isEquivalence {k n : ℕ} {S : Scheme.{u}} :
    Equivalence (@Rel k n S) := sorry

/-- Pullback preserves finite local freeness of the rank prescribed by a Grassmannian quotient. -/
theorem pullback_isLocallyFree {k n : ℕ} {S T : Scheme.{u}} (f : T ⟶ S)
    (Q : _root_.AlgebraicGeometry.Grassmannian.Quotient k n S) :
    Scheme.Modules.IsFiniteLocallyFreeOfRank (n - k)
      ((Scheme.Modules.pullback f).obj Q.module) := sorry

/-- The quotient morphism obtained by pullback and the canonical free-module comparison is an
epimorphism. -/
theorem pullback_map_epi {k n : ℕ} {S T : Scheme.{u}} (f : T ⟶ S)
    (Q : _root_.AlgebraicGeometry.Grassmannian.Quotient k n S) :
    Epi ((SheafOfModules.pullbackObjFreeIso
      (RingedSpace.Hom.toRingCatSheafHom f.toShHom)
      (ULift.{u} (Fin n))).inv ≫ (Scheme.Modules.pullback f).map Q.map) := sorry

/-- Pull back a Grassmannian quotient along a morphism of schemes. -/
noncomputable def pullback {k n : ℕ} {S T : Scheme.{u}} (f : T ⟶ S)
    (Q : _root_.AlgebraicGeometry.Grassmannian.Quotient k n S) :
    _root_.AlgebraicGeometry.Grassmannian.Quotient k n T where
  module := (Scheme.Modules.pullback f).obj Q.module
  isLocallyFree := pullback_isLocallyFree f Q
  map :=
    (SheafOfModules.pullbackObjFreeIso
      (RingedSpace.Hom.toRingCatSheafHom f.toShHom)
      (ULift.{u} (Fin n))).inv ≫ (Scheme.Modules.pullback f).map Q.map
  map_epi := pullback_map_epi f Q

/-- Pullback preserves compatible isomorphisms between Grassmannian quotients. -/
theorem rel_pullback {k n : ℕ} {S T : Scheme.{u}} (f : T ⟶ S)
    {Q₁ Q₂ : _root_.AlgebraicGeometry.Grassmannian.Quotient k n S} :
    Rel Q₁ Q₂ → Rel (pullback f Q₁) (pullback f Q₂) := sorry

/-- Pullback along the identity morphism is related to the original Grassmannian quotient. -/
theorem pullback_id_rel {k n : ℕ} {S : Scheme.{u}}
    (Q : _root_.AlgebraicGeometry.Grassmannian.Quotient k n S) :
    Rel (pullback (𝟙 S) Q) Q := sorry

/-- Pullback along a composite is related to the corresponding iterated pullback. -/
theorem pullback_comp_rel {k n : ℕ} {S T U : Scheme.{u}} (f : T ⟶ S) (g : U ⟶ T)
    (Q : _root_.AlgebraicGeometry.Grassmannian.Quotient k n S) :
    Rel (pullback (g ≫ f) Q) (pullback g (pullback f Q)) := sorry

end Quotient

/-- The setoid of locally free quotients modulo compatible target isomorphism. -/
def quotientSetoid (k n : ℕ) (S : Scheme.{u}) :
    Setoid (_root_.AlgebraicGeometry.Grassmannian.Quotient k n S) where
  r := Quotient.Rel
  iseqv := Quotient.rel_isEquivalence

/-- Pullback preserves the relation of the Grassmannian quotient setoid. -/
theorem quotientSetoid_rel_pullback {k n : ℕ} {S T : Scheme.{u}} (f : T ⟶ S) :
    ∀ {Q₁ Q₂ : _root_.AlgebraicGeometry.Grassmannian.Quotient k n S},
      (quotientSetoid k n S).r Q₁ Q₂ →
        (quotientSetoid k n T).r (Quotient.pullback f Q₁) (Quotient.pullback f Q₂) := sorry

/-- The map on equivalence classes of locally free quotients induced by pullback. -/
def map (k n : ℕ) {S T : Scheme.{u}ᵒᵖ} (f : S ⟶ T) :
    _root_.Quotient (quotientSetoid k n S.unop) ⟶
      _root_.Quotient (quotientSetoid k n T.unop) :=
  TypeCat.ofHom (fun Q ↦ _root_.Quotient.map
    (@Quotient.pullback k n S.unop T.unop f.unop)
    (@quotientSetoid_rel_pullback k n S.unop T.unop f.unop) Q)

/-- Pullback along the identity induces the identity on quotient classes. -/
theorem map_id (k n : ℕ) (S : Scheme.{u}ᵒᵖ) :
    map k n (𝟙 S) = 𝟙 (_root_.Quotient (quotientSetoid k n S.unop)) := sorry

/-- Pullback along a composite induces the composite of the pullback maps on quotient classes. -/
theorem map_comp (k n : ℕ) {S T U : Scheme.{u}ᵒᵖ} (f : S ⟶ T) (g : T ⟶ U) :
    map k n (f ≫ g) = map k n f ≫ map k n g := sorry

/-- The contravariant Grassmannian functor of rank-`n - k` locally free quotients of the free
rank-`n` module sheaf. -/
def functor (k n : ℕ) : Scheme.{u}ᵒᵖ ⥤ Type (u + 1) where
  obj S := _root_.Quotient (quotientSetoid k n S.unop)
  map f := map k n f
  map_id S := map_id k n S
  map_comp f g := map_comp k n f g

/-- The value of the Grassmannian functor is the quotient of locally free quotient data by
compatible target isomorphism. -/
theorem functor_obj (k n : ℕ) (S : Scheme.{u}ᵒᵖ) :
    (functor k n).obj S = _root_.Quotient (quotientSetoid k n S.unop) := sorry

end AlgebraicGeometry.Grassmannian
