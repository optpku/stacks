/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Grassmannian.Functor
import StacksCheckRecall

@[expose] public section

open CategoryTheory

universe u

#check (AlgebraicGeometry.Grassmannian.Quotient :
  (k n : ℕ) → AlgebraicGeometry.Scheme.{u} → Type (u + 1))

#check (AlgebraicGeometry.Grassmannian.Quotient.spec :
  ∀ {k n : ℕ} {S : AlgebraicGeometry.Scheme.{u}}
    (Q : AlgebraicGeometry.Grassmannian.Quotient k n S),
    AlgebraicGeometry.Scheme.Modules.IsFiniteLocallyFreeOfRank (n - k) Q.module ∧ Epi Q.map)

#check (AlgebraicGeometry.Grassmannian.Quotient.Rel :
  ∀ {k n : ℕ} {S : AlgebraicGeometry.Scheme.{u}}
    (Q₁ Q₂ : AlgebraicGeometry.Grassmannian.Quotient k n S), Prop)

#check (AlgebraicGeometry.Grassmannian.Quotient.rel_isEquivalence :
  ∀ {k n : ℕ} {S : AlgebraicGeometry.Scheme.{u}},
    Equivalence (@AlgebraicGeometry.Grassmannian.Quotient.Rel k n S))

#check (AlgebraicGeometry.Grassmannian.Quotient.pullback_isLocallyFree :
  ∀ {k n : ℕ} {S T : AlgebraicGeometry.Scheme.{u}} (f : T ⟶ S)
    (Q : AlgebraicGeometry.Grassmannian.Quotient k n S),
    AlgebraicGeometry.Scheme.Modules.IsFiniteLocallyFreeOfRank (n - k)
      ((AlgebraicGeometry.Scheme.Modules.pullback f).obj Q.module))

#check (AlgebraicGeometry.Grassmannian.Quotient.pullback_map_epi :
  ∀ {k n : ℕ} {S T : AlgebraicGeometry.Scheme.{u}} (f : T ⟶ S)
    (Q : AlgebraicGeometry.Grassmannian.Quotient k n S),
    Epi ((SheafOfModules.pullbackObjFreeIso
      (AlgebraicGeometry.RingedSpace.Hom.toRingCatSheafHom f.toShHom)
      (ULift.{u} (Fin n))).inv ≫
        (AlgebraicGeometry.Scheme.Modules.pullback f).map Q.map))

#check (AlgebraicGeometry.Grassmannian.Quotient.pullback :
  ∀ {k n : ℕ} {S T : AlgebraicGeometry.Scheme.{u}} (f : T ⟶ S)
    (Q : AlgebraicGeometry.Grassmannian.Quotient k n S),
    AlgebraicGeometry.Grassmannian.Quotient k n T)

#check (AlgebraicGeometry.Grassmannian.Quotient.rel_pullback :
  ∀ {k n : ℕ} {S T : AlgebraicGeometry.Scheme.{u}} (f : T ⟶ S)
    {Q₁ Q₂ : AlgebraicGeometry.Grassmannian.Quotient k n S},
    AlgebraicGeometry.Grassmannian.Quotient.Rel Q₁ Q₂ →
      AlgebraicGeometry.Grassmannian.Quotient.Rel
        (AlgebraicGeometry.Grassmannian.Quotient.pullback f Q₁)
        (AlgebraicGeometry.Grassmannian.Quotient.pullback f Q₂))

#check (AlgebraicGeometry.Grassmannian.Quotient.pullback_id_rel :
  ∀ {k n : ℕ} {S : AlgebraicGeometry.Scheme.{u}}
    (Q : AlgebraicGeometry.Grassmannian.Quotient k n S),
    AlgebraicGeometry.Grassmannian.Quotient.Rel
      (AlgebraicGeometry.Grassmannian.Quotient.pullback (𝟙 S) Q) Q)

#check (AlgebraicGeometry.Grassmannian.Quotient.pullback_comp_rel :
  ∀ {k n : ℕ} {S T U : AlgebraicGeometry.Scheme.{u}} (f : T ⟶ S) (g : U ⟶ T)
    (Q : AlgebraicGeometry.Grassmannian.Quotient k n S),
    AlgebraicGeometry.Grassmannian.Quotient.Rel
      (AlgebraicGeometry.Grassmannian.Quotient.pullback (g ≫ f) Q)
      (AlgebraicGeometry.Grassmannian.Quotient.pullback g
        (AlgebraicGeometry.Grassmannian.Quotient.pullback f Q)))

#check (AlgebraicGeometry.Grassmannian.quotientSetoid :
  ∀ (k n : ℕ) (S : AlgebraicGeometry.Scheme.{u}),
    Setoid (AlgebraicGeometry.Grassmannian.Quotient k n S))

#check (AlgebraicGeometry.Grassmannian.quotientSetoid_rel_pullback :
  ∀ {k n : ℕ} {S T : AlgebraicGeometry.Scheme.{u}} (f : T ⟶ S)
    {Q₁ Q₂ : AlgebraicGeometry.Grassmannian.Quotient k n S},
    (AlgebraicGeometry.Grassmannian.quotientSetoid k n S).r Q₁ Q₂ →
      (AlgebraicGeometry.Grassmannian.quotientSetoid k n T).r
        (AlgebraicGeometry.Grassmannian.Quotient.pullback f Q₁)
        (AlgebraicGeometry.Grassmannian.Quotient.pullback f Q₂))

#check (AlgebraicGeometry.Grassmannian.map :
  ∀ (k n : ℕ) {S T : AlgebraicGeometry.Scheme.{u}ᵒᵖ} (f : S ⟶ T),
    _root_.Quotient (AlgebraicGeometry.Grassmannian.quotientSetoid k n S.unop) ⟶
      _root_.Quotient (AlgebraicGeometry.Grassmannian.quotientSetoid k n T.unop))

#check (AlgebraicGeometry.Grassmannian.map_id :
  ∀ (k n : ℕ) (S : AlgebraicGeometry.Scheme.{u}ᵒᵖ),
    AlgebraicGeometry.Grassmannian.map k n (𝟙 S) =
      𝟙 (_root_.Quotient
        (AlgebraicGeometry.Grassmannian.quotientSetoid k n S.unop)))

#check (AlgebraicGeometry.Grassmannian.map_comp :
  ∀ (k n : ℕ) {S T U : AlgebraicGeometry.Scheme.{u}ᵒᵖ}
    (f : S ⟶ T) (g : T ⟶ U),
    AlgebraicGeometry.Grassmannian.map k n (f ≫ g) =
      AlgebraicGeometry.Grassmannian.map k n f ≫
        AlgebraicGeometry.Grassmannian.map k n g)

#check (AlgebraicGeometry.Grassmannian.functor_obj :
  ∀ (k n : ℕ) (S : AlgebraicGeometry.Scheme.{u}ᵒᵖ),
    (AlgebraicGeometry.Grassmannian.functor k n).obj S =
      _root_.Quotient
        (AlgebraicGeometry.Grassmannian.quotientSetoid k n S.unop))

/- 27.22.0.1: for natural numbers `k` and `n` satisfying `0 < k` and `k < n`, `G(k, n)` is
the contravariant functor from schemes to sets classifying rank-`n - k` locally free quotients
of the free rank-`n` module sheaf. -/
@[stacks 089S] #check (AlgebraicGeometry.Grassmannian.functor :
  ∀ (_k _n : ℕ), AlgebraicGeometry.Scheme.{u}ᵒᵖ ⥤ Type (u + 1))
