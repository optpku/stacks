module

public import Mathlib.CategoryTheory.Elements
public import Mathlib.CategoryTheory.Limits.Types.Pullbacks
public import Mathlib.CategoryTheory.Yoneda
public import ReasLib.AlgebraicGeometry.FormalDeformation.Schlessinger

/-!
# Set-valued Schlessinger conditions

For a set-valued functor on Artinian local algebras, the pullback comparison
maps give the set-theoretic forms of Schlessinger's conditions.
-/

@[expose] public section

open CategoryTheory Limits ArtinianLocalAlgCat Opposite

universe u v

variable {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]

namespace CategoryTheory.Functor

/-- The canonical comparison sends an element of a pullback to its two projected images. -/
def pullbackObjMap_subtype (F : ArtinianLocalAlgCat Λ k ⥤ Type v)
    {P A A1 A2 : ArtinianLocalAlgCat Λ k}
    (π1 : P ⟶ A1) (π2 : P ⟶ A2) (f1 : A1 ⟶ A) (f2 : A2 ⟶ A)
    (h : IsPullback π1 π2 f1 f2) :
    F.obj P → Types.PullbackObj (F.map f1) (F.map f2) :=
  fun y ↦
    (PullbackCone.mk (F.map π1) (F.map π2) (F.map_commSq h.toCommSq).w).toPullbackObj y

/-- A functor satisfies the set-valued Schlessinger condition (H1) when every
surjective pullback comparison is surjective. -/
class HasSchlessingerH1 (F : ArtinianLocalAlgCat Λ k ⥤ Type v) : Prop where
  /-- The comparison map is surjective whenever the second cospan leg is surjective. -/
  surjective_pullbackObjMap :
    ∀ {A A1 A2 P : ArtinianLocalAlgCat Λ k} (f1 : A1 ⟶ A) (f2 : A2 ⟶ A)
      (π1 : P ⟶ A1) (π2 : P ⟶ A2) (h : IsPullback π1 π2 f1 f2),
      Function.Surjective f2.hom →
        Function.Surjective (pullbackObjMap_subtype F π1 π2 f1 f2 h)

/-- A functor satisfies the set-valued Schlessinger condition (H2) when every
dual-number pullback comparison is bijective. -/
class HasSchlessingerH2 (F : ArtinianLocalAlgCat Λ k ⥤ Type v) : Prop where
  /-- The dual-number comparison map is bijective. -/
  bijective_pullbackObjMap :
    ∀ {A P : ArtinianLocalAlgCat Λ k} (f : A ⟶ residue Λ k)
      (π1 : P ⟶ A) (π2 : P ⟶ dualNumber Λ k)
      (h : IsPullback π1 π2 f (dualNumberToResidue Λ k)),
      Function.Bijective
        (pullbackObjMap_subtype F π1 π2 f (dualNumberToResidue Λ k) h)

/-- The set-valued Schlessinger condition (H1) is equivalent to surjectivity
onto every matching pair of values. -/
theorem hasSchlessingerH1_iff (F : ArtinianLocalAlgCat Λ k ⥤ Type v) :
    HasSchlessingerH1 F ↔
      ∀ {A A1 A2 P : ArtinianLocalAlgCat Λ k} (f1 : A1 ⟶ A) (f2 : A2 ⟶ A)
        (π1 : P ⟶ A1) (π2 : P ⟶ A2),
        IsPullback π1 π2 f1 f2 →
          Function.Surjective f2.hom →
            ∀ (x1 : F.obj A1) (x2 : F.obj A2),
              F.map f1 x1 = F.map f2 x2 →
                ∃ y : F.obj P, F.map π1 y = x1 ∧ F.map π2 y = x2 := sorry

/-- The set-valued Schlessinger condition (H2) is equivalent to bijectivity
of every dual-number pullback comparison. -/
theorem hasSchlessingerH2_iff (F : ArtinianLocalAlgCat Λ k ⥤ Type v) :
    HasSchlessingerH2 F ↔
      ∀ {A P : ArtinianLocalAlgCat Λ k} (f : A ⟶ residue Λ k)
        (π1 : P ⟶ A) (π2 : P ⟶ dualNumber Λ k)
        (h : IsPullback π1 π2 f (dualNumberToResidue Λ k)),
        Function.Bijective
          (pullbackObjMap_subtype F π1 π2 f (dualNumberToResidue Λ k) h) := sorry

/-- The coyoneda functor of an Artinian local algebra satisfies (H1). -/
instance instHasSchlessingerH1Coyoneda (A : ArtinianLocalAlgCat Λ k) :
    HasSchlessingerH1 (coyoneda.obj (op A)) := sorry

/-- The coyoneda functor of an Artinian local algebra satisfies (H2). -/
instance instHasSchlessingerH2Coyoneda (A : ArtinianLocalAlgCat Λ k) :
    HasSchlessingerH2 (coyoneda.obj (op A)) := sorry

/-- Injectivity of the dual-number comparison is equivalent to uniqueness of
an element with prescribed images under both projections. -/
theorem pullbackObjMap_subtype_injective_iff_unique
    (F : ArtinianLocalAlgCat Λ k ⥤ Type v) {A P : ArtinianLocalAlgCat Λ k}
    (f : A ⟶ residue Λ k) (π1 : P ⟶ A) (π2 : P ⟶ dualNumber Λ k)
    (h : IsPullback π1 π2 f (dualNumberToResidue Λ k)) :
    Function.Injective (pullbackObjMap_subtype F π1 π2 f (dualNumberToResidue Λ k) h) ↔
      ∀ y₁ y₂ : F.obj P,
        F.map π1 y₁ = F.map π1 y₂ →
          F.map π2 y₁ = F.map π2 y₂ → y₁ = y₂ := sorry

/-- The categorical condition (S1) for the category-of-elements projection is
equivalent to the set-valued condition (H1). -/
theorem hasSchlessingerS1_iff_hasSchlessingerH1
    (F : ArtinianLocalAlgCat Λ k ⥤ Type v) :
    HasSchlessingerS1 (CategoryOfElements.π F) ↔ HasSchlessingerH1 F := sorry

/-- The categorical condition (S2) for the category-of-elements projection is
equivalent to the set-valued condition (H2). -/
theorem hasSchlessingerS2_iff_hasSchlessingerH2
    (F : ArtinianLocalAlgCat Λ k ⥤ Type v) :
    HasSchlessingerS2 (CategoryOfElements.π F) ↔ HasSchlessingerH2 F := sorry

end CategoryTheory.Functor
