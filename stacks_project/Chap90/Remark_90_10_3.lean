module

public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs
public import Mathlib.CategoryTheory.Limits.Types.Pullbacks
public import Mathlib.CategoryTheory.Yoneda
public import stacks_project.Chap90.Remark_90_10_3_DualNumber

/-!
# Schlessinger's conditions (H1) and (H2)

When a category cofibered in groupoids over `ArtinianLocalAlgCat Λ k` is cofibered in sets,
hence corresponds to a functor `F : ArtinianLocalAlgCat Λ k ⥤ Type v`, Stacks (S1) and (S2)
become Schlessinger's (H1) and (H2): surjectivity of the pullback comparison along a
surjection, and bijectivity of the dual-number comparison.
-/

@[expose] public section

open CategoryTheory Limits ArtinianLocalAlgCat Opposite

universe u v

variable {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]

namespace CategoryTheory.Functor

/-- The raw comparison map sending an object over a fibre product to the pair of its images. -/
def pullbackObjMap (F : ArtinianLocalAlgCat Λ k ⥤ Type v)
    {P A1 A2 : ArtinianLocalAlgCat Λ k} (π1 : P ⟶ A1) (π2 : P ⟶ A2) :
    F.obj P → F.obj A1 × F.obj A2 :=
  fun y ↦ (F.map π1 y, F.map π2 y)

/-- Images of a fibre-product object under the two projections agree after mapping to the base. -/
theorem pullbackObjMap_mem (F : ArtinianLocalAlgCat Λ k ⥤ Type v)
    {P A A1 A2 : ArtinianLocalAlgCat Λ k}
    (π1 : P ⟶ A1) (π2 : P ⟶ A2) (f1 : A1 ⟶ A) (f2 : A2 ⟶ A)
    (h : IsPullback π1 π2 f1 f2) (y : F.obj P) :
    F.map f1 (F.map π1 y) = F.map f2 (F.map π2 y) := sorry

/-- The induced comparison `F.obj P → Types.PullbackObj (F.map f1) (F.map f2)`. -/
def pullbackObjMap_subtype (F : ArtinianLocalAlgCat Λ k ⥤ Type v)
    {P A A1 A2 : ArtinianLocalAlgCat Λ k}
    (π1 : P ⟶ A1) (π2 : P ⟶ A2) (f1 : A1 ⟶ A) (f2 : A2 ⟶ A)
    (h : IsPullback π1 π2 f1 f2) :
    F.obj P → Types.PullbackObj (F.map f1) (F.map f2) :=
  fun y ↦ ⟨pullbackObjMap F π1 π2 y, pullbackObjMap_mem F π1 π2 f1 f2 h y⟩

/-- Remark 90.10.3 (1): for a functor `F : ArtinianLocalAlgCat Λ k ⥤ Type v`, Schlessinger's
(H1) is condition (S1): if `IsPullback π1 π2 f1 f2` and `f2` is surjective, then the induced
map `F.obj P → Types.PullbackObj (F.map f1) (F.map f2)` is surjective. -/
@[stacks 06HY]
class HasSchlessingerH1 (F : ArtinianLocalAlgCat Λ k ⥤ Type v) : Prop where
  /-- Along a surjection, the comparison map to the fibre product of values is surjective. -/
  surjective_pullbackObjMap :
    ∀ {A A1 A2 P : ArtinianLocalAlgCat Λ k} (f1 : A1 ⟶ A) (f2 : A2 ⟶ A)
      (π1 : P ⟶ A1) (π2 : P ⟶ A2) (h : IsPullback π1 π2 f1 f2),
      Function.Surjective f2.hom →
        Function.Surjective (pullbackObjMap_subtype F π1 π2 f1 f2 h)

/-- Remark 90.10.3 (2): for a functor `F : ArtinianLocalAlgCat Λ k ⥤ Type v`, Schlessinger's
(H2) is condition (S2): if `IsPullback π1 π2 f (dualNumberToResidue Λ k)`, then the induced
map `F.obj P → Types.PullbackObj (F.map f) (F.map (dualNumberToResidue Λ k))` is bijective. -/
@[stacks 06HY]
class HasSchlessingerH2 (F : ArtinianLocalAlgCat Λ k ⥤ Type v) : Prop where
  /-- The dual-number comparison map is bijective. -/
  bijective_pullbackObjMap :
    ∀ {A P : ArtinianLocalAlgCat Λ k} (f : A ⟶ residue Λ k)
      (π1 : P ⟶ A) (π2 : P ⟶ dualNumber Λ k)
      (h : IsPullback π1 π2 f (dualNumberToResidue Λ k)),
      Function.Bijective (pullbackObjMap_subtype F π1 π2 f (dualNumberToResidue Λ k) h)

/-- Schlessinger's (H1) is surjectivity of the comparison onto matching pairs of values. -/
theorem hasSchlessingerH1_iff (F : ArtinianLocalAlgCat Λ k ⥤ Type v) :
    HasSchlessingerH1 F ↔
      ∀ {A A1 A2 P : ArtinianLocalAlgCat Λ k} (f1 : A1 ⟶ A) (f2 : A2 ⟶ A)
        (π1 : P ⟶ A1) (π2 : P ⟶ A2),
        IsPullback π1 π2 f1 f2 →
          Function.Surjective f2.hom →
            ∀ (x1 : F.obj A1) (x2 : F.obj A2),
              F.map f1 x1 = F.map f2 x2 →
                ∃ y : F.obj P, F.map π1 y = x1 ∧ F.map π2 y = x2 := sorry

/-- Schlessinger's (H2) is bijectivity of the dual-number comparison. -/
theorem hasSchlessingerH2_iff (F : ArtinianLocalAlgCat Λ k ⥤ Type v) :
    HasSchlessingerH2 F ↔
      ∀ {A P : ArtinianLocalAlgCat Λ k} (f : A ⟶ residue Λ k)
        (π1 : P ⟶ A) (π2 : P ⟶ dualNumber Λ k)
        (h : IsPullback π1 π2 f (dualNumberToResidue Λ k)),
        Function.Bijective (pullbackObjMap_subtype F π1 π2 f (dualNumberToResidue Λ k) h) := sorry

/-- Representable functors satisfy Schlessinger's (H1). -/
instance instHasSchlessingerH1Coyoneda (A : ArtinianLocalAlgCat Λ k) :
    HasSchlessingerH1 (coyoneda.obj (op A)) := sorry

/-- Representable functors satisfy Schlessinger's (H2). -/
instance instHasSchlessingerH2Coyoneda (A : ArtinianLocalAlgCat Λ k) :
    HasSchlessingerH2 (coyoneda.obj (op A)) := sorry

/-- Injectivity of the (H2) comparison is uniqueness of a lift with given images, i.e. the
identity-morphism form of the second clause of (S2). -/
theorem pullbackObjMap_subtype_injective_iff_unique
    (F : ArtinianLocalAlgCat Λ k ⥤ Type v) {A P : ArtinianLocalAlgCat Λ k}
    (f : A ⟶ residue Λ k) (π1 : P ⟶ A) (π2 : P ⟶ dualNumber Λ k)
    (h : IsPullback π1 π2 f (dualNumberToResidue Λ k)) :
    Function.Injective (pullbackObjMap_subtype F π1 π2 f (dualNumberToResidue Λ k) h) ↔
      ∀ y₁ y₂ : F.obj P,
        F.map π1 y₁ = F.map π1 y₂ →
          F.map π2 y₁ = F.map π2 y₂ → y₁ = y₂ := sorry

end CategoryTheory.Functor
