/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.InducedCategory
public import Mathlib.CategoryTheory.FiberedCategory.Fiber
public import ReasLib.AlgebraicGeometry.FormalDeformation.FiltrationEquivalence
public import ReasLib.CategoryTheory.Fibered.BasedCategory.Equivalence.Basic

/-!
# Completion along a family of filtrations

This module constructs the total category of formal objects indexed by an
objectwise family of ideal filtrations and compares it with ordinary completion.
-/

@[expose] public section
noncomputable section

open CategoryTheory CompleteLocalAlgCat
open scoped BasedFunctor

universe u v

variable {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]
variable {F : Type v} [Category.{v} F]

namespace FormalObject

/-- The total category of formal objects indexed by a family of filtrations. -/
abbrev AlongOver (p : F ⥤ ArtinianLocalAlgCat Λ k)
    (I : ∀ R : CompleteLocalAlgCat Λ k, AdicIdealFiltration R)
    [Functor.IsFibered.InGroupoids p.op] :=
  InducedCategory (FormalObject p)
    (fun ξ : Σ R : CompleteLocalAlgCat Λ k, Along p R (I R) ↦ ξ.2.toFormalObject)

namespace AlongOver

variable {p : F ⥤ ArtinianLocalAlgCat Λ k}
variable [Functor.IsFibered.InGroupoids p.op]

/-- The complete local base stored by an object of the total category. -/
def base {I : ∀ R : CompleteLocalAlgCat Λ k, AdicIdealFiltration R}
    (ξ : AlongOver p I) : CompleteLocalAlgCat Λ k := ξ.1

/-- The filtration-indexed formal object stored by an object of the total category. -/
def along {I : ∀ R : CompleteLocalAlgCat Λ k, AdicIdealFiltration R}
    (ξ : AlongOver p I) : Along p ξ.base (I ξ.base) := ξ.2

/-- Package a complete local base and a formal object along its filtration. -/
def of (I : ∀ R : CompleteLocalAlgCat Λ k, AdicIdealFiltration R)
    (R : CompleteLocalAlgCat Λ k) (ξ : Along p R (I R)) : AlongOver p I := ⟨R, ξ⟩

/-- The base of a packaged total-category object is the supplied base. -/
theorem of_base (I : ∀ R : CompleteLocalAlgCat Λ k, AdicIdealFiltration R)
    (R : CompleteLocalAlgCat Λ k) (ξ : Along p R (I R)) :
    (of I R ξ).base = R := rfl

/-- The filtration-indexed object of a packaged total-category object is the supplied object. -/
theorem of_along (I : ∀ R : CompleteLocalAlgCat Λ k, AdicIdealFiltration R)
    (R : CompleteLocalAlgCat Λ k) (ξ : Along p R (I R)) :
    (of I R ξ).along = ξ := rfl

/-- The stagewise quotient and transition-lift specification of a total-category object. -/
theorem spec {I : ∀ R : CompleteLocalAlgCat Λ k, AdicIdealFiltration R}
    (ξ : AlongOver p I) (n : ℕ) :
    p.obj (ξ.along.system.family n) = (I ξ.base).truncation n ∧
      p.IsHomLift ((I ξ.base).truncationMap n) (ξ.along.system.stepMap n) :=
  ⟨ξ.along.over_obj n, ξ.along.over_step n⟩

variable {I : ∀ R : CompleteLocalAlgCat Λ k, AdicIdealFiltration R}
/-- The ordinary formal object obtained from the stored filtration-indexed object. -/
noncomputable def toFormalObject (ξ : AlongOver p I) : FormalObject p :=
  ξ.along.toFormalObject

/-- The comparison functor from the induced total category to formal objects. -/
noncomputable def toCompletion
    (I : ∀ R : CompleteLocalAlgCat Λ k, AdicIdealFiltration R)
    (p : F ⥤ ArtinianLocalAlgCat Λ k) [Functor.IsFibered.InGroupoids p.op] :
    AlongOver p I ⥤ FormalObject p :=
  inducedFunctor (fun ξ : Σ R : CompleteLocalAlgCat Λ k, Along p R (I R) ↦ ξ.2.toFormalObject)

/-- The object map of the comparison functor is the maximal-adic pushforward. -/
theorem toCompletion_obj (ξ : AlongOver p I) :
    (toCompletion I p).obj ξ = ξ.along.toFormalObject := rfl

end AlongOver

end FormalObject

namespace CategoryTheory.Functor

/-- Projection from the total filtration category to complete local algebras. -/
noncomputable def completionAlong
    (I : ∀ R : CompleteLocalAlgCat Λ k, AdicIdealFiltration R)
    (p : F ⥤ ArtinianLocalAlgCat Λ k) [IsFibered.InGroupoids p.op] :
    FormalObject.AlongOver p I ⥤ CompleteLocalAlgCat Λ k :=
  FormalObject.AlongOver.toCompletion I p ⋙ completion p

/-- The projection sends a total-category object to its stored base. -/
theorem completionAlong_obj
    (I : ∀ R : CompleteLocalAlgCat Λ k, AdicIdealFiltration R)
    (p : F ⥤ ArtinianLocalAlgCat Λ k) [IsFibered.InGroupoids p.op]
    (ξ : FormalObject.AlongOver p I) :
    (completionAlong I p).obj ξ = ξ.base := rfl

/-- The projection sends a total-category morphism to its base morphism. -/
theorem completionAlong_map
    (I : ∀ R : CompleteLocalAlgCat Λ k, AdicIdealFiltration R)
    (p : F ⥤ ArtinianLocalAlgCat Λ k) [IsFibered.InGroupoids p.op]
    {ξ η : FormalObject.AlongOver p I} (a : ξ ⟶ η) :
    (completionAlong I p).map a = (completion p).map a.hom := rfl

/-- The projection from the total filtration category is cofibered in groupoids. -/
theorem completionAlong_op_isFiberedInGroupoids
    (I : ∀ R : CompleteLocalAlgCat Λ k, AdicIdealFiltration R)
    (p : F ⥤ ArtinianLocalAlgCat Λ k) [IsFibered.InGroupoids p.op] :
    IsFibered.InGroupoids (completionAlong I p).op := sorry

end CategoryTheory.Functor

namespace FormalObject.AlongOver

variable {p : F ⥤ ArtinianLocalAlgCat Λ k}
variable {I : ∀ R : CompleteLocalAlgCat Λ k, AdicIdealFiltration R}
variable [Functor.IsFibered.InGroupoids p.op]

/-- The comparison functor commutes strictly with projection to the complete base. -/
theorem toCompletion_comp :
    toCompletion I p ⋙ Functor.completion p = Functor.completionAlong I p := rfl

/-- The underlying morphism used by the fixed-base fibre comparison. -/
noncomputable def ofAlongMap
    (I : ∀ R : CompleteLocalAlgCat Λ k, AdicIdealFiltration R)
    (R : CompleteLocalAlgCat Λ k) {ξ η : Along p R (I R)} (a : Along.Hom ξ η) :
    of I R ξ ⟶ of I R η :=
  InducedCategory.homMk (Along.toFormalObjectMap a)

set_option backward.privateInPublic true in
/-- The underlying fibre morphism lies over the identity of the fixed base. -/
private theorem ofAlongMap_lift
    (I : ∀ R : CompleteLocalAlgCat Λ k, AdicIdealFiltration R)
    (R : CompleteLocalAlgCat Λ k) {ξ η : Along p R (I R)} (a : Along.Hom ξ η) :
    (Functor.completionAlong I p).IsHomLift (𝟙 R) (ofAlongMap I R a) :=
  Functor.IsHomLift.map (p := Functor.completionAlong I p) (ofAlongMap I R a)

set_option backward.privateInPublic true in
/-- The fibre morphism construction preserves identity morphisms. -/
private theorem ofAlongMap_id
    (I : ∀ R : CompleteLocalAlgCat Λ k, AdicIdealFiltration R)
    (R : CompleteLocalAlgCat Λ k) (ξ : Along p R (I R)) :
    -- Local instance justification (defeq pin): the identity law uses the explicit Along category.
    letI := Along.category (p := p) (R := R) (I := I R)
    ofAlongMap I R (𝟙 ξ) = 𝟙 (of I R ξ) := by
  letI := Along.category (p := p) (R := R) (I := I R)
  apply InducedCategory.hom_ext
  exact congrArg (fun f ↦ Functor.Fiber.fiberInclusion.map f)
    ((Along.toFiber p R (I R)).map_id ξ)

set_option backward.privateInPublic true in
/-- The fibre morphism construction preserves composition. -/
private theorem ofAlongMap_comp
    (I : ∀ R : CompleteLocalAlgCat Λ k, AdicIdealFiltration R)
    (R : CompleteLocalAlgCat Λ k) {ξ η ζ : Along p R (I R)}
    (a : Along.Hom ξ η) (b : Along.Hom η ζ) :
    -- Local instance justification (defeq pin): the composition law uses the explicit Along category.
    letI := Along.category (p := p) (R := R) (I := I R)
    ofAlongMap I R (Along.Hom.comp a b) = ofAlongMap I R a ≫ ofAlongMap I R b := by
  letI := Along.category (p := p) (R := R) (I := I R)
  apply InducedCategory.hom_ext
  exact congrArg (fun f ↦ Functor.Fiber.fiberInclusion.map f)
    ((Along.toFiber p R (I R)).map_comp a b)

set_option backward.privateInPublic true in
/-- The fixed-base fibre comparison packages a filtration-indexed object over its base. -/
def ofAlong
    (p : F ⥤ ArtinianLocalAlgCat Λ k) [Functor.IsFibered.InGroupoids p.op]
    (I : ∀ R : CompleteLocalAlgCat Λ k, AdicIdealFiltration R)
    (R : CompleteLocalAlgCat Λ k) :
    -- Local instance justification (defeq pin): the fibre source is the explicit Along category.
    letI := Along.category (p := p) (R := R) (I := I R)
    Along p R (I R) ⥤ Functor.Fiber (Functor.completionAlong I p) R :=
  -- Local instance justification (defeq pin): construct the functor with the category fixed by its source type.
  letI := Along.category (p := p) (R := R) (I := I R)
  { obj ξ := ⟨of I R ξ, by simp [Functor.completionAlong_obj, of_base]⟩
    map a := ⟨ofAlongMap (p := p) I R a, ofAlongMap_lift (p := p) I R a⟩
    map_id := fun ξ ↦ by
      apply Functor.Fiber.hom_ext
      exact ofAlongMap_id (p := p) I R ξ
    map_comp := fun f g ↦ by
      apply Functor.Fiber.hom_ext
      exact ofAlongMap_comp (p := p) I R f g }

/-- The fixed-base fibre comparison sends an object to its packaged total object. -/
theorem ofAlong_obj (R : CompleteLocalAlgCat Λ k) (ξ : Along p R (I R)) :
    -- Local instance justification (defeq pin): the fibre object is formed in the explicit Along category.
    letI := Along.category (p := p) (R := R) (I := I R)
    Functor.Fiber.fiberInclusion.obj ((ofAlong p I R).obj ξ) = of I R ξ := rfl

/-- The fixed-base fibre comparison is an isomorphism of categories. -/
theorem ofAlong_isIso
    (p : F ⥤ ArtinianLocalAlgCat Λ k) [Functor.IsFibered.InGroupoids p.op]
    (I : ∀ R : CompleteLocalAlgCat Λ k, AdicIdealFiltration R)
    (R : CompleteLocalAlgCat Λ k) :
    -- Local instance justification (defeq pin): the strict-isomorphism property uses the explicit Along category.
    letI := Along.category (p := p) (R := R) (I := I R)
    (ofAlong p I R).IsIso := by
  letI := Along.category (p := p) (R := R) (I := I R)
  haveI := Along.toFiber_isEquivalence p R (I R)
  refine { faithful := ?_, full := ?_, bijective_obj := ?_ }
  · show (ofAlong p I R).Faithful
    constructor
    intro ξ η a b h
    apply (Along.toFiber p R (I R)).map_injective
    apply Functor.Fiber.hom_ext
    exact congrArg (fun f ↦ f.val.hom) h
  · show (ofAlong p I R).Full
    constructor
    intro ξ η a
    let a' : (Along.toFiber p R (I R)).obj ξ ⟶
        (Along.toFiber p R (I R)).obj η := ⟨a.val.hom, by
      have h : 𝟙 R = (Functor.completionAlong I p).map a.val :=
        @IsHomLift.eq_of_isHomLift _ _ _ _ (Functor.completionAlong I p)
          (of I R ξ) (of I R η) (𝟙 R) a.val a.property
      exact (congrArg
        (fun f : R ⟶ R ↦ (Functor.completion p).IsHomLift f a.val.hom) h).mpr
          (Functor.IsHomLift.map a.val.hom)⟩
    obtain ⟨b, hb⟩ := (Along.toFiber p R (I R)).map_surjective a'
    refine ⟨b, ?_⟩
    apply Functor.Fiber.hom_ext
    apply InducedCategory.hom_ext
    exact congrArg (fun f ↦ f.val) hb
  · change Function.Bijective (ofAlong p I R).obj
    constructor
    · show Function.Injective (ofAlong p I R).obj
      intro ξ η h
      have h' : (⟨R, ξ⟩ : Σ S, Along p S (I S)) = ⟨R, η⟩ :=
        congrArg Subtype.val h
      exact eq_of_heq (Sigma.mk.inj h').2
    · show Function.Surjective (ofAlong p I R).obj
      rintro ⟨⟨S, ξ⟩, h⟩
      change S = R at h
      subst S
      exact ⟨ξ, rfl⟩

/-- The comparison to ordinary completion, regarded as a based functor. -/
noncomputable def toCompletionBased
    (I : ∀ R : CompleteLocalAlgCat Λ k, AdicIdealFiltration R)
    (p : F ⥤ ArtinianLocalAlgCat Λ k) [Functor.IsFibered.InGroupoids p.op] :
    BasedCategory.ofFunctor (Functor.completionAlong I p) ⥤ᵇ
      BasedCategory.ofFunctor (Functor.completion p) where
  toFunctor := toCompletion I p
  w := rfl

/-- The underlying functor of the based completion comparison. -/
theorem toCompletionBased_toFunctor
    (I : ∀ R : CompleteLocalAlgCat Λ k, AdicIdealFiltration R)
    (p : F ⥤ ArtinianLocalAlgCat Λ k) [Functor.IsFibered.InGroupoids p.op] :
    (toCompletionBased I p).toFunctor = toCompletion I p := rfl

/-- The total comparison is an equivalence over the complete local base. -/
theorem toCompletion_isEquivalence
    (I : ∀ R : CompleteLocalAlgCat Λ k, AdicIdealFiltration R)
    (p : F ⥤ ArtinianLocalAlgCat Λ k) [Functor.IsFibered.InGroupoids p.op] :
    BasedFunctor.IsEquivalence (toCompletionBased I p) := sorry

end FormalObject.AlongOver

end
