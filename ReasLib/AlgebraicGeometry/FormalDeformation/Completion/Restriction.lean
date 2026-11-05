/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.FiberedCategory.Fiber
public import Mathlib.CategoryTheory.ConcreteCategory.EpiMono
public import ReasLib.CategoryTheory.Fibered.BasedCategory.Equivalence.Basic
public import ReasLib.AlgebraicGeometry.FormalDeformation.Completion
public import ReasLib.AlgebraicGeometry.FormalDeformation.Along
public import ReasLib.AlgebraicGeometry.FormalDeformation.FiltrationEquivalence
public import ReasLib.AlgebraicGeometry.FormalDeformation.TypesCompletion
public import ReasLib.AlgebraicGeometry.FormalDeformation.ArtinianLocal.Nilpotency
public import ReasLib.AlgebraicGeometry.FormalDeformation.Filtration.Artinian

/-!
# Restriction of the completion to `C_Λ` and the evaluation functor `can`

Objects of `FormalObject.Restrict p` are formal objects of `p` whose complete local
base is the image of an Artinian algebra. The functor `can` evaluates a formal object
at the nilpotency stage and transports along `truncationNilpotencyIso`. A quasi-inverse
`toRestrict` realises `F` as a full subcategory of formal objects via `embed`.
-/

@[expose] public section

open CategoryTheory IsLocalRing Opposite ArtinianLocalAlgCat
open scoped BasedFunctor

noncomputable section

set_option backward.privateInPublic true

universe u v

variable {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]
variable {F : Type v} [Category.{v} F]

namespace FormalObject

/-- The restriction of `hat F` to `C_Λ`: a formal object of `p` together with an Artinian
base identified with its complete local view. -/
structure RestrictStorage (p : F ⥤ ArtinianLocalAlgCat Λ k) where
  /-- Underlying formal object of `p`. -/
  formal : FormalObject p
  /-- Artinian base of the restricted object. -/
  base : ArtinianLocalAlgCat Λ k
  /-- The formal object lies over the complete-local view of `base`. -/
  over : formal.base = toComplete base

/-- A formal object with an identified Artinian base, regarded as a categorical object. -/
def Restrict (p : F ⥤ ArtinianLocalAlgCat Λ k) := RestrictStorage p

/-- A formal object with an identified Artinian base determines a completion-fibre object. -/
def RestrictStorage.toFiber {p : F ⥤ ArtinianLocalAlgCat Λ k}
    [Functor.IsFibered.InGroupoids p.op] (ξ : RestrictStorage p) :
    Functor.Fiber (Functor.completion p) (toComplete ξ.base) :=
  ⟨ξ.formal, ξ.over⟩

namespace Restrict

variable {p : F ⥤ ArtinianLocalAlgCat Λ k}

/-- Construct a restricted formal object from its formal object and Artinian base. -/
def mk (formal : FormalObject p) (base : ArtinianLocalAlgCat Λ k)
    (over : formal.base = toComplete base) : Restrict p :=
  RestrictStorage.mk formal base over

/-- The underlying formal object of a restricted object. -/
def formal (ξ : Restrict p) : FormalObject p := RestrictStorage.formal ξ

/-- The Artinian base of a restricted object. -/
def base (ξ : Restrict p) : ArtinianLocalAlgCat Λ k := RestrictStorage.base ξ

/-- The identification of the formal base with the included Artinian base. -/
def over (ξ : Restrict p) : ξ.formal.base = toComplete ξ.base := RestrictStorage.over ξ

/-- Package a completion fibre over `toComplete A` as an object of the restriction. -/
noncomputable def of [Functor.IsFibered.InGroupoids p.op] (A : ArtinianLocalAlgCat Λ k)
    (ξ : Functor.Fiber (Functor.completion p) (toComplete A)) : Restrict p where
  formal := ξ.1
  base := A
  over := ξ.2

/-- The formal object of a packaged fibre is the fibre representative. -/
theorem of_formal [Functor.IsFibered.InGroupoids p.op] (A : ArtinianLocalAlgCat Λ k)
    (ξ : Functor.Fiber (Functor.completion p) (toComplete A)) :
    (of A ξ).formal = ξ.1 := sorry

/-- The Artinian base of a packaged fibre is the supplied algebra. -/
theorem of_base [Functor.IsFibered.InGroupoids p.op] (A : ArtinianLocalAlgCat Λ k)
    (ξ : Functor.Fiber (Functor.completion p) (toComplete A)) :
    (of A ξ).base = A := sorry

/-- An object of the restriction is a formal object over `toComplete` of its Artinian base. -/
theorem spec (ξ : Restrict p) :
    ξ.formal.base = toComplete ξ.base := sorry

/-- A morphism of restricted formal objects is a morphism of formal objects together with an
Artinian base map compatible with inclusion into complete local algebras. -/
structure HomStorage (ξ η : Restrict p) where
  /-- Underlying morphism of formal objects. -/
  formal : ξ.formal ⟶ η.formal
  /-- Underlying morphism of Artinian bases. -/
  base : ξ.base ⟶ η.base
  /-- The complete-local view of `base` recovers the formal base map. -/
  over : inclusion.map base =
    eqToHom ξ.over.symm ≫ formal.base ≫ eqToHom η.over

/-- A compatible formal morphism and Artinian base map, regarded as a categorical morphism. -/
def Hom (ξ η : Restrict p) := HomStorage ξ η

/-- Construct a restricted morphism from its formal and base maps. -/
def Hom.of {ξ η : Restrict p} (formal : ξ.formal ⟶ η.formal)
    (base : ξ.base ⟶ η.base)
    (over : inclusion.map base = eqToHom ξ.over.symm ≫ formal.base ≫ eqToHom η.over) :
    Hom ξ η := HomStorage.mk formal base over

/-- The underlying formal morphism of a restricted morphism. -/
def Hom.formal {ξ η : Restrict p} (a : Hom ξ η) : ξ.formal ⟶ η.formal := HomStorage.formal a

/-- The Artinian base map of a restricted morphism. -/
def Hom.base {ξ η : Restrict p} (a : Hom ξ η) : ξ.base ⟶ η.base := HomStorage.base a

/-- The compatibility equation of a restricted morphism with inclusion of bases. -/
def Hom.over {ξ η : Restrict p} (a : Hom ξ η) :
    inclusion.map a.base = eqToHom ξ.over.symm ≫ a.formal.base ≫ eqToHom η.over := HomStorage.over a

/-- Identity formal and Artinian base maps satisfy the restriction compatibility equation. -/
private theorem Hom.id_over (ξ : Restrict p) :
    inclusion.map (𝟙 ξ.base) =
      eqToHom ξ.over.symm ≫ (𝟙 ξ.formal : FormalObject.Hom ξ.formal ξ.formal).base ≫
        eqToHom ξ.over := sorry

/-- Composites of compatible formal and Artinian maps satisfy restriction compatibility. -/
private theorem Hom.comp_over {ξ η ζ : Restrict p} (a : Hom ξ η) (b : Hom η ζ) :
    inclusion.map (a.base ≫ b.base) =
      eqToHom ξ.over.symm ≫ (a.formal ≫ b.formal).base ≫ eqToHom ζ.over := sorry

/-- Identity on the explicit data of a restricted morphism. -/
def HomStorage.id (ξ : Restrict p) : HomStorage ξ ξ :=
  ⟨𝟙 ξ.formal, 𝟙 ξ.base, Hom.id_over ξ⟩

/-- Composition of the explicit data of restricted morphisms. -/
def HomStorage.comp {ξ η ζ : Restrict p} (a : HomStorage ξ η) (b : HomStorage η ζ) :
    HomStorage ξ ζ :=
  ⟨a.formal ≫ b.formal, a.base ≫ b.base, Hom.comp_over a b⟩

/-- Identity morphism of a restricted formal object. -/
def Hom.id (ξ : Restrict p) : Hom ξ ξ := HomStorage.id ξ

/-- Composition of morphisms of restricted formal objects. -/
def Hom.comp {ξ η ζ : Restrict p} (a : Hom ξ η) (b : Hom η ζ) : Hom ξ ζ :=
  HomStorage.comp a b

/-- A restricted morphism is compatible with inclusion of Artinian bases. -/
theorem Hom.spec {ξ η : Restrict p} (a : Hom ξ η) :
    inclusion.map a.base =
      eqToHom ξ.over.symm ≫ a.formal.base ≫ eqToHom η.over := sorry

/-- Left identity for composition of restricted morphisms. -/
private theorem Hom.id_comp {ξ η : Restrict p} (a : Hom ξ η) :
    Hom.comp (Hom.id ξ) a = a := sorry

/-- Right identity for composition of restricted morphisms. -/
private theorem Hom.comp_id {ξ η : Restrict p} (a : Hom ξ η) :
    Hom.comp a (Hom.id η) = a := sorry

/-- Associativity of composition of restricted morphisms. -/
private theorem Hom.assoc {ξ η ζ ω : Restrict p}
    (a : Hom ξ η) (b : Hom η ζ) (c : Hom ζ ω) :
    Hom.comp (Hom.comp a b) c = Hom.comp a (Hom.comp b c) := sorry

/-- The category with compatible formal morphisms over included Artinian bases. -/
private def categoryData : Category.{max u v} (FormalObject.Restrict p) where
  Hom := FormalObject.Restrict.Hom
  id := FormalObject.Restrict.Hom.id
  comp f g := FormalObject.Restrict.Hom.comp f g
  id_comp := FormalObject.Restrict.Hom.id_comp
  comp_id := FormalObject.Restrict.Hom.comp_id
  assoc := FormalObject.Restrict.Hom.assoc

/-- The category of formal objects over included Artinian bases. -/
instance category : Category.{max u v} (Restrict p) := categoryData

/-- The Artinian base map of an identity restricted morphism is an identity. -/
private theorem projection_map_id (ξ : Restrict p) :
    (𝟙 ξ : ξ ⟶ ξ).base = 𝟙 ξ.base := sorry

/-- Artinian base maps preserve composition of restricted morphisms. -/
private theorem projection_map_comp {ξ η ζ : Restrict p} (a : ξ ⟶ η) (b : η ⟶ ζ) :
    (a ≫ b).base = a.base ≫ b.base := sorry

/-- The projection `hat F |_{C_Λ} ⥤ C_Λ` sending a restricted formal object to its Artinian base. -/
def projection (p : F ⥤ ArtinianLocalAlgCat Λ k) : Restrict p ⥤ ArtinianLocalAlgCat Λ k where
  obj ξ := ξ.base
  map a := a.base
  map_id := projection_map_id
  map_comp := projection_map_comp

/-- The projection sends a restricted formal object to its stored Artinian base. -/
theorem projection_obj (ξ : Restrict p) : (projection p).obj ξ = ξ.base := sorry

/-- The formal map of an identity restricted morphism is an identity. -/
private theorem ι_map_id (ξ : Restrict p) :
    (𝟙 ξ : ξ ⟶ ξ).formal = 𝟙 ξ.formal := sorry

/-- Formal maps preserve composition of restricted morphisms. -/
private theorem ι_map_comp {ξ η ζ : Restrict p} (a : ξ ⟶ η) (b : η ⟶ ζ) :
    (a ≫ b).formal = a.formal ≫ b.formal := sorry

/-- Inclusion of the restriction into the category of all formal objects of `p`. -/
def ι (p : F ⥤ ArtinianLocalAlgCat Λ k) : Restrict p ⥤ FormalObject p where
  obj ξ := ξ.formal
  map a := a.formal
  map_id := ι_map_id
  map_comp := ι_map_comp

/-- The inclusion sends a restricted object to its stored formal object. -/
theorem ι_obj (ξ : Restrict p) : (ι p).obj ξ = ξ.formal := sorry

/-- The inclusion of the restriction into formal objects is full. -/
instance ι.full : (ι p).Full := sorry

/-- The inclusion of the restriction into formal objects is faithful. -/
instance ι.faithful : (ι p).Faithful := sorry

/-- The restricted projection is cofibered in groupoids. -/
instance projection_op_isFiberedInGroupoids [Functor.IsFibered.InGroupoids p.op] :
    Functor.IsFibered.InGroupoids (projection p).op := sorry

end Restrict

variable {p : F ⥤ ArtinianLocalAlgCat Λ k} [Functor.IsFibered.InGroupoids p.op]

/-- Stage `n` of a restricted formal object lies over the corresponding truncation of its
Artinian base. -/
private def stageOver (ξ : Restrict p) (n : ℕ) :
    p.obj (ξ.formal.system.family n) = (toComplete ξ.base).truncation n :=
  (ξ.formal.over_obj n).trans (congrArg (fun R ↦ R.truncation n) ξ.over)

/-- Evaluation of a restricted formal object at its nilpotency stage, transported to the
Artinian base along `truncationNilpotencyIso`. -/
noncomputable def canObj (ξ : Restrict p) : F :=
  Along.pushforwardObj (stageOver ξ (nilpotencyIndex ξ.base))
    (truncationNilpotencyIso ξ.base).hom

/-- The cofibered pushforward from the nilpotency stage to `canObj`. -/
noncomputable def canPush (ξ : Restrict p) :
    ξ.formal.system.family (nilpotencyIndex ξ.base) ⟶ canObj ξ :=
  Along.pushforwardMap (stageOver ξ (nilpotencyIndex ξ.base))
    (truncationNilpotencyIso ξ.base).hom

/-- Evaluation at the nilpotency stage lies over the stored Artinian base. -/
private theorem canObj_over (ξ : Restrict p) : p.obj (canObj ξ) = ξ.base := by
  exact congrArg Opposite.unop (Functor.IsPreFibered.pullbackObj_proj
    (p := p.op) (ha := congrArg Opposite.op (stageOver ξ (nilpotencyIndex ξ.base)))
    (Quiver.Hom.op (truncationNilpotencyIso ξ.base).hom))

section

-- These explicit storage wrappers require full definitional equality when checking
-- the transported morphisms. This option only affects elaboration in this section.
set_option backward.isDefEq.respectTransparency false

/-- Forget the Artinian algebra structure while retaining the actual underlying ring maps. -/
private def artinianRingForget : ArtinianLocalAlgCat Λ k ⥤ CommRingCat.{u} where
  obj A := A.carrier
  map f := CommRingCat.ofHom (ArtinianLocalAlgCat.Hom.toRingHom f)
  map_id _ := rfl
  map_comp _ _ := rfl

/-- Forget the complete-local algebra structure while retaining the actual underlying ring maps. -/
private def completeRingForget : CompleteLocalAlgCat Λ k ⥤ CommRingCat.{u} where
  obj A := A.carrier
  map f := CommRingCat.ofHom (CompleteLocalAlgCat.Hom.toRingHom f)
  map_id _ := rfl
  map_comp _ _ := rfl

/-- The quotient map from the complete base to the actual base of a system stage. -/
private def stageQuotient (ξ : FormalObject p) (n : ℕ) :
    completeRingForget.obj ξ.base ⟶ artinianRingForget.obj (p.obj (ξ.system.family n)) :=
  CommRingCat.ofHom (Ideal.Quotient.mk (CompleteLocalAlgCat.maximalIdeal ξ.base ^ (n + 1))) ≫
    artinianRingForget.map (eqToHom (ξ.over_obj n).symm)

omit [Functor.IsFibered.InGroupoids p.op] in
/-- A successor transition commutes with the quotient maps from the complete base. -/
private theorem stageQuotient_step (ξ : FormalObject p) (n : ℕ) :
    stageQuotient ξ (n+1) ≫ artinianRingForget.map (p.map (ξ.system.stepMap n)) =
      stageQuotient ξ n := by
  letI := ξ.over_step n
  have hmap : eqToHom (ξ.over_obj (n+1)).symm ≫ p.map (ξ.system.stepMap n) ≫
      eqToHom (ξ.over_obj n) = ξ.base.truncationMap n :=
    (IsHomLift.fac p (ξ.base.truncationMap n) (ξ.system.stepMap n)).symm
  calc
    stageQuotient ξ (n+1) ≫ artinianRingForget.map (p.map (ξ.system.stepMap n)) =
        CommRingCat.ofHom (Ideal.Quotient.mk
            (CompleteLocalAlgCat.maximalIdeal ξ.base ^ (n + 1 + 1))) ≫
          artinianRingForget.map
            (eqToHom (ξ.over_obj (n+1)).symm ≫ p.map (ξ.system.stepMap n) ≫
              eqToHom (ξ.over_obj n)) ≫
          artinianRingForget.map (eqToHom (ξ.over_obj n).symm) := by
      simp [stageQuotient, Functor.map_comp, eqToHom_map, Category.assoc]
    _ = CommRingCat.ofHom (Ideal.Quotient.mk
            (CompleteLocalAlgCat.maximalIdeal ξ.base ^ (n + 1 + 1))) ≫
          artinianRingForget.map (ξ.base.truncationMap n) ≫
          artinianRingForget.map (eqToHom (ξ.over_obj n).symm) := by rw [hmap]
    _ = stageQuotient ξ n := by
      dsimp [stageQuotient]
      rw [← Category.assoc]
      congr 1

omit [Functor.IsFibered.InGroupoids p.op] in
/-- Every transition commutes with the quotient maps from the complete base. -/
private theorem stageQuotient_transition (ξ : FormalObject p) {i j : ℕ} (h : i ≤ j) :
    stageQuotient ξ j ≫ artinianRingForget.map (p.map (ξ.system.transitionMap h)) =
      stageQuotient ξ i := by
  induction j, h using Nat.le_induction with
  | base =>
    have hi : ξ.system.transitionMap (le_refl i) = 𝟙 (ξ.system.family i) :=
      ξ.system.map_id _
    simp only [hi, p.map_id, artinianRingForget.map_id, Category.comp_id]
  | succ j h ih =>
    have hfactor : ξ.system.transitionMap (Nat.le_succ_of_le h) =
        ξ.system.stepMap j ≫ ξ.system.transitionMap h := by
      rw [← ξ.system.map_comp]
      congr 1
    rw [hfactor, p.map_comp, artinianRingForget.map_comp, ← Category.assoc,
      stageQuotient_step, ih]

omit [Functor.IsFibered.InGroupoids p.op] in
/-- The quotient squares stored in a formal morphism commute before identifying stage bases. -/
private theorem stageQuotient_naturality {ξ η : FormalObject p} (a : ξ ⟶ η) (n : ℕ) :
    stageQuotient ξ n ≫ artinianRingForget.map (p.map (a.app n)) =
      completeRingForget.map a.base ≫ stageQuotient η n := by
  letI := a.over n
  have hmap : eqToHom (ξ.over_obj n).symm ≫ p.map (a.app n) ≫
      eqToHom (η.over_obj n) = a.baseTrunc n :=
    (IsHomLift.fac p (a.baseTrunc n) (a.app n)).symm
  calc
    stageQuotient ξ n ≫ artinianRingForget.map (p.map (a.app n)) =
        CommRingCat.ofHom (Ideal.Quotient.mk
            (CompleteLocalAlgCat.maximalIdeal ξ.base ^ (n + 1))) ≫
          artinianRingForget.map
            (eqToHom (ξ.over_obj n).symm ≫ p.map (a.app n) ≫
              eqToHom (η.over_obj n)) ≫
          artinianRingForget.map (eqToHom (η.over_obj n).symm) := by
      simp [stageQuotient, Functor.map_comp, eqToHom_map, Category.assoc]
    _ = CommRingCat.ofHom (Ideal.Quotient.mk
            (CompleteLocalAlgCat.maximalIdeal ξ.base ^ (n + 1))) ≫
          artinianRingForget.map (a.baseTrunc n) ≫
          artinianRingForget.map (eqToHom (η.over_obj n).symm) := by rw [hmap]
    _ = completeRingForget.map a.base ≫ stageQuotient η n := by
      rw [stageQuotient]
      simp only [← Category.assoc]
      apply congrArg (fun f => f ≫ artinianRingForget.map (eqToHom (η.over_obj n).symm))
      apply CommRingCat.hom_ext
      exact a.baseTrunc_spec n

omit [Functor.IsFibered.InGroupoids p.op] in
/-- An Artinian algebra morphism is determined by its underlying ring map. -/
private theorem artinianRingForget_injective {A B : ArtinianLocalAlgCat Λ k}
    {f g : A ⟶ B} (h : artinianRingForget.map f = artinianRingForget.map g) : f = g := by
  letI := A.algebra
  letI := B.algebra
  have h' : f.hom = g.hom := by
    apply AlgHom.ext
    intro x
    exact congrArg (fun q : A.carrier ⟶ B.carrier => q.hom x) h
  rcases f with ⟨f, hf, hfc⟩
  rcases g with ⟨g, hg, hgc⟩
  cases h'
  rfl

omit [Functor.IsFibered.InGroupoids p.op] in
/-- The transported quotient map to each stage is an epimorphism. -/
private theorem stageQuotient_epi (ξ : FormalObject p) (n : ℕ) :
    Epi (stageQuotient ξ n) := by
  change Epi (CommRingCat.ofHom (Ideal.Quotient.mk
      (CompleteLocalAlgCat.maximalIdeal ξ.base ^ (n + 1))) ≫
      artinianRingForget.map (eqToHom (ξ.over_obj n).symm))
  haveI : Epi (CommRingCat.ofHom (Ideal.Quotient.mk
      (CompleteLocalAlgCat.maximalIdeal ξ.base ^ (n + 1)))) :=
    ConcreteCategory.epi_of_surjective _ Ideal.Quotient.mk_surjective
  haveI : IsIso (artinianRingForget.map (eqToHom (ξ.over_obj n).symm)) := inferInstance
  infer_instance

omit [Functor.IsFibered.InGroupoids p.op] in
/-- At the nilpotency stage the quotient identification recovers the stored Artinian base. -/
private theorem nilStageQuotient (ξ : FormalObject.Restrict p) :
    stageQuotient ξ.formal (nilpotencyIndex ξ.base) ≫
      artinianRingForget.map (eqToHom (FormalObject.stageOver ξ (nilpotencyIndex ξ.base)) ≫
        (truncationNilpotencyIso ξ.base).hom) =
      completeRingForget.map (eqToHom ξ.over) := by
  rcases ξ with ⟨⟨R, s, ho, hs⟩, A, hR⟩
  change R = toComplete A at hR
  subst R
  change (CommRingCat.ofHom (Ideal.Quotient.mk
      (CompleteLocalAlgCat.maximalIdeal (toComplete A) ^ (nilpotencyIndex A + 1))) ≫
      artinianRingForget.map (eqToHom (ho (nilpotencyIndex A)).symm)) ≫
      artinianRingForget.map (eqToHom (ho (nilpotencyIndex A)) ≫
        (truncationNilpotencyIso A).hom) = completeRingForget.map (𝟙 (toComplete A))
  simp only [Functor.map_comp, eqToHom_map, Category.assoc,
    eqToHom_trans_assoc, eqToHom_refl, Category.id_comp, Functor.map_id]
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro x
  change truncationNilpotencyAlgEquiv A (Ideal.Quotient.mk _ x) = x
  rfl

omit [Functor.IsFibered.InGroupoids p.op] in
/-- A lift in the opposite category gives a lift in the original category. -/
private theorem unopLift {R S : (ArtinianLocalAlgCat Λ k)ᵒᵖ} {x y : Fᵒᵖ}
    {f : R ⟶ S} {φ : x ⟶ y} (h : p.op.IsHomLift f φ) :
    p.IsHomLift f.unop φ.unop := by
  cases h
  exact IsHomLift.map (p := p) _

/-- The evaluation pushforward lifts the actual nilpotency quotient isomorphism. -/
private theorem canPush_lift (ξ : FormalObject.Restrict p) :
    p.IsHomLift (truncationNilpotencyIso ξ.base).hom (FormalObject.canPush ξ) := by
  let φ := Functor.IsPreFibered.pullbackMap (p := p.op)
    (a := Opposite.op (ξ.formal.system.family (nilpotencyIndex ξ.base)))
    (ha := congrArg Opposite.op (FormalObject.stageOver ξ (nilpotencyIndex ξ.base)))
    (Quiver.Hom.op (truncationNilpotencyIso ξ.base).hom)
  have h : p.op.IsHomLift (truncationNilpotencyIso ξ.base).hom.op φ := inferInstance
  exact unopLift h

/-- Evaluation cancels the nilpotency-stage quotient map. -/
private theorem stageQuotient_canPush (ξ : FormalObject.Restrict p) :
    stageQuotient ξ.formal (nilpotencyIndex ξ.base) ≫
      artinianRingForget.map (p.map (FormalObject.canPush ξ)) =
      completeRingForget.map (eqToHom ξ.over) ≫
        artinianRingForget.map (eqToHom (FormalObject.canObj_over ξ).symm) := by
  letI := canPush_lift ξ
  have hmap : p.map (FormalObject.canPush ξ) =
      eqToHom (FormalObject.stageOver ξ (nilpotencyIndex ξ.base)) ≫
        (truncationNilpotencyIso ξ.base).hom ≫ eqToHom (FormalObject.canObj_over ξ).symm :=
    IsHomLift.fac' p (truncationNilpotencyIso ξ.base).hom (FormalObject.canPush ξ)
  rw [hmap, ← Category.assoc, artinianRingForget.map_comp, ← Category.assoc,
    nilStageQuotient]

omit [Functor.IsFibered.InGroupoids p.op] in
/-- The nilpotency quotient identity with the transport and quotient isomorphism separated. -/
private theorem nilStageQuotient_split (ξ : FormalObject.Restrict p) :
    (stageQuotient ξ.formal (nilpotencyIndex ξ.base) ≫
      artinianRingForget.map (eqToHom (FormalObject.stageOver ξ (nilpotencyIndex ξ.base)))) ≫
      artinianRingForget.map (truncationNilpotencyIso ξ.base).hom =
      completeRingForget.map (eqToHom ξ.over) := by
  simpa only [Functor.map_comp, ← Category.assoc] using nilStageQuotient ξ

omit [Functor.IsFibered.InGroupoids p.op] in
/-- The formal and Artinian base maps of a restricted morphism agree on underlying rings. -/
private theorem restricted_base_naturality {ξ η : FormalObject.Restrict p} (a : ξ ⟶ η) :
    completeRingForget.map a.formal.base ≫ completeRingForget.map (eqToHom η.over) =
      completeRingForget.map (eqToHom ξ.over) ≫ artinianRingForget.map a.base := by
  have hh : a.formal.base ≫ eqToHom η.over =
      eqToHom ξ.over ≫ inclusion.map a.base := by
    rw [a.over]
    simp [Category.assoc]
  have hf : completeRingForget.map (inclusion.map a.base) = artinianRingForget.map a.base := rfl
  simpa only [Functor.map_comp, hf] using congrArg completeRingForget.map hh

/-- The increasing-index factorization lies over its actual varying base map. -/
private theorem canAppAux_lift {ξ η : Restrict p} (a : ξ ⟶ η)
    (h : ¬ nilpotencyIndex η.base ≤ nilpotencyIndex ξ.base) :
    let m := nilpotencyIndex ξ.base
    let m' := nilpotencyIndex η.base
    let φ := Quiver.Hom.op (ξ.formal.system.transitionMap (le_of_not_ge h))
    let g := Quiver.Hom.op
      (eqToHom (stageOver ξ m) ≫ (truncationNilpotencyIso ξ.base).hom ≫ a.base ≫
        eqToHom (canObj_over η).symm)
    p.op.IsHomLift (g ≫ p.op.map φ) (Quiver.Hom.op (a.formal.app m' ≫ canPush η)) := by
  let m := nilpotencyIndex ξ.base
  let m' := nilpotencyIndex η.base
  let τ := ξ.formal.system.transitionMap (le_of_not_ge h)
  let b := eqToHom (FormalObject.stageOver ξ m) ≫ (truncationNilpotencyIso ξ.base).hom ≫
    a.base ≫ eqToHom (FormalObject.canObj_over η).symm
  have hbase : p.map (a.formal.app m' ≫ FormalObject.canPush η) = p.map τ ≫ b := by
    apply artinianRingForget_injective
    letI := stageQuotient_epi ξ.formal m'
    apply (cancel_epi (stageQuotient ξ.formal m')).mp
    dsimp only [τ]
    simp only [Functor.map_comp, ← Category.assoc]
    rw [stageQuotient_naturality, stageQuotient_transition]
    simp only [Category.assoc]
    rw [stageQuotient_canPush]
    dsimp only [b]
    simp only [Functor.map_comp, ← Category.assoc]
    rw [nilStageQuotient_split, restricted_base_naturality]
  have H : p.IsHomLift (p.map τ ≫ b) (a.formal.app m' ≫ FormalObject.canPush η) :=
    IsHomLift.of_fac' p _ _ rfl rfl (by simpa using hbase)
  exact FormalObject.Along.isHomLift_op H

end

/-- The stagewise map into the target evaluation is obtained by strongly cartesian factorization. -/
private noncomputable def canAppAux {ξ η : Restrict p} (a : ξ ⟶ η) :
    ξ.formal.system.family (nilpotencyIndex ξ.base) ⟶ canObj η :=
  let m := nilpotencyIndex ξ.base
  let m' := nilpotencyIndex η.base
  if h : m' ≤ m then
    a.formal.app m ≫ η.formal.system.transitionMap h ≫ canPush η
  else
    let φ := Quiver.Hom.op (ξ.formal.system.transitionMap (le_of_not_ge h))
    let f := p.op.map φ
    let g := Quiver.Hom.op
      (eqToHom (stageOver ξ m) ≫ (truncationNilpotencyIso ξ.base).hom ≫ a.base ≫
        eqToHom (canObj_over η).symm)
    Along.stronglyCartesianUnop (p := p) f φ g (g ≫ f) rfl
      (Quiver.Hom.op (a.formal.app m' ≫ canPush η)) inferInstance (canAppAux_lift a h)

/-- The evaluation pushforward is invertible because its base map is the
nilpotency-stage quotient isomorphism. -/
private theorem canPush_isIso (ξ : Restrict p) : IsIso (canPush ξ) := by
  let φ := Functor.IsPreFibered.pullbackMap (p := p.op)
    (a := Opposite.op (ξ.formal.system.family (nilpotencyIndex ξ.base)))
    (ha := congrArg Opposite.op (stageOver ξ (nilpotencyIndex ξ.base)))
    (Quiver.Hom.op (truncationNilpotencyIso ξ.base).hom)
  haveI : IsIso φ := Functor.IsStronglyCartesian.isIso_of_base_isIso
    (p := p.op) (f := Quiver.Hom.op (truncationNilpotencyIso ξ.base).hom) φ
  exact inferInstanceAs (IsIso φ.unop)

/-- The map of evaluations induced by a restricted formal morphism, obtained by
inverting the nilpotency-stage evaluation pushforward. -/
private noncomputable def canMap {ξ η : Restrict p} (a : ξ ⟶ η) : canObj ξ ⟶ canObj η :=
  letI := canPush_isIso ξ
  inv (canPush ξ) ≫ canAppAux a

/-- Evaluation of a morphism agrees with its stagewise map after the evaluation
pushforward from the source nilpotency stage. -/
private theorem canMap_fac {ξ η : Restrict p} (a : ξ ⟶ η) :
    canPush ξ ≫ canMap a = canAppAux a := by
  letI := canPush_isIso ξ
  simp [canMap, ← Category.assoc]

/-- Evaluation maps preserve identity morphisms. -/
private theorem can_map_id (ξ : Restrict p) : canMap (𝟙 ξ) = 𝟙 (canObj ξ) := sorry

/-- Evaluation maps preserve composition. -/
private theorem can_map_comp {ξ η ζ : Restrict p} (a : ξ ⟶ η) (b : η ⟶ ζ) :
    canMap (a ≫ b) = canMap a ≫ canMap b := sorry

/-- Evaluation of restricted formal objects at their nilpotency stages. -/
noncomputable def can (p : F ⥤ ArtinianLocalAlgCat Λ k)
    [Functor.IsFibered.InGroupoids p.op] : Restrict p ⥤ F where
  obj ξ := canObj ξ
  map a := canMap a
  map_id := can_map_id
  map_comp := can_map_comp

/-- `can` evaluates a restricted formal object at its nilpotency stage. -/
theorem can_obj (ξ : Restrict p) : (can p).obj ξ = canObj ξ := sorry

/-- Evaluation commutes strictly with the Artinian projection. -/
private theorem can_comp_projection : can p ⋙ p = Restrict.projection p := sorry

/-- The evaluation functor lies strictly over `C_Λ`. -/
noncomputable def basedCan (p : F ⥤ ArtinianLocalAlgCat Λ k)
    [Functor.IsFibered.InGroupoids p.op] :
    BasedCategory.ofFunctor (Restrict.projection p) ⥤ᵇ BasedCategory.ofFunctor p where
  toFunctor := can p
  w := can_comp_projection (p := p)

/-- The based evaluation functor lies over the identity of `C_Λ`. -/
theorem basedCan_w (p : F ⥤ ArtinianLocalAlgCat Λ k)
    [Functor.IsFibered.InGroupoids p.op] :
    (basedCan p).toFunctor ⋙ p = Restrict.projection p :=
  (basedCan p).w

/-- A completion-fibre morphism is compatible with the identity Artinian base map. -/
private theorem Restrict.ofHom_over {A : ArtinianLocalAlgCat Λ k}
    {ξ η : Functor.Fiber (Functor.completion p) (toComplete A)} (a : ξ ⟶ η) :
    inclusion.map (𝟙 A) = eqToHom (Restrict.of A ξ).over.symm ≫
      (a.1 : FormalObject.Hom ξ.1 η.1).base ≫ eqToHom (Restrict.of A η).over := sorry

/-- Package a completion-fibre morphism as a restricted morphism over the identity. -/
noncomputable def Restrict.ofHom {A : ArtinianLocalAlgCat Λ k}
    {ξ η : Functor.Fiber (Functor.completion p) (toComplete A)}
    (a : ξ ⟶ η) : Restrict.of A ξ ⟶ Restrict.of A η :=
  Restrict.Hom.of a.1 (𝟙 A) (Restrict.ofHom_over a)

/-- A fibre morphism evaluates to a morphism over the identity Artinian base map. -/
private theorem canFiber_map_over {A : ArtinianLocalAlgCat Λ k}
    {ξ η : Functor.Fiber (Functor.completion p) (toComplete A)} (a : ξ ⟶ η) :
    p.IsHomLift (𝟙 A) ((can p).map (Restrict.ofHom a)) := sorry

/-- The evaluated object in the fibre over the given Artinian algebra. -/
private noncomputable def canFiberObj {A : ArtinianLocalAlgCat Λ k}
    (ξ : Functor.Fiber (Functor.completion p) (toComplete A)) : Functor.Fiber p A :=
  ⟨(can p).obj (Restrict.of A ξ), canObj_over (Restrict.of A ξ)⟩

/-- The map of completion fibres induced by evaluation. -/
private noncomputable def canFiberMap {A : ArtinianLocalAlgCat Λ k}
    {ξ η : Functor.Fiber (Functor.completion p) (toComplete A)} (a : ξ ⟶ η) :
    canFiberObj ξ ⟶ canFiberObj η :=
  ⟨(can p).map (Restrict.ofHom a), canFiber_map_over a⟩

/-- Evaluation on a completion fibre preserves identities. -/
private theorem canFiber_map_id (A : ArtinianLocalAlgCat Λ k)
    (ξ : Functor.Fiber (Functor.completion p) (toComplete A)) :
    canFiberMap (𝟙 ξ) = 𝟙 _ := sorry

/-- Evaluation on a completion fibre preserves composition. -/
private theorem canFiber_map_comp {A : ArtinianLocalAlgCat Λ k}
    {ξ η ζ : Functor.Fiber (Functor.completion p) (toComplete A)}
    (a : ξ ⟶ η) (b : η ⟶ ζ) :
    canFiberMap (a ≫ b) = canFiberMap a ≫ canFiberMap b := sorry

/-- Evaluation of the actual completion fibre over an Artinian algebra. -/
noncomputable def canFiber (p : F ⥤ ArtinianLocalAlgCat Λ k)
    [Functor.IsFibered.InGroupoids p.op] (A : ArtinianLocalAlgCat Λ k) :
    Functor.Fiber (Functor.completion p) (toComplete A) ⥤ Functor.Fiber p A where
  obj ξ := canFiberObj ξ
  map a := canFiberMap a
  map_id := canFiber_map_id A
  map_comp := canFiber_map_comp

/-- Fibrewise evaluation sends a completion fibre to the evaluation of the packaged object. -/
theorem canFiber_obj (A : ArtinianLocalAlgCat Λ k)
    (ξ : Functor.Fiber (Functor.completion p) (toComplete A)) :
    Functor.Fiber.fiberInclusion.obj ((canFiber p A).obj ξ) =
      (can p).obj (Restrict.of A ξ) := sorry

/-- Nilpotency-stage evaluation is an equivalence on each Artinian fibre. -/
instance canFiber_isEquivalence (A : ArtinianLocalAlgCat Λ k) :
    (canFiber p A).IsEquivalence := sorry

/-- Evaluation is an equivalence of categories cofibered in groupoids over `C_Λ`. -/
instance basedCan_isEquivalence (p : F ⥤ ArtinianLocalAlgCat Λ k)
    [Functor.IsFibered.InGroupoids p.op] :
    BasedFunctor.IsEquivalence (basedCan p) := sorry

/-- The two quotient pushforwards satisfy the lift condition for the truncation transition. -/
private theorem embedStep_lift (x : F) (n : ℕ) :
  let A := p.obj x
  let φ := Functor.IsPreFibered.pullbackMap (p := p.op) (a := Opposite.op x)
    (ha := congrArg Opposite.op rfl) (Quiver.Hom.op (toTruncation A (n + 1)))
  let φ' := Functor.IsPreFibered.pullbackMap (p := p.op) (a := Opposite.op x)
    (ha := congrArg Opposite.op rfl) (Quiver.Hom.op (toTruncation A n))
  let g :=
    eqToHom (Functor.IsPreFibered.pullbackObj_proj (p := p.op) (a := Opposite.op x)
        (ha := congrArg Opposite.op rfl) (Quiver.Hom.op (toTruncation A n))) ≫
      Quiver.Hom.op ((toComplete A).truncationMap n)
  let f := Quiver.Hom.op (toTruncation A (n + 1))
  p.op.IsHomLift (g ≫ f) φ' := sorry

/-- The transition between the pushed successor truncations of an object. -/
private noncomputable def embedStep (x : F) (n : ℕ) :
    Along.pushforwardObj (rfl : p.obj x = p.obj x) (toTruncation (p.obj x) (n + 1)) ⟶
      Along.pushforwardObj (rfl : p.obj x = p.obj x) (toTruncation (p.obj x) n) :=
  let A := p.obj x
  let φ := Functor.IsPreFibered.pullbackMap (p := p.op) (a := Opposite.op x)
    (ha := congrArg Opposite.op rfl) (Quiver.Hom.op (toTruncation A (n + 1)))
  let φ' := Functor.IsPreFibered.pullbackMap (p := p.op) (a := Opposite.op x)
    (ha := congrArg Opposite.op rfl) (Quiver.Hom.op (toTruncation A n))
  let g :=
    eqToHom (Functor.IsPreFibered.pullbackObj_proj (p := p.op) (a := Opposite.op x)
        (ha := congrArg Opposite.op rfl) (Quiver.Hom.op (toTruncation A n))) ≫
      Quiver.Hom.op ((toComplete A).truncationMap n)
  let f := Quiver.Hom.op (toTruncation A (n + 1))
  Along.stronglyCartesianUnop (p := p) f φ g (g ≫ f) rfl φ' inferInstance
    (embedStep_lift x n)

/-- A morphism and its quotient pushforwards satisfy the stagewise lift condition. -/
private theorem toRestrictApp_lift {x y : F} (f : x ⟶ y) (n : ℕ) :
  let φ := Functor.IsPreFibered.pullbackMap (p := p.op) (a := Opposite.op x)
    (ha := congrArg Opposite.op rfl) (Quiver.Hom.op (toTruncation (p.obj x) n))
  let φ' :=
    Functor.IsPreFibered.pullbackMap (p := p.op) (a := Opposite.op y)
      (ha := congrArg Opposite.op rfl) (Quiver.Hom.op (toTruncation (p.obj y) n)) ≫
      Quiver.Hom.op f
  let fst := Quiver.Hom.op (toTruncation (p.obj x) n)
  let g := Quiver.Hom.op (CompleteLocalAlgCat.truncationHom (inclusion.map (p.map f)) n)
  p.op.IsHomLift (g ≫ fst) φ' := sorry

/-- The map between pushed truncations induced by a morphism. -/
private noncomputable def toRestrictApp {x y : F} (f : x ⟶ y) (n : ℕ) :
    Along.pushforwardObj (rfl : p.obj x = p.obj x) (toTruncation (p.obj x) n) ⟶
      Along.pushforwardObj (rfl : p.obj y = p.obj y) (toTruncation (p.obj y) n) :=
  let φ := Functor.IsPreFibered.pullbackMap (p := p.op) (a := Opposite.op x)
    (ha := congrArg Opposite.op rfl) (Quiver.Hom.op (toTruncation (p.obj x) n))
  let φ' :=
    Functor.IsPreFibered.pullbackMap (p := p.op) (a := Opposite.op y)
      (ha := congrArg Opposite.op rfl) (Quiver.Hom.op (toTruncation (p.obj y) n)) ≫
      Quiver.Hom.op f
  let fst := Quiver.Hom.op (toTruncation (p.obj x) n)
  let g := Quiver.Hom.op (CompleteLocalAlgCat.truncationHom (inclusion.map (p.map f)) n)
  Along.stronglyCartesianUnop (p := p) fst φ g (g ≫ fst) rfl φ' inferInstance
    (toRestrictApp_lift f n)

/-- Pushing an object along a quotient places it over that truncation. -/
private theorem toRestrictFormal_over_obj (x : F) (n : ℕ) :
    p.obj (Along.pushforwardObj (rfl : p.obj x = p.obj x) (toTruncation (p.obj x) n)) =
      (toComplete (p.obj x)).truncation n := sorry

/-- The pushed successor transitions lie over the truncation maps. -/
private theorem toRestrictFormal_over_step (x : F) (n : ℕ) :
    p.IsHomLift ((toComplete (p.obj x)).truncationMap n) (embedStep (p := p) x n) := sorry

/-- The formal object obtained by pushing an object to all truncations of its base. -/
private noncomputable def toRestrictFormal (x : F) : FormalObject p :=
  FormalObject.of (toComplete (p.obj x))
    (fun n ↦ Along.pushforwardObj (rfl : p.obj x = p.obj x) (toTruncation (p.obj x) n))
    (fun n ↦ embedStep (p := p) x n) (toRestrictFormal_over_obj x) (toRestrictFormal_over_step x)

/-- Pushed stage maps lie over the induced truncation maps. -/
private theorem toRestrictMap_over {x y : F} (f : x ⟶ y) (n : ℕ) :
    p.IsHomLift (CompleteLocalAlgCat.truncationHom (inclusion.map (p.map f)) n)
      (toRestrictApp (p := p) f n) := sorry

/-- The induced truncation maps commute with the quotient maps. -/
private theorem toRestrictMap_baseTrunc_spec {x y : F} (f : x ⟶ y) (n : ℕ) :
    (ArtinianLocalAlgCat.Hom.toRingHom
        (CompleteLocalAlgCat.truncationHom (inclusion.map (p.map f)) n)).comp
      (Ideal.Quotient.mk (CompleteLocalAlgCat.maximalIdeal (toComplete (p.obj x)) ^ (n + 1))) =
    (Ideal.Quotient.mk (CompleteLocalAlgCat.maximalIdeal (toComplete (p.obj y)) ^ (n + 1))).comp
      (CompleteLocalAlgCat.Hom.toRingHom (inclusion.map (p.map f))) := sorry

/-- Pushed stage maps commute with successor transitions. -/
private theorem toRestrictMap_naturality {x y : F} (f : x ⟶ y) (n : ℕ) :
    (toRestrictFormal (p := p) x).system.stepMap n ≫ toRestrictApp (p := p) f n =
      toRestrictApp (p := p) f (n + 1) ≫ (toRestrictFormal (p := p) y).system.stepMap n := sorry

/-- The formal-object morphism induced by pushing a morphism to every truncation. -/
private noncomputable def toRestrictFormalMap {x y : F} (f : x ⟶ y) :
    toRestrictFormal (p := p) x ⟶ toRestrictFormal (p := p) y :=
  FormalObject.Hom.of (inclusion.map (p.map f))
    (fun n ↦ toRestrictApp (p := p) f n)
    (fun n ↦ CompleteLocalAlgCat.truncationHom (inclusion.map (p.map f)) n)
    (toRestrictMap_over f) (toRestrictMap_baseTrunc_spec f) (toRestrictMap_naturality f)

/-- The formal map of truncation systems lies over the included Artinian base map. -/
private theorem toRestrictMap_base_over {x y : F} (f : x ⟶ y) :
    inclusion.map (p.map f) =
      eqToHom (rfl : (toRestrictFormal (p := p) x).base = toComplete (p.obj x)).symm ≫
        (toRestrictFormalMap (p := p) f).base ≫
          eqToHom (rfl : (toRestrictFormal (p := p) y).base = toComplete (p.obj y)) := sorry

/-- An object determines a restricted formal object by its quotient pushforwards. -/
private noncomputable def toRestrictObj (x : F) : Restrict p :=
  Restrict.mk (toRestrictFormal (p := p) x) (p.obj x) rfl

/-- A morphism determines a restricted morphism of quotient pushforward systems. -/
private noncomputable def toRestrictMap {x y : F} (f : x ⟶ y) :
    toRestrictObj (p := p) x ⟶ toRestrictObj (p := p) y :=
  Restrict.Hom.of (toRestrictFormalMap (p := p) f) (p.map f) (toRestrictMap_base_over f)

/-- The truncation-system construction preserves identities. -/
private theorem toRestrict_map_id (x : F) : toRestrictMap (p := p) (𝟙 x) = 𝟙 (toRestrictObj (p := p) x) := sorry

/-- The truncation-system construction preserves composition. -/
private theorem toRestrict_map_comp {x y z : F} (f : x ⟶ y) (g : y ⟶ z) :
    toRestrictMap (p := p) (f ≫ g) = toRestrictMap (p := p) f ≫ toRestrictMap g := sorry

/-- The functor of quotient pushforward systems over Artinian bases. -/
noncomputable def toRestrict (p : F ⥤ ArtinianLocalAlgCat Λ k)
    [Functor.IsFibered.InGroupoids p.op] : F ⥤ Restrict p where
  obj x := toRestrictObj (p := p) x
  map f := toRestrictMap (p := p) f
  map_id := toRestrict_map_id (p := p)
  map_comp := toRestrict_map_comp (p := p)

/-- The fixed quotient-pushforward functor is a quasi-inverse to evaluation. -/
theorem toRestrict_isQuasiInverse :
    Nonempty (𝟭 (Restrict p) ≅ can p ⋙ toRestrict p) ∧
      Nonempty (toRestrict p ⋙ can p ≅ 𝟭 F) := sorry

/-- Inclusion of `F` into formal objects of `p` as the composite of the quasi-inverse
with the restriction inclusion. -/
noncomputable def embed (p : F ⥤ ArtinianLocalAlgCat Λ k)
    [Functor.IsFibered.InGroupoids p.op] : F ⥤ FormalObject p :=
  toRestrict p ⋙ Restrict.ι p

/-- The complete local base of an embedded object is the complete-local view of `p.obj x`. -/
theorem embed_base (x : F) : ((embed p).obj x).base = toComplete (p.obj x) := sorry

/-- The embedding of `F` into formal objects is full. -/
instance embed.full : (embed p).Full := sorry

/-- The embedding of `F` into formal objects is faithful. -/
instance embed.faithful : (embed p).Faithful := sorry

end FormalObject

end
