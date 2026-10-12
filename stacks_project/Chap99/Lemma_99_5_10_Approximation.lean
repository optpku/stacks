/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.FiberedCategory.Fibered
public import stacks_project.Chap98.«98_9_3_1_Approximation»
public import stacks_project.Chap99.Lemma_99_5_2

/-!
# Artin approximation for `Coh_{X/B}`

Restriction along `Spec(R ⧸ m^{n+1}) ⟶ Spec(R)` sends an object of `CohStack f`
over a complete local finite-type-residue spectrum to a formal object. Hom-types
of `Obj f` live in `Type (u + 1)`, so this cannot reuse `GroupoidsOver.approximation`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open Functor IsLocalRing

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.CohStack

variable {S : Scheme.{u}} [AlgebraicGeometry.IsLocallyNoetherian S] {X B : AlgebraicSpace S}

/-- An object of `CohStack f` lying over `Spec(R)` for a Noetherian complete local
`S`-algebra `R` with residue field of finite type over `S`. -/
structure CompleteLocalObject (f : X ⟶ B) [FinitePresentation f] where
  /-- Complete local `S`-algebra underlying the object. -/
  base : CompleteLocalSAlgebra S
  /-- Underlying object of `Obj f`. -/
  object : Obj f
  /-- The object lies over `Spec(R) ⟶ S`. -/
  over_obj : (p f).obj object = Over.mk base.toS

namespace CompleteLocalObject

variable {f : X ⟶ B} [FinitePresentation f]

/-- Package an object of `CohStack f` over a complete local finite-type-residue
spectrum. -/
def of (base : CompleteLocalSAlgebra S) (object : Obj f)
    (over_obj : (p f).obj object = Over.mk base.toS) : CompleteLocalObject f where
  base := base
  object := object
  over_obj := over_obj

/-- An object of the source of approximation lies over its stored complete local
spectrum. -/
theorem spec (x : CompleteLocalObject f) :
    (p f).obj x.object = Over.mk x.base.toS :=
  sorry

/-- Underlying morphism of spectra induced by a morphism of complete local
objects. -/
def schemeHom {x y : CompleteLocalObject f} (φ : x.object ⟶ y.object) :
    Spec (CommRingCat.of x.base.carrier) ⟶ Spec (CommRingCat.of y.base.carrier) :=
  eqToHom (congrArg Over.left x.over_obj).symm ≫ ((p f).map φ).left ≫
    eqToHom (congrArg Over.left y.over_obj)

/-- Ring homomorphism associated to a morphism of complete local objects. -/
def ringHom {x y : CompleteLocalObject f} (φ : x.object ⟶ y.object) :
    y.base.carrier →+* x.base.carrier :=
  CommRingCat.Hom.hom <|
    (Scheme.ΓSpecIso (CommRingCat.of y.base.carrier)).inv ≫ (schemeHom φ).appTop ≫
      (Scheme.ΓSpecIso (CommRingCat.of x.base.carrier)).hom

/-- The induced ring map of a morphism of complete local objects is local. -/
theorem ringHom_isLocalHom {x y : CompleteLocalObject f} (φ : x.object ⟶ y.object) :
    IsLocalHom (ringHom φ) :=
  sorry

/-- The spectrum of the induced ring map lies over `S`. -/
theorem ringHom_over_S {x y : CompleteLocalObject f} (φ : x.object ⟶ y.object) :
    Spec.map (CommRingCat.ofHom (ringHom φ)) ≫ y.base.toS = x.base.toS :=
  sorry

/-- Induced morphism of complete local `S`-algebras of a morphism of complete
local objects. Locality and compatibility with `S` are proof obligations, not
extra restrictions of the full subcategory. -/
def baseHom {x y : CompleteLocalObject f} (φ : x.object ⟶ y.object) :
    CompleteLocalSAlgebra.Hom x.base y.base where
  hom := ringHom φ
  isLocalHom := ringHom_isLocalHom φ
  over_S := ringHom_over_S φ

/-- `baseHom` recovers the extracted ring homomorphism. -/
theorem baseHom_hom {x y : CompleteLocalObject f} (φ : x.object ⟶ y.object) :
    (baseHom φ).hom = ringHom φ :=
  sorry

/-- Underlying morphism in `Over S` induced by a morphism of complete local
objects. -/
def overHom {x y : CompleteLocalObject f} (φ : x.object ⟶ y.object) :
    Over.mk x.base.toS ⟶ Over.mk y.base.toS :=
  eqToHom x.over_obj.symm ≫ (p f).map φ ≫ eqToHom y.over_obj

/-- A morphism of complete local objects lies over `overHom`. -/
instance overHom_isHomLift {x y : CompleteLocalObject f} (φ : x.object ⟶ y.object) :
    (p f).IsHomLift (overHom φ) φ :=
  IsHomLift.of_fac (p f) (overHom φ) φ x.over_obj y.over_obj rfl

/-- Identity morphism of a complete local object. -/
def Hom.id (x : CompleteLocalObject f) : x.object ⟶ x.object := 𝟙 x.object

/-- Composition of morphisms of complete local objects. -/
def Hom.comp {x y z : CompleteLocalObject f} (φ : x.object ⟶ y.object)
    (ψ : y.object ⟶ z.object) : x.object ⟶ z.object :=
  φ ≫ ψ

/-- The full subcategory of complete local objects of `CohStack f`. Morphisms are
all morphisms of `Obj f`. -/
instance category : Category.{u + 1} (CompleteLocalObject f) where
  Hom x y := x.object ⟶ y.object
  id := Hom.id
  comp φ ψ := Hom.comp φ ψ
  id_comp := sorry
  comp_id := sorry
  assoc := sorry

end CompleteLocalObject

/-- A formal object of `CohStack f` is a complete local `S`-algebra `R` together
with objects over `Spec(R ⧸ m^{n+1})` and transition morphisms over
`Spec(R ⧸ m^{n+1}) ⟶ Spec(R ⧸ m^{n+2})`. Lean stage `n` is the source object
`ξ_{n+1}`. -/
structure FormalObject (f : X ⟶ B) [FinitePresentation f] where
  /-- Complete local `S`-algebra underlying the formal object. -/
  base : CompleteLocalSAlgebra S
  /-- Stage `n` is the source object `ξ_{n+1}` over `Spec(R ⧸ m^{n+1})`. -/
  objects : ℕ → Obj f
  /-- Transition `ξ_{n+1} ⟶ ξ_{n+2}` over `Spec(R ⧸ m^{n+1}) ⟶ Spec(R ⧸ m^{n+2})`. -/
  step : ∀ n, objects n ⟶ objects (n + 1)
  /-- Stage `n` lies over `Spec(R ⧸ m^{n+1}) ⟶ S`. -/
  over_obj : ∀ n, (p f).obj (objects n) = base.stageOver n
  /-- The successor morphism lies over the truncation thickening in `Over S`. -/
  over_step : ∀ n, (p f).IsHomLift (base.stageHom n) (step n)

namespace FormalObject

variable {f : X ⟶ B} [FinitePresentation f]

/-- Package a complete local `S`-algebra and a compatible forward system as a
formal object of `CohStack f`. -/
def of (base : CompleteLocalSAlgebra S) (objects : ℕ → Obj f)
    (step : ∀ n, objects n ⟶ objects (n + 1))
    (over_obj : ∀ n, (p f).obj (objects n) = base.stageOver n)
    (over_step : ∀ n, (p f).IsHomLift (base.stageHom n) (step n)) :
    FormalObject f where
  base := base
  objects := objects
  step := step
  over_obj := over_obj
  over_step := over_step

/-- The packaged formal object recovers the supplied complete local `S`-algebra. -/
theorem of_base (base : CompleteLocalSAlgebra S) (objects : ℕ → Obj f)
    (step : ∀ n, objects n ⟶ objects (n + 1))
    (over_obj : ∀ n, (p f).obj (objects n) = base.stageOver n)
    (over_step : ∀ n, (p f).IsHomLift (base.stageHom n) (step n)) :
    (of base objects step over_obj over_step).base = base := sorry

/-- Stagewise specification of a formal object over the truncations of its base. -/
theorem spec (ξ : FormalObject f) (n : ℕ) :
    (p f).obj (ξ.objects n) = ξ.base.stageOver n ∧
      (p f).IsHomLift (ξ.base.stageHom n) (ξ.step n) := sorry

/-- The stagewise over-object and over-step conditions are equivalent to the
bundled pair of universal conditions. -/
theorem spec_iff (ξ : FormalObject f) :
    (∀ n, (p f).obj (ξ.objects n) = ξ.base.stageOver n ∧
        (p f).IsHomLift (ξ.base.stageHom n) (ξ.step n)) ↔
      ((∀ n, (p f).obj (ξ.objects n) = ξ.base.stageOver n) ∧
        ∀ n, (p f).IsHomLift (ξ.base.stageHom n) (ξ.step n)) := sorry

/-- A morphism of formal objects is a natural family `a_n : ξ_n ⟶ η_n` lying
over the truncated spectra of a morphism of complete local `S`-algebras. -/
structure Hom (ξ η : FormalObject f) where
  /-- Stagewise morphisms `a_n : ξ_n ⟶ η_n` of the forward systems. -/
  app : ∀ n, ξ.objects n ⟶ η.objects n
  /-- Induced morphism of complete local `S`-algebras, giving `a0`. -/
  base : CompleteLocalSAlgebra.Hom ξ.base η.base
  /-- Each `a_n` lies over the truncated map `Spec(R ⧸ m^{n+1}) ⟶ Spec(T ⧸ m^{n+1})`. -/
  over : ∀ n, (p f).IsHomLift (base.stageMap n) (app n)
  /-- The family `(a_n)` intertwines successor transitions. -/
  naturality : ∀ n, ξ.step n ≫ app (n + 1) = app n ≫ η.step n

/-- Package a natural family over a morphism of complete local `S`-algebras as
a morphism of formal objects. -/
def Hom.of {ξ η : FormalObject f} (app : ∀ n, ξ.objects n ⟶ η.objects n)
    (base : CompleteLocalSAlgebra.Hom ξ.base η.base)
    (over : ∀ n, (p f).IsHomLift (base.stageMap n) (app n))
    (naturality : ∀ n, ξ.step n ≫ app (n + 1) = app n ≫ η.step n) :
    Hom ξ η where
  app := app
  base := base
  over := over
  naturality := naturality

/-- Identity morphism of a formal object. -/
def Hom.id (ξ : FormalObject f) : Hom ξ ξ where
  app := fun n ↦ 𝟙 (ξ.objects n)
  base := CompleteLocalSAlgebra.Hom.id ξ.base
  over := sorry
  naturality := sorry

/-- Composition of morphisms of formal objects, covariant on stage maps and on
the induced spectra. -/
def Hom.comp {ξ η ζ : FormalObject f} (a : Hom ξ η) (b : Hom η ζ) : Hom ξ ζ where
  app := fun n ↦ a.app n ≫ b.app n
  base := CompleteLocalSAlgebra.Hom.comp a.base b.base
  over := sorry
  naturality := sorry

/-- A morphism of formal objects lies over its truncated base maps and commutes
with successor transitions. -/
theorem Hom.spec {ξ η : FormalObject f} (a : Hom ξ η) (n : ℕ) :
    (p f).IsHomLift (a.base.stageMap n) (a.app n) ∧
      ξ.step n ≫ a.app (n + 1) = a.app n ≫ η.step n := sorry

/-- The induced scheme morphism `a0 : Spec(R) ⟶ Spec(T)`. -/
def Hom.overMorphism {ξ η : FormalObject f} (a : Hom ξ η) :
    Spec (CommRingCat.of ξ.base.carrier) ⟶ Spec (CommRingCat.of η.base.carrier) :=
  a.base.toSpec

/-- `overMorphism` is the spectrum of the stored base homomorphism. -/
theorem Hom.overMorphism_eq {ξ η : FormalObject f} (a : Hom ξ η) :
    a.overMorphism = a.base.toSpec := sorry

/-- Category of formal objects of `CohStack f`, with morphisms the natural
families over a morphism of complete local `S`-algebras. -/
instance category : Category.{u + 1} (FormalObject f) where
  Hom := Hom
  id := Hom.id
  comp a b := Hom.comp a b
  id_comp := sorry
  comp_id := sorry
  assoc := sorry

/-- Unique factorization of a lift through a strongly cartesian arrow. -/
def factorCartesian {U V W : Over S} {x y z : Obj f} (g : V ⟶ U) (φ : y ⟶ x)
    (hφ : (p f).IsStronglyCartesian g φ) {h : W ⟶ V} {g' : W ⟶ U} (hg' : g' = h ≫ g)
    (φ' : z ⟶ x) (hφ' : (p f).IsHomLift g' φ') : z ⟶ y :=
  @IsStronglyCartesian.map _ _ _ _ (p f) _ _ _ _ g φ hφ _ _ h g' hg' φ' hφ'

/-- The comparison `factorCartesian` lies over the first factor of the base. -/
instance factorCartesian_isHomLift {U V W : Over S} {x y z : Obj f} (g : V ⟶ U)
    (φ : y ⟶ x) (hφ : (p f).IsStronglyCartesian g φ) {h : W ⟶ V} {g' : W ⟶ U}
    (hg' : g' = h ≫ g) (φ' : z ⟶ x) (hφ' : (p f).IsHomLift g' φ') :
    (p f).IsHomLift h (factorCartesian g φ hφ hg' φ' hφ') :=
  @IsStronglyCartesian.map_isHomLift _ _ _ _ (p f) _ _ _ _ g φ hφ _ _ h g' hg' φ' hφ'

/-- Restriction of an object along `Spec(R ⧸ m^{n+1}) ⟶ Spec(R)`. -/
def restrictionObj (x : CompleteLocalObject f) (n : ℕ) : Obj f :=
  IsPreFibered.pullbackObj x.over_obj (x.base.truncationOverHom n)

/-- Cartesian lift of restriction along `Spec(R ⧸ m^{n+1}) ⟶ Spec(R)`. -/
def restrictionHom (x : CompleteLocalObject f) (n : ℕ) :
    restrictionObj x n ⟶ x.object :=
  IsPreFibered.pullbackMap x.over_obj (x.base.truncationOverHom n)

/-- Restriction of `x` to stage `n` is cartesian over `truncationOverHom`. -/
instance restrictionHom_isCartesian (x : CompleteLocalObject f) (n : ℕ) :
    (p f).IsCartesian (x.base.truncationOverHom n) (restrictionHom x n) :=
  IsPreFibered.pullbackMap.IsCartesian x.over_obj (x.base.truncationOverHom n)

/-- Restriction of `x` to stage `n` is strongly cartesian. -/
instance restrictionHom_isStronglyCartesian (x : CompleteLocalObject f) (n : ℕ) :
    (p f).IsStronglyCartesian (x.base.truncationOverHom n) (restrictionHom x n) :=
  IsFibered.isStronglyCartesian_of_isCartesian (p f) (x.base.truncationOverHom n)
    (restrictionHom x n)

/-- Stage `n` of the restricted system lies over `Spec(R ⧸ m^{n+1})`. -/
theorem restrictionObj_over (x : CompleteLocalObject f) (n : ℕ) :
    (p f).obj (restrictionObj x n) = x.base.stageOver n :=
  sorry

/-- Successor map of restrictions, obtained from transitivity of pullback along
`Spec(R ⧸ m^{n+1}) ⟶ Spec(R ⧸ m^{n+2}) ⟶ Spec(R)`. -/
def restrictionStep (x : CompleteLocalObject f) (n : ℕ) :
    restrictionObj x n ⟶ restrictionObj x (n + 1) :=
  factorCartesian (x.base.truncationOverHom (n + 1)) (restrictionHom x (n + 1))
    (restrictionHom_isStronglyCartesian x (n + 1)) (x.base.truncationOverHom_comp n)
    (restrictionHom x n) (restrictionHom_isCartesian x n).toIsHomLift

/-- Successor maps of restrictions lift the truncated thickenings. -/
instance restrictionStep_isHomLift (x : CompleteLocalObject f) (n : ℕ) :
    (p f).IsHomLift (x.base.stageHom n) (restrictionStep x n) :=
  factorCartesian_isHomLift (x.base.truncationOverHom (n + 1))
    (restrictionHom x (n + 1)) (restrictionHom_isStronglyCartesian x (n + 1))
    (x.base.truncationOverHom_comp n) (restrictionHom x n)
    (restrictionHom_isCartesian x n).toIsHomLift

/-- Formal object obtained by restricting `x` along all truncations
`Spec(R ⧸ m^{n+1}) ⟶ Spec(R)`. -/
def restriction (x : CompleteLocalObject f) : FormalObject f :=
  of x.base (restrictionObj x) (restrictionStep x)
    (fun n ↦ IsPreFibered.pullbackObj_proj x.over_obj (x.base.truncationOverHom n))
    (restrictionStep_isHomLift x)

/-- Stage objects of `restriction x` are the chosen cartesian restrictions. -/
theorem restriction_family (x : CompleteLocalObject f) (n : ℕ) :
    (restriction x).objects n = restrictionObj x n :=
  sorry

/-- Successor maps of `restriction x` are the transitivity comparisons. -/
theorem restriction_step (x : CompleteLocalObject f) (n : ℕ) :
    (restriction x).step n = restrictionStep x n :=
  sorry

/-- Restriction of `x` followed by `φ` lies over the composite truncated base
morphism. -/
theorem approximation_factor {x y : CompleteLocalObject f} (φ : x.object ⟶ y.object)
    (n : ℕ) :
    x.base.truncationOverHom n ≫ CompleteLocalObject.overHom φ =
      (CompleteLocalObject.baseHom φ).stageMap n ≫ y.base.truncationOverHom n :=
  sorry

/-- The composite `restrictionHom x n ≫ φ` lifts the composite truncated base
morphism. -/
instance approximationApp_isHomLift {x y : CompleteLocalObject f}
    (φ : x.object ⟶ y.object) (n : ℕ) :
    (p f).IsHomLift (x.base.truncationOverHom n ≫ CompleteLocalObject.overHom φ)
      (restrictionHom x n ≫ φ) :=
  IsHomLift.comp (p f) (x.base.truncationOverHom n) (CompleteLocalObject.overHom φ)
    (restrictionHom x n) φ

/-- Stagewise restriction of a morphism of complete local objects. -/
def approximationApp {x y : CompleteLocalObject f} (φ : x.object ⟶ y.object)
    (n : ℕ) : restrictionObj x n ⟶ restrictionObj y n :=
  factorCartesian (y.base.truncationOverHom n) (restrictionHom y n)
    (restrictionHom_isStronglyCartesian y n) (approximation_factor φ n)
    (restrictionHom x n ≫ φ) (approximationApp_isHomLift φ n)

/-- Stage maps of approximation lie over the truncated maps of `baseHom`. -/
instance approximationApp_over {x y : CompleteLocalObject f} (φ : x.object ⟶ y.object)
    (n : ℕ) :
    (p f).IsHomLift ((CompleteLocalObject.baseHom φ).stageMap n) (approximationApp φ n) :=
  factorCartesian_isHomLift (y.base.truncationOverHom n) (restrictionHom y n)
    (restrictionHom_isStronglyCartesian y n) (approximation_factor φ n)
    (restrictionHom x n ≫ φ) (approximationApp_isHomLift φ n)

end FormalObject

/-- The approximation functor sending an object of `CohStack f` over `Spec(R)` to
the formal object of its restrictions along `Spec(R ⧸ m^{n+1}) ⟶ Spec(R)`. Lean
stage `n` is the source object `ξ_{n+1}` over `Spec(R ⧸ m^{n+1})`. -/
def approximation (f : X ⟶ B) [FinitePresentation f] :
    CompleteLocalObject f ⥤ FormalObject f where
  obj := FormalObject.restriction
  map φ := FormalObject.Hom.of (FormalObject.approximationApp φ)
      (CompleteLocalObject.baseHom φ) (FormalObject.approximationApp_over φ)
      (fun _ ↦ sorry)
  map_id := sorry
  map_comp := sorry

/-- The object map of approximation is restriction along truncations. -/
theorem approximation_obj {f : X ⟶ B} [FinitePresentation f]
    (x : CompleteLocalObject f) :
    (approximation f).obj x = FormalObject.restriction x :=
  sorry

/-- Stage `n` of `approximation.obj x` is the restriction of `x` along
`Spec(R ⧸ m^{n+1}) ⟶ Spec(R)`. -/
theorem approximation_family {f : X ⟶ B} [FinitePresentation f]
    (x : CompleteLocalObject f) (n : ℕ) :
    ((approximation f).obj x).objects n = FormalObject.restrictionObj x n :=
  sorry

/-- Successor maps of `approximation.obj x` are the transitivity comparisons of
restriction. -/
theorem approximation_step {f : X ⟶ B} [FinitePresentation f]
    (x : CompleteLocalObject f) (n : ℕ) :
    ((approximation f).obj x).step n = FormalObject.restrictionStep x n :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.CohStack
