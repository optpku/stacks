module

public import Mathlib.CategoryTheory.FiberedCategory.Fibered
public import stacks_project.Chap98.Definition_98_9_1_Hom

/-!
# Approximation of objects by formal objects

Restriction along `Spec(R ⧸ m^{n+1}) ⟶ Spec(R)` sends an object of a groupoid
fibration over a complete local finite-type-residue spectrum to a formal object
in the sense of definition-formal-objects. This construction is functorial.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Functor IsLocalRing

noncomputable section

universe u

namespace AlgebraicGeometry.CompleteLocalSAlgebra

variable {S : Scheme.{u}}

/-- Canonical scheme morphism `Spec(R ⧸ m^{n+1}) ⟶ Spec(R)`. -/
def truncationToSpec (R : CompleteLocalSAlgebra S) (n : ℕ) :
    R.truncationSpec n ⟶ Spec (CommRingCat.of R.carrier) :=
  Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (maximalIdeal R.carrier ^ (n + 1))))

/-- `truncationToSpec` is the spectrum of the quotient map of `m^{n+1}`. -/
theorem truncationToSpec_eq (R : CompleteLocalSAlgebra S) (n : ℕ) :
    R.truncationToSpec n =
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (maximalIdeal R.carrier ^ (n + 1)))) :=
  sorry

/-- Restriction morphism `Spec(R ⧸ m^{n+1}) ⟶ Spec(R)` in `Over S`. -/
def truncationOverHom (R : CompleteLocalSAlgebra S) (n : ℕ) :
    R.stageOver n ⟶ Over.mk R.toS :=
  Over.homMk (R.truncationToSpec n) rfl

/-- The underlying scheme morphism of `truncationOverHom` is `truncationToSpec`. -/
theorem truncationOverHom_left (R : CompleteLocalSAlgebra S) (n : ℕ) :
    (R.truncationOverHom n).left = R.truncationToSpec n := sorry

/-- Restriction to stage `n` factors through the successor thickening
`Spec(R ⧸ m^{n+1}) ⟶ Spec(R ⧸ m^{n+2}) ⟶ Spec(R)`. -/
theorem truncationOverHom_comp (R : CompleteLocalSAlgebra S) (n : ℕ) :
    R.truncationOverHom n = R.stageHom n ≫ R.truncationOverHom (n + 1) :=
  sorry

end AlgebraicGeometry.CompleteLocalSAlgebra

namespace AlgebraicGeometry.GroupoidsOver

variable {S : Scheme.{u}} [IsLocallyNoetherian S]

/-- An object of `X` lying over `Spec(R)` for a Noetherian complete local
`S`-algebra `R` with residue field of finite type over `S`. -/
structure CompleteLocalObject (X : GroupoidsOver S) where
  /-- Complete local `S`-algebra underlying the object. -/
  base : CompleteLocalSAlgebra S
  /-- Underlying object of the total category of `X`. -/
  object : X.total
  /-- The object lies over `Spec(R) ⟶ S`. -/
  over_obj : X.p.obj object = Over.mk base.toS

namespace CompleteLocalObject

variable {X : GroupoidsOver S}

/-- Package an object of `X` over a complete local finite-type-residue spectrum. -/
def of (base : CompleteLocalSAlgebra S) (object : X.total)
    (over_obj : X.p.obj object = Over.mk base.toS) : CompleteLocalObject X where
  base := base
  object := object
  over_obj := over_obj

/-- An object of the source of approximation lies over its stored complete local
spectrum. -/
theorem spec (x : CompleteLocalObject X) :
    X.p.obj x.object = Over.mk x.base.toS :=
  sorry

/-- Underlying morphism of spectra induced by a morphism of complete local
objects. -/
def schemeHom {x y : CompleteLocalObject X} (f : x.object ⟶ y.object) :
    Spec (CommRingCat.of x.base.carrier) ⟶ Spec (CommRingCat.of y.base.carrier) :=
  eqToHom (congrArg Over.left x.over_obj).symm ≫ (X.p.map f).left ≫
    eqToHom (congrArg Over.left y.over_obj)

/-- Ring homomorphism associated to a morphism of complete local objects. -/
def ringHom {x y : CompleteLocalObject X} (f : x.object ⟶ y.object) :
    y.base.carrier →+* x.base.carrier :=
  CommRingCat.Hom.hom <|
    (Scheme.ΓSpecIso (CommRingCat.of y.base.carrier)).inv ≫ (schemeHom f).appTop ≫
      (Scheme.ΓSpecIso (CommRingCat.of x.base.carrier)).hom

/-- The induced ring map of a morphism of complete local objects is local. -/
theorem ringHom_isLocalHom {x y : CompleteLocalObject X} (f : x.object ⟶ y.object) :
    IsLocalHom (ringHom f) :=
  sorry

/-- The spectrum of the induced ring map lies over `S`. -/
theorem ringHom_over_S {x y : CompleteLocalObject X} (f : x.object ⟶ y.object) :
    Spec.map (CommRingCat.ofHom (ringHom f)) ≫ y.base.toS = x.base.toS :=
  sorry

/-- Induced morphism of complete local `S`-algebras of a morphism of complete
local objects. Locality and compatibility with `S` are proof obligations, not
extra restrictions of the full subcategory. -/
def baseHom {x y : CompleteLocalObject X} (f : x.object ⟶ y.object) :
    CompleteLocalSAlgebra.Hom x.base y.base where
  hom := ringHom f
  isLocalHom := ringHom_isLocalHom f
  over_S := ringHom_over_S f

/-- `baseHom` recovers the extracted ring homomorphism. -/
theorem baseHom_hom {x y : CompleteLocalObject X} (f : x.object ⟶ y.object) :
    (baseHom f).hom = ringHom f :=
  sorry

/-- Underlying morphism in `Over S` induced by a morphism of complete local
objects. -/
def overHom {x y : CompleteLocalObject X} (f : x.object ⟶ y.object) :
    Over.mk x.base.toS ⟶ Over.mk y.base.toS :=
  eqToHom x.over_obj.symm ≫ X.p.map f ≫ eqToHom y.over_obj

/-- A morphism of complete local objects lies over `overHom`. -/
instance overHom_isHomLift {x y : CompleteLocalObject X} (f : x.object ⟶ y.object) :
    X.p.IsHomLift (overHom f) f :=
  IsHomLift.of_fac X.p (overHom f) f x.over_obj y.over_obj rfl

/-- Identity morphism of a complete local object. -/
def Hom.id (x : CompleteLocalObject X) : x.object ⟶ x.object := 𝟙 x.object

/-- Composition of morphisms of complete local objects. -/
def Hom.comp {x y z : CompleteLocalObject X} (f : x.object ⟶ y.object)
    (g : y.object ⟶ z.object) : x.object ⟶ z.object :=
  f ≫ g

/-- The full subcategory of complete local objects of `X`. Morphisms are all
morphisms of the total category of `X`. -/
instance category : Category.{u} (CompleteLocalObject X) where
  Hom x y := x.object ⟶ y.object
  id := Hom.id
  comp f g := Hom.comp f g
  id_comp := sorry
  comp_id := sorry
  assoc := sorry

/-- Forgetful functor from complete local objects to the total category of `X`. -/
def forget : CompleteLocalObject X ⥤ X.total where
  obj x := x.object
  map f := f
  map_id := sorry
  map_comp := sorry

/-- The forgetful functor returns the stored object of `X`. -/
theorem forget_obj (x : CompleteLocalObject X) : forget.obj x = x.object :=
  sorry

end CompleteLocalObject

namespace FormalObject

variable {X : GroupoidsOver S}

/-- Category of formal objects of `X`, with morphisms the natural families over
a morphism of complete local `S`-algebras. -/
instance category : Category.{u} (FormalObject X) where
  Hom := Hom
  id := Hom.id
  comp f g := Hom.comp f g
  id_comp := sorry
  comp_id := sorry
  assoc := sorry

/-- Unique factorization of a lift through a strongly cartesian arrow. -/
def factorCartesian {U V W : Over S} {x y z : X.total} (f : V ⟶ U) (φ : y ⟶ x)
    (hφ : X.p.IsStronglyCartesian f φ) {g : W ⟶ V} {f' : W ⟶ U} (hf' : f' = g ≫ f)
    (φ' : z ⟶ x) (hφ' : X.p.IsHomLift f' φ') : z ⟶ y :=
  @IsStronglyCartesian.map _ _ _ _ X.p _ _ _ _ f φ hφ _ _ g f' hf' φ' hφ'

/-- The comparison `factorCartesian` lies over the first factor of the base. -/
instance factorCartesian_isHomLift {U V W : Over S} {x y z : X.total} (f : V ⟶ U)
    (φ : y ⟶ x) (hφ : X.p.IsStronglyCartesian f φ) {g : W ⟶ V} {f' : W ⟶ U}
    (hf' : f' = g ≫ f) (φ' : z ⟶ x) (hφ' : X.p.IsHomLift f' φ') :
    X.p.IsHomLift g (factorCartesian f φ hφ hf' φ' hφ') :=
  @IsStronglyCartesian.map_isHomLift _ _ _ _ X.p _ _ _ _ f φ hφ _ _ g f' hf' φ' hφ'

/-- Restriction of an object along `Spec(R ⧸ m^{n+1}) ⟶ Spec(R)`. -/
def restrictionObj (x : CompleteLocalObject X) (n : ℕ) : X.total :=
  IsPreFibered.pullbackObj x.over_obj (x.base.truncationOverHom n)

/-- Cartesian lift of restriction along `Spec(R ⧸ m^{n+1}) ⟶ Spec(R)`. -/
def restrictionHom (x : CompleteLocalObject X) (n : ℕ) :
    restrictionObj x n ⟶ x.object :=
  IsPreFibered.pullbackMap x.over_obj (x.base.truncationOverHom n)

/-- Restriction of `x` to stage `n` is cartesian over `truncationOverHom`. -/
instance restrictionHom_isCartesian (x : CompleteLocalObject X) (n : ℕ) :
    X.p.IsCartesian (x.base.truncationOverHom n) (restrictionHom x n) :=
  IsPreFibered.pullbackMap.IsCartesian x.over_obj (x.base.truncationOverHom n)

/-- Restriction of `x` to stage `n` is strongly cartesian. -/
instance restrictionHom_isStronglyCartesian (x : CompleteLocalObject X) (n : ℕ) :
    X.p.IsStronglyCartesian (x.base.truncationOverHom n) (restrictionHom x n) :=
  IsFibered.isStronglyCartesian_of_isCartesian X.p (x.base.truncationOverHom n)
    (restrictionHom x n)

/-- Stage `n` of the restricted system lies over `Spec(R ⧸ m^{n+1})`. -/
theorem restrictionObj_over (x : CompleteLocalObject X) (n : ℕ) :
    X.p.obj (restrictionObj x n) = x.base.stageOver n :=
  sorry

/-- Successor map of restrictions, obtained from transitivity of pullback along
`Spec(R ⧸ m^{n+1}) ⟶ Spec(R ⧸ m^{n+2}) ⟶ Spec(R)`. -/
def restrictionStep (x : CompleteLocalObject X) (n : ℕ) :
    restrictionObj x n ⟶ restrictionObj x (n + 1) :=
  factorCartesian (x.base.truncationOverHom (n + 1)) (restrictionHom x (n + 1))
    (restrictionHom_isStronglyCartesian x (n + 1)) (x.base.truncationOverHom_comp n)
    (restrictionHom x n) (restrictionHom_isCartesian x n).toIsHomLift

/-- Successor maps of restrictions lift the truncated thickenings. -/
instance restrictionStep_isHomLift (x : CompleteLocalObject X) (n : ℕ) :
    X.p.IsHomLift (x.base.stageHom n) (restrictionStep x n) :=
  factorCartesian_isHomLift (x.base.truncationOverHom (n + 1))
    (restrictionHom x (n + 1)) (restrictionHom_isStronglyCartesian x (n + 1))
    (x.base.truncationOverHom_comp n) (restrictionHom x n)
    (restrictionHom_isCartesian x n).toIsHomLift

/-- Formal object obtained by restricting `x` along all truncations
`Spec(R ⧸ m^{n+1}) ⟶ Spec(R)`. -/
def restriction (x : CompleteLocalObject X) : FormalObject X :=
  of x.base (restrictionObj x) (restrictionStep x)
    (fun n ↦ IsPreFibered.pullbackObj_proj x.over_obj (x.base.truncationOverHom n))
    (restrictionStep_isHomLift x)

/-- Stage objects of `restriction x` are the chosen cartesian restrictions. -/
theorem restriction_family (x : CompleteLocalObject X) (n : ℕ) :
    (restriction x).objects n = restrictionObj x n :=
  sorry

/-- Successor maps of `restriction x` are the transitivity comparisons. -/
theorem restriction_step (x : CompleteLocalObject X) (n : ℕ) :
    (restriction x).step n = restrictionStep x n :=
  sorry

/-- Restriction of `x` followed by `f` lies over the composite truncated base
morphism. -/
theorem approximation_factor {x y : CompleteLocalObject X} (f : x.object ⟶ y.object)
    (n : ℕ) :
    x.base.truncationOverHom n ≫ CompleteLocalObject.overHom f =
      (CompleteLocalObject.baseHom f).stageMap n ≫ y.base.truncationOverHom n :=
  sorry

/-- The composite `restrictionHom x n ≫ f` lifts the composite truncated base
morphism. -/
instance approximationApp_isHomLift {x y : CompleteLocalObject X}
    (f : x.object ⟶ y.object) (n : ℕ) :
    X.p.IsHomLift (x.base.truncationOverHom n ≫ CompleteLocalObject.overHom f)
      (restrictionHom x n ≫ f) :=
  IsHomLift.comp X.p (x.base.truncationOverHom n) (CompleteLocalObject.overHom f)
    (restrictionHom x n) f

/-- Stagewise restriction of a morphism of complete local objects. -/
def approximationApp {x y : CompleteLocalObject X} (f : x.object ⟶ y.object)
    (n : ℕ) : restrictionObj x n ⟶ restrictionObj y n :=
  factorCartesian (y.base.truncationOverHom n) (restrictionHom y n)
    (restrictionHom_isStronglyCartesian y n) (approximation_factor f n)
    (restrictionHom x n ≫ f) (approximationApp_isHomLift f n)

/-- Stage maps of approximation lie over the truncated maps of `baseHom`. -/
instance approximationApp_over {x y : CompleteLocalObject X} (f : x.object ⟶ y.object)
    (n : ℕ) :
    X.p.IsHomLift ((CompleteLocalObject.baseHom f).stageMap n) (approximationApp f n) :=
  factorCartesian_isHomLift (y.base.truncationOverHom n) (restrictionHom y n)
    (restrictionHom_isStronglyCartesian y n) (approximation_factor f n)
    (restrictionHom x n ≫ f) (approximationApp_isHomLift f n)

/-- The approximation functor sending an object over `Spec(R)` to the formal
object of its restrictions along `Spec(R ⧸ m^{n+1}) ⟶ Spec(R)`. Lean stage `n`
is the source object `ξ_{n+1}` over `Spec(R ⧸ m^{n+1})`. -/
def approximation : CompleteLocalObject X ⥤ FormalObject X where
  obj := restriction
  map f := Hom.of (approximationApp f) (CompleteLocalObject.baseHom f)
      (approximationApp_over f) (fun _ ↦ sorry)
  map_id := sorry
  map_comp := sorry

/-- The object map of approximation is restriction along truncations. -/
theorem approximation_obj (x : CompleteLocalObject X) :
    approximation.obj x = restriction x :=
  sorry

/-- Stage `n` of `approximation.obj x` is the restriction of `x` along
`Spec(R ⧸ m^{n+1}) ⟶ Spec(R)`. -/
theorem approximation_family (x : CompleteLocalObject X) (n : ℕ) :
    (approximation.obj x).objects n = restrictionObj x n :=
  sorry

/-- Successor maps of `approximation.obj x` are the transitivity comparisons of
restriction. -/
theorem approximation_step (x : CompleteLocalObject X) (n : ℕ) :
    (approximation.obj x).step n = restrictionStep x n :=
  sorry

/-- Stage maps of `approximation.map f` are cartesian factorizations of
`restrictionHom x n ≫ f`. -/
theorem approximation_map_app {x y : CompleteLocalObject X} (f : x.object ⟶ y.object)
    (n : ℕ) : (approximation.map f).app n = approximationApp f n :=
  sorry

end FormalObject

end AlgebraicGeometry.GroupoidsOver
