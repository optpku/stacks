/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Limits
public import ReasLib.CategoryTheory.Fibered.BasedCategory.Basic
public import ReasLib.CategoryTheory.Fibered.Groupoids.Hom.OneCell
public import ReasLib.AlgebraicGeometry.GroupoidsOver.Basic
public import Mathlib.CategoryTheory.Category.Cat
public import ReasLib.AlgebraicGeometry.EllipticCurve.HomOver

/-!
# The category fibred in groupoids of elliptic curves

This file owns the category of geometric elliptic curves over schemes, the
forgetful functor to `Over (Spec ℤ)`, the resulting category fibred in
groupoids `M_{1,1}`, and classifying 1-morphisms of elliptic curves.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.EllipticCurve

/-- The canonical final scheme `Spec ℤ` in universe `u`, identified with
`Spec (ULift ℤ)`. -/
abbrev Moduli.specInt : Scheme.{u} :=
  Spec (CommRingCat.of (ULift.{u} ℤ))

/-- `Moduli.specInt` is the spectrum of `ULift ℤ`. -/
theorem Moduli.specInt_eq :
    Moduli.specInt = Spec (CommRingCat.of (ULift.{u} ℤ)) := rfl

namespace Moduli

/-- An object of the moduli stack of elliptic curves: a scheme over `Spec ℤ`
together with an elliptic curve over that scheme. -/
structure Obj : Type (u + 1) where
  /-- The base scheme, as an object of `Over (Spec ℤ)`. -/
  U : Over specInt
  /-- The total space of the elliptic curve, as a scheme over `U.left`. -/
  E : Over U.left
  /-- The zero section of the elliptic curve. -/
  zero : U.left ⟶ E.left
  /-- The pair `(E, zero)` is an elliptic curve over `U.left`. -/
  isElliptic : IsEllipticCurve E zero

/-- Assemble an object of `M_{1,1}` from a geometric elliptic curve over a
scheme, using the unique morphism to `Spec ℤ`. -/
def Obj.ofEllipticCurve {S : Scheme.{u}} (E : Over S) (zero : S ⟶ E.left)
    [h : IsEllipticCurve E zero] : Obj where
  U := Over.mk (specULiftZIsTerminal.from S)
  E := E
  zero := zero
  isElliptic := h

/-- `Obj.ofEllipticCurve` stores the supplied elliptic curve over the unique
map from its base to `Spec ℤ`. -/
theorem Obj.ofEllipticCurve_spec {S : Scheme.{u}} (E : Over S)
    (zero : S ⟶ E.left) [IsEllipticCurve E zero] :
    (Obj.ofEllipticCurve E zero).U = Over.mk (specULiftZIsTerminal.from S) ∧
      (Obj.ofEllipticCurve E zero).E = E ∧
      (Obj.ofEllipticCurve E zero).zero = zero := ⟨rfl, rfl, rfl⟩

/-- A morphism of objects of `M_{1,1}` is a base map over `Spec ℤ` together with
a cartesian zero-preserving map of elliptic curves over that base map. -/
structure Hom (ξ ξ' : Obj) : Type u where
  /-- The underlying morphism of base schemes over `Spec ℤ`. -/
  f : ξ.U ⟶ ξ'.U
  /-- The cartesian zero-preserving map of elliptic curves over `f.left`. -/
  iso : HomOver f.left ξ.E ξ.zero ξ'.E ξ'.zero

/-- Morphisms are determined by their base map and total-space map. -/
private theorem Hom.ext {ξ ξ' : Obj} {α β : Hom ξ ξ'}
    (hf : α.f = β.f) (hh : α.iso.hom = β.iso.hom) : α = β := by
  cases α with
  | mk f iso =>
    cases β with
    | mk f' iso' =>
      cases hf
      cases iso
      cases iso'
      cases hh
      rfl

/-- Assemble a base morphism and a morphism of elliptic curves as a morphism of
`M_{1,1}`. -/
def Hom.ofHomOver {ξ ξ' : Obj} (f : ξ.U ⟶ ξ'.U)
    (iso : HomOver f.left ξ.E ξ.zero ξ'.E ξ'.zero) : Hom ξ ξ' where
  f := f
  iso := iso

/-- `Hom.ofHomOver` stores the supplied base map and elliptic-curve morphism. -/
theorem Hom.ofHomOver_spec {ξ ξ' : Obj} (f : ξ.U ⟶ ξ'.U)
    (iso : HomOver f.left ξ.E ξ.zero ξ'.E ξ'.zero) :
    (Hom.ofHomOver f iso).f = f ∧ (Hom.ofHomOver f iso).iso = iso := ⟨rfl, rfl⟩

/-- Identity morphisms of `M_{1,1}`. -/
def Hom.id (ξ : Obj) : Hom ξ ξ where
  f := 𝟙 ξ.U
  iso := HomOver.id ξ.E ξ.zero

/-- The identity morphism of `M_{1,1}` has identity base map. -/
theorem Hom.id_f (ξ : Obj) : (Hom.id ξ).f = 𝟙 ξ.U := rfl

/-- Composition of morphisms of `M_{1,1}`. -/
def Hom.comp {ξ ξ' ξ'' : Obj} (α : Hom ξ ξ') (β : Hom ξ' ξ'') : Hom ξ ξ'' where
  f := α.f ≫ β.f
  iso := HomOver.comp α.iso β.iso

/-- Composition of morphisms of `M_{1,1}` composes the base maps. -/
theorem Hom.comp_f {ξ ξ' ξ'' : Obj} (α : Hom ξ ξ') (β : Hom ξ' ξ'') :
    (Hom.comp α β).f = α.f ≫ β.f := rfl

/-- Left identity law for morphisms of `M_{1,1}`. -/
theorem Hom.id_comp {ξ ξ' : Obj} (α : Hom ξ ξ') : Hom.comp (Hom.id ξ) α = α := by
  apply Hom.ext
  · exact Category.id_comp α.f
  · exact Category.id_comp α.iso.hom

/-- Right identity law for morphisms of `M_{1,1}`. -/
theorem Hom.comp_id {ξ ξ' : Obj} (α : Hom ξ ξ') : Hom.comp α (Hom.id ξ') = α := by
  apply Hom.ext
  · exact Category.comp_id α.f
  · exact Category.comp_id α.iso.hom

/-- Associativity of composition of morphisms of `M_{1,1}`. -/
theorem Hom.assoc {ξ₁ ξ₂ ξ₃ ξ₄ : Obj}
    (α : Hom ξ₁ ξ₂) (β : Hom ξ₂ ξ₃) (γ : Hom ξ₃ ξ₄) :
    Hom.comp (Hom.comp α β) γ = Hom.comp α (Hom.comp β γ) := by
  apply Hom.ext
  · exact Category.assoc α.f β.f γ.f
  · exact Category.assoc α.iso.hom β.iso.hom γ.iso.hom

/-- The category of elliptic curves over schemes, as the total category of
`M_{1,1}`. -/
@[reducible]
def category : Category.{u} Obj where
  Hom := Hom
  id := Hom.id
  comp := Hom.comp
  id_comp := Hom.id_comp
  comp_id := Hom.comp_id
  assoc := Hom.assoc

/-- The bundled category of geometric elliptic curves over schemes. -/
def cat : CategoryTheory.Cat.{u, u + 1} :=
  ⟨Obj, category⟩

/-- The forgetful functor from the category of elliptic curves to
`Over (Spec ℤ)`. -/
def forget : cat ⥤ Over specInt where
  obj ξ := ξ.U
  map α := α.f
  map_id := Hom.id_f
  map_comp := Hom.comp_f

/-- The forgetful functor sends an object to its base scheme over `Spec ℤ`. -/
theorem forget_obj (ξ : Obj) : forget.obj ξ = ξ.U := rfl

/-- The forgetful functor sends a morphism to its underlying base map. -/
theorem forget_map {ξ ξ' : Obj} (α : Hom ξ ξ') : forget.map α = α.f := rfl

/-- Factor a cartesian morphism through another one using its pullback square. -/
private theorem Hom.factorization {ξ ξ' ζ : Obj} (α : Hom ξ ξ') (β : Hom ζ ξ')
    (g : ζ.U ⟶ ξ.U) (hg : g ≫ α.f = β.f) :
    ∃! γ : Hom ζ ξ, γ.f = g ∧ Hom.comp γ α = β := by
  have hg' : g.left ≫ α.f.left = β.f.left := congrArg (fun f => f.left) hg
  have hcomm : β.iso.hom ≫ ξ'.E.hom = (ζ.E.hom ≫ g.left) ≫ α.f.left := by
    rw [Category.assoc, hg']
    exact β.iso.isPullback.w
  obtain ⟨h, hα, hbase⟩ :=
    α.iso.isPullback.exists_lift β.iso.hom (ζ.E.hom ≫ g.left) hcomm
  have hcart : IsPullback h ζ.E.hom ξ.E.hom g.left := by
    apply IsPullback.of_right (h₁₂ := α.iso.hom) (h₂₂ := α.f.left)
    · simpa only [hα, hg'] using β.iso.isPullback
    · exact hbase
    · exact α.iso.isPullback
  have hzero : ζ.zero ≫ h = g.left ≫ ξ.zero := by
    apply α.iso.isPullback.hom_ext
    · calc
        (ζ.zero ≫ h) ≫ α.iso.hom = ζ.zero ≫ β.iso.hom := by
          rw [Category.assoc, hα]
        _ = β.f.left ≫ ξ'.zero := β.iso.comm_zero
        _ = (g.left ≫ ξ.zero) ≫ α.iso.hom := by
          rw [Category.assoc, α.iso.comm_zero, ← Category.assoc, hg']
    · calc
        (ζ.zero ≫ h) ≫ ξ.E.hom = ζ.zero ≫ (ζ.E.hom ≫ g.left) := by
          rw [Category.assoc, hbase]
        _ = g.left := by
          rw [← Category.assoc, ζ.isElliptic.isSection, Category.id_comp]
        _ = (g.left ≫ ξ.zero) ≫ ξ.E.hom := by
          rw [Category.assoc, ξ.isElliptic.isSection, Category.comp_id]
  let γ : Hom ζ ξ := ⟨g, ⟨h, hcart, hzero⟩⟩
  refine ⟨γ, ⟨rfl, ?_⟩, ?_⟩
  · apply Hom.ext hg
    exact hα
  · intro δ hδ
    apply Hom.ext hδ.1
    apply α.iso.isPullback.hom_ext
    · exact (congrArg (fun ε => ε.iso.hom) hδ.2).trans hα.symm
    · calc
        δ.iso.hom ≫ ξ.E.hom = ζ.E.hom ≫ δ.f.left := δ.iso.isPullback.w
        _ = ζ.E.hom ≫ g.left := by rw [hδ.1]
        _ = h ≫ ξ.E.hom := hbase.symm

/-- Every morphism in the moduli category is strongly cartesian over its base map. -/
private theorem forget_isStronglyCartesian {ξ ξ' : cat} (α : ξ ⟶ ξ') :
    forget.IsStronglyCartesian (forget.map α) α where
  toIsHomLift := inferInstance
  universal_property' {ζ} g β hβ := by
    have hg : g ≫ α.f = β.f :=
      IsHomLift.eq_of_isHomLift forget (g ≫ forget.map α) β
    obtain ⟨γ, hγ, huniq⟩ := Hom.factorization α β g hg
    refine ⟨γ, ⟨?_, hγ.2⟩, ?_⟩
    · rw [← hγ.1]
      exact Functor.IsHomLift.map (p := forget) γ
    · intro δ hδ
      haveI := hδ.1
      exact huniq δ
        ⟨(IsHomLift.eq_of_isHomLift forget g δ).symm, hδ.2⟩

/-- Scheme pullbacks provide lifts of all base maps into the moduli category. -/
private theorem forget_exists_lift (ξ : cat) (U : Over specInt) (f : U ⟶ forget.obj ξ) :
    ∃ (ξ' : cat) (α : ξ' ⟶ ξ), forget.IsStronglyCartesian f α := by
  letI : IsEllipticCurve ξ.E ξ.zero := ξ.isElliptic
  let ξ' : Obj :=
    { U := U
      E := Over.mk (pullback.snd ξ.E.hom f.left)
      zero := pullbackSection ξ.E ξ.zero f.left IsEllipticCurve.isSection
      isElliptic := instIsEllipticCurve_pullback ξ.E ξ.zero f.left }
  let α : Hom ξ' ξ :=
    { f := f
      iso :=
        { hom := pullback.fst ξ.E.hom f.left
          isPullback := IsPullback.of_hasPullback ξ.E.hom f.left
          comm_zero := pullbackSection_fst ξ.E ξ.zero f.left IsEllipticCurve.isSection } }
  exact ⟨ξ', α, forget_isStronglyCartesian α⟩

/-- The forgetful functor is fibered in groupoids. -/
instance forget.instIsFiberedInGroupoids :
    Functor.IsFibered.InGroupoids forget where
  toIsFibered := Functor.IsFibered.of_exists_isStronglyCartesian forget_exists_lift
  all_isCartesian α := by
    haveI := forget_isStronglyCartesian α
    infer_instance

end Moduli

/-- The moduli stack of elliptic curves, as a category fibred in groupoids over
`Over (Spec ℤ)`. -/
def moduli : GroupoidsOver Moduli.specInt :=
  FiberedCategoryOver.Groupoids.ofFunctor Moduli.forget

/-- The projection of `moduli` is the forgetful functor to `Over (Spec ℤ)`. -/
theorem moduli_p : moduli.p = Moduli.forget := rfl

/-- The total category of `moduli` is the category of elliptic curves. -/
theorem moduli_obj : moduli.total = Moduli.Obj := rfl

namespace Moduli

variable (U : Over specInt) (E : Over U.left) (zero : U.left ⟶ E.left)
  [IsEllipticCurve E zero]

/-- The compatibility needed to lift a morphism of test schemes over `U` to a
map of pulled-back total spaces. -/
private theorem classifyingHom_lift_condition (a b : Over U) (f : a ⟶ b) :
    pullback.fst E.hom a.hom.left ≫ E.hom =
      (pullback.snd E.hom a.hom.left ≫ f.left.left) ≫ b.hom.left := by
  have hab : f.left.left ≫ b.hom.left = a.hom.left :=
    congrArg (fun h => h.left) (Over.w f)
  rw [Category.assoc, hab]
  exact pullback.condition

/-- The underlying total-space map of the classifying morphism associated to a
morphism of test schemes over `U`. -/
private def classifyingHom_hom (a b : Over U) (f : a ⟶ b) :
    pullback E.hom a.hom.left ⟶ pullback E.hom b.hom.left :=
  pullback.lift (pullback.fst E.hom a.hom.left)
    (pullback.snd E.hom a.hom.left ≫ f.left.left)
    (by exact classifyingHom_lift_condition U E a b f)

/-- The classifying total-space map is cartesian over the underlying scheme
map. -/
private theorem classifyingHom_isPullback (a b : Over U) (f : a ⟶ b) :
    IsPullback (classifyingHom_hom U E a b f)
      (pullback.snd E.hom a.hom.left) (pullback.snd E.hom b.hom.left)
      f.left.left := by
  have hab : f.left.left ≫ b.hom.left = a.hom.left :=
    congrArg (fun h => h.left) (Over.w f)
  apply IsPullback.of_right (h₁₂ := pullback.fst E.hom b.hom.left)
    (h₂₂ := b.hom.left)
  · simpa only [classifyingHom_hom, pullback.lift_fst, hab] using
      (IsPullback.of_hasPullback E.hom a.hom.left)
  · exact pullback.lift_snd _ _ _
  · exact IsPullback.of_hasPullback E.hom b.hom.left

/-- The classifying total-space map preserves lifted zero sections. -/
private theorem classifyingHom_comm_zero (a b : Over U) (f : a ⟶ b) :
    pullbackSection E zero a.hom.left IsEllipticCurve.isSection ≫
        classifyingHom_hom U E a b f =
      f.left.left ≫
        pullbackSection E zero b.hom.left IsEllipticCurve.isSection := by
  have hab : f.left.left ≫ b.hom.left = a.hom.left :=
    congrArg (fun h => h.left) (Over.w f)
  apply pullback.hom_ext
  · simp only [Category.assoc, classifyingHom_hom, pullback.lift_fst,
      pullbackSection_fst]
    rw [← Category.assoc, hab]
  · simp [classifyingHom_hom, pullbackSection, Category.assoc,
      pullback.lift_snd, pullback.lift_snd_assoc]

/-- The morphism of pulled-back elliptic curves induced by a morphism of test
schemes over `U`. -/
private def classifyingHom (a b : Over U) (f : a ⟶ b) :
    HomOver f.left.left (Over.mk (pullback.snd E.hom a.hom.left))
      (pullbackSection E zero a.hom.left IsEllipticCurve.isSection)
      (Over.mk (pullback.snd E.hom b.hom.left))
      (pullbackSection E zero b.hom.left IsEllipticCurve.isSection) where
  hom := classifyingHom_hom U E a b f
  isPullback := by exact classifyingHom_isPullback U E a b f
  comm_zero := by exact classifyingHom_comm_zero U E zero a b f

/-- The object of `M_{1,1}` obtained by pulling `(E, zero)` back along a test
morphism into `U`. -/
def classifyingObj (a : Over U) : Obj where
  U := a.left
  E := Over.mk (pullback.snd E.hom a.hom.left)
  zero := pullbackSection E zero a.hom.left IsEllipticCurve.isSection
  isElliptic := instIsEllipticCurve_pullback E zero a.hom.left

/-- `classifyingObj` has base the source of the test morphism. -/
theorem classifyingObj_U (a : Over U) :
    (classifyingObj U E zero a).U = a.left := rfl

/-- The morphism of `M_{1,1}` induced by a morphism of test schemes over `U`. -/
private def classifyingMap (a b : Over U) (f : a ⟶ b) :
    Hom (classifyingObj U E zero a) (classifyingObj U E zero b) where
  f := f.left
  iso := classifyingHom U E zero a b f

/-- Identity morphisms of test schemes act as identities on classifying
objects. -/
private theorem classifyingFunctor_map_id (a : Over U) :
    classifyingMap U E zero a a (𝟙 a) = Hom.id (classifyingObj U E zero a) := by
  apply Hom.ext
  · rfl
  · change classifyingHom_hom U E a a (𝟙 a) = 𝟙 _
    apply pullback.hom_ext
    · simp [classifyingHom_hom]
    · simp [classifyingHom_hom]

/-- Classifying morphisms preserve composition of test morphisms. -/
private theorem classifyingFunctor_map_comp (a b c : Over U) (f : a ⟶ b) (g : b ⟶ c) :
    classifyingMap U E zero a c (f ≫ g) =
      Hom.comp (classifyingMap U E zero a b f) (classifyingMap U E zero b c g) := by
  apply Hom.ext
  · rfl
  · change classifyingHom_hom U E a c (f ≫ g) =
      classifyingHom_hom U E a b f ≫ classifyingHom_hom U E b c g
    apply pullback.hom_ext
    · simp [classifyingHom_hom, Category.assoc, pullback.lift_fst]
    · simp [classifyingHom_hom, Category.assoc, pullback.lift_snd,
        pullback.lift_snd_assoc]

/-- The total functor of the classifying 1-morphism associated to `(E, zero)`. -/
def classifyingFunctor : Over U ⥤ cat where
  obj := classifyingObj U E zero
  map {a b} f := private classifyingMap U E zero a b f
  map_id := by exact classifyingFunctor_map_id U E zero
  map_comp {a b c} f g := by exact classifyingFunctor_map_comp U E zero a b c f g

/-- The classifying total functor sends a test morphism `a : V ⟶ U` to the
pullback of `(E, zero)` along `a`. -/
theorem classifyingFunctor_obj (a : Over U) :
    (classifyingFunctor U E zero).obj a = classifyingObj U E zero a := rfl

/-- The classifying total functor lies strictly over `Over (Spec ℤ)`. -/
theorem classifyingFunctor_forget :
    classifyingFunctor U E zero ⋙ forget = Over.forget U := by
  rfl

/-- The classifying 1-morphism `U ⟶ M_{1,1}` associated to an elliptic curve
over `U`. -/
def classifying : GroupoidsOver.slice U ⟶ moduli :=
  FiberedCategoryOver.Groupoids.ofBasedFunctor
    { toFunctor := classifyingFunctor U E zero
      w := classifyingFunctor_forget U E zero }

/-- The total functor of `classifying` is `classifyingFunctor`. -/
theorem classifying_toFunctor :
    FiberedCategoryOver.Groupoids.toFunctor (classifying U E zero) =
      classifyingFunctor U E zero := rfl

/-- The classifying 1-morphism lies over the slice projection `Over.forget U`. -/
theorem classifying_p :
    FiberedCategoryOver.Groupoids.toFunctor (classifying U E zero) ⋙ moduli.p =
      Over.forget U := classifyingFunctor_forget U E zero

/-- Evaluating the classifying 1-morphism on a test morphism `a : V ⟶ U` yields
the pullback of `(E, zero)` along `a`. -/
theorem classifying_spec (a : Over U) :
    (FiberedCategoryOver.Groupoids.toFunctor (classifying U E zero)).obj a =
      classifyingObj U E zero a := rfl

end Moduli

end AlgebraicGeometry.EllipticCurve
