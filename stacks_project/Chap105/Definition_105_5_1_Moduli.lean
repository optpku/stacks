/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.Limits
public import ReasLib.CategoryTheory.Fibered.BasedCategory.Basic
public import ReasLib.CategoryTheory.Fibered.Groupoids.Hom.OneCell
public import stacks_project.Chap94.Definition_94_12_1_Representable
public import stacks_project.Chap105.Lemma_105_4_1_Key_fact_EllipticCurve

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
    Moduli.specInt = Spec (CommRingCat.of (ULift.{u} ℤ)) := sorry

namespace HomOver

/-- Pasting cartesian squares of elliptic-curve morphisms yields a cartesian
square over the composite base morphism. -/
theorem comp_isPullback {S S' S'' : Scheme.{u}} {a : S ⟶ S'} {b : S' ⟶ S''}
    {E : Over S} {zero : S ⟶ E.left} {E' : Over S'} {zero' : S' ⟶ E'.left}
    {E'' : Over S''} {zero'' : S'' ⟶ E''.left}
    (φ : HomOver a E zero E' zero') (ψ : HomOver b E' zero' E'' zero'') :
    IsPullback (φ.hom ≫ ψ.hom) E.hom E''.hom (a ≫ b) := sorry

/-- Composite elliptic-curve morphisms send the source zero section to the
target zero section. -/
theorem comp_comm_zero {S S' S'' : Scheme.{u}} {a : S ⟶ S'} {b : S' ⟶ S''}
    {E : Over S} {zero : S ⟶ E.left} {E' : Over S'} {zero' : S' ⟶ E'.left}
    {E'' : Over S''} {zero'' : S'' ⟶ E''.left}
    (φ : HomOver a E zero E' zero') (ψ : HomOver b E' zero' E'' zero'') :
    zero ≫ φ.hom ≫ ψ.hom = (a ≫ b) ≫ zero'' := sorry

/-- Composition of morphisms of elliptic curves along a composite base map. -/
def comp {S S' S'' : Scheme.{u}} {a : S ⟶ S'} {b : S' ⟶ S''}
    {E : Over S} {zero : S ⟶ E.left} {E' : Over S'} {zero' : S' ⟶ E'.left}
    {E'' : Over S''} {zero'' : S'' ⟶ E''.left}
    (φ : HomOver a E zero E' zero') (ψ : HomOver b E' zero' E'' zero'') :
    HomOver (a ≫ b) E zero E'' zero'' where
  hom := φ.hom ≫ ψ.hom
  isPullback := comp_isPullback φ ψ
  comm_zero := comp_comm_zero φ ψ

/-- The underlying total-space map of a composite is the composite of the
underlying maps. -/
theorem comp_hom {S S' S'' : Scheme.{u}} {a : S ⟶ S'} {b : S' ⟶ S''}
    {E : Over S} {zero : S ⟶ E.left} {E' : Over S'} {zero' : S' ⟶ E'.left}
    {E'' : Over S''} {zero'' : S'' ⟶ E''.left}
    (φ : HomOver a E zero E' zero') (ψ : HomOver b E' zero' E'' zero'') :
    (comp φ ψ).hom = φ.hom ≫ ψ.hom := sorry

end HomOver

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
      (Obj.ofEllipticCurve E zero).zero = zero := sorry

/-- A morphism of objects of `M_{1,1}` is a base map over `Spec ℤ` together with
a cartesian zero-preserving map of elliptic curves over that base map. -/
structure Hom (ξ ξ' : Obj) : Type u where
  /-- The underlying morphism of base schemes over `Spec ℤ`. -/
  f : ξ.U ⟶ ξ'.U
  /-- The cartesian zero-preserving map of elliptic curves over `f.left`. -/
  iso : HomOver f.left ξ.E ξ.zero ξ'.E ξ'.zero

/-- Assemble a base morphism and a morphism of elliptic curves as a morphism of
`M_{1,1}`. -/
def Hom.ofHomOver {ξ ξ' : Obj} (f : ξ.U ⟶ ξ'.U)
    (iso : HomOver f.left ξ.E ξ.zero ξ'.E ξ'.zero) : Hom ξ ξ' where
  f := f
  iso := iso

/-- `Hom.ofHomOver` stores the supplied base map and elliptic-curve morphism. -/
theorem Hom.ofHomOver_spec {ξ ξ' : Obj} (f : ξ.U ⟶ ξ'.U)
    (iso : HomOver f.left ξ.E ξ.zero ξ'.E ξ'.zero) :
    (Hom.ofHomOver f iso).f = f ∧ (Hom.ofHomOver f iso).iso = iso := sorry

/-- Identity morphisms of `M_{1,1}`. -/
def Hom.id (ξ : Obj) : Hom ξ ξ where
  f := 𝟙 ξ.U
  iso := HomOver.id ξ.E ξ.zero

/-- The identity morphism of `M_{1,1}` has identity base map. -/
theorem Hom.id_f (ξ : Obj) : (Hom.id ξ).f = 𝟙 ξ.U := sorry

/-- Composition of morphisms of `M_{1,1}`. -/
def Hom.comp {ξ ξ' ξ'' : Obj} (α : Hom ξ ξ') (β : Hom ξ' ξ'') : Hom ξ ξ'' where
  f := α.f ≫ β.f
  iso := HomOver.comp α.iso β.iso

/-- Composition of morphisms of `M_{1,1}` composes the base maps. -/
theorem Hom.comp_f {ξ ξ' ξ'' : Obj} (α : Hom ξ ξ') (β : Hom ξ' ξ'') :
    (Hom.comp α β).f = α.f ≫ β.f := sorry

/-- Left identity law for morphisms of `M_{1,1}`. -/
theorem Hom.id_comp {ξ ξ' : Obj} (α : Hom ξ ξ') : Hom.comp (Hom.id ξ) α = α :=
  sorry

/-- Right identity law for morphisms of `M_{1,1}`. -/
theorem Hom.comp_id {ξ ξ' : Obj} (α : Hom ξ ξ') : Hom.comp α (Hom.id ξ') = α :=
  sorry

/-- Associativity of composition of morphisms of `M_{1,1}`. -/
theorem Hom.assoc {ξ₁ ξ₂ ξ₃ ξ₄ : Obj}
    (α : Hom ξ₁ ξ₂) (β : Hom ξ₂ ξ₃) (γ : Hom ξ₃ ξ₄) :
    Hom.comp (Hom.comp α β) γ = Hom.comp α (Hom.comp β γ) := sorry

/-- The category of elliptic curves over schemes, as the total category of
`M_{1,1}`. -/
instance instCategory : Category.{u} Obj where
  Hom := Hom
  id := Hom.id
  comp := Hom.comp
  id_comp := Hom.id_comp
  comp_id := Hom.comp_id
  assoc := Hom.assoc

/-- The forgetful functor sends identity morphisms of `M_{1,1}` to identity
morphisms of `Over (Spec ℤ)`. -/
theorem forget_map_id (ξ : Obj) : (Hom.id ξ).f = 𝟙 ξ.U := sorry

/-- The forgetful functor preserves composition. -/
theorem forget_map_comp {ξ ξ' ξ'' : Obj} (α : Hom ξ ξ') (β : Hom ξ' ξ'') :
    (Hom.comp α β).f = α.f ≫ β.f := sorry

/-- The forgetful functor from the category of elliptic curves to
`Over (Spec ℤ)`. -/
def forget : Obj ⥤ Over specInt where
  obj ξ := ξ.U
  map α := α.f
  map_id := forget_map_id
  map_comp := forget_map_comp

/-- The forgetful functor sends an object to its base scheme over `Spec ℤ`. -/
theorem forget_obj (ξ : Obj) : forget.obj ξ = ξ.U := sorry

/-- The forgetful functor sends a morphism to its underlying base map. -/
theorem forget_map {ξ ξ' : Obj} (α : Hom ξ ξ') : forget.map α = α.f := sorry

/-- The forgetful functor is fibered in groupoids. -/
instance forget.instIsFiberedInGroupoids :
    Functor.IsFibered.InGroupoids forget := sorry

end Moduli

/-- The moduli stack of elliptic curves, as a category fibred in groupoids over
`Over (Spec ℤ)`. -/
def moduli : GroupoidsOver Moduli.specInt :=
  FiberedCategoryOver.Groupoids.ofFunctor Moduli.forget

/-- The projection of `moduli` is the forgetful functor to `Over (Spec ℤ)`. -/
theorem moduli_p : moduli.p = Moduli.forget := sorry

/-- The total category of `moduli` is the category of elliptic curves. -/
theorem moduli_obj : moduli.total = Moduli.Obj := sorry

namespace Moduli

variable (U : Over specInt) (E : Over U.left) (zero : U.left ⟶ E.left)
  [IsEllipticCurve E zero]

/-- The compatibility needed to lift a morphism of test schemes over `U` to a
map of pulled-back total spaces. -/
theorem classifyingHom_lift_condition (a b : Over U) (f : a ⟶ b) :
    pullback.fst E.hom a.hom.left ≫ E.hom =
      (pullback.snd E.hom a.hom.left ≫ f.left.left) ≫ b.hom.left := sorry

/-- The underlying total-space map of the classifying morphism associated to a
morphism of test schemes over `U`. -/
def classifyingHom_hom (a b : Over U) (f : a ⟶ b) :
    pullback E.hom a.hom.left ⟶ pullback E.hom b.hom.left :=
  pullback.lift (pullback.fst E.hom a.hom.left)
    (pullback.snd E.hom a.hom.left ≫ f.left.left)
    (classifyingHom_lift_condition U E a b f)

/-- The classifying total-space map is cartesian over the underlying scheme
map. -/
theorem classifyingHom_isPullback (a b : Over U) (f : a ⟶ b) :
    IsPullback (classifyingHom_hom U E a b f)
      (pullback.snd E.hom a.hom.left) (pullback.snd E.hom b.hom.left)
      f.left.left := sorry

/-- The classifying total-space map preserves lifted zero sections. -/
theorem classifyingHom_comm_zero (a b : Over U) (f : a ⟶ b) :
    pullbackSection E zero a.hom.left IsEllipticCurve.isSection ≫
        classifyingHom_hom U E a b f =
      f.left.left ≫
        pullbackSection E zero b.hom.left IsEllipticCurve.isSection := sorry

/-- The morphism of pulled-back elliptic curves induced by a morphism of test
schemes over `U`. -/
def classifyingHom (a b : Over U) (f : a ⟶ b) :
    HomOver f.left.left (Over.mk (pullback.snd E.hom a.hom.left))
      (pullbackSection E zero a.hom.left IsEllipticCurve.isSection)
      (Over.mk (pullback.snd E.hom b.hom.left))
      (pullbackSection E zero b.hom.left IsEllipticCurve.isSection) where
  hom := classifyingHom_hom U E a b f
  isPullback := classifyingHom_isPullback U E a b f
  comm_zero := classifyingHom_comm_zero U E zero a b f

/-- The object of `M_{1,1}` obtained by pulling `(E, zero)` back along a test
morphism into `U`. -/
def classifyingObj (a : Over U) : Obj where
  U := a.left
  E := Over.mk (pullback.snd E.hom a.hom.left)
  zero := pullbackSection E zero a.hom.left IsEllipticCurve.isSection
  isElliptic := instIsEllipticCurve_pullback E zero a.hom.left

/-- `classifyingObj` has base the source of the test morphism. -/
theorem classifyingObj_U (a : Over U) :
    (classifyingObj U E zero a).U = a.left := sorry

/-- The morphism of `M_{1,1}` induced by a morphism of test schemes over `U`. -/
def classifyingMap (a b : Over U) (f : a ⟶ b) :
    Hom (classifyingObj U E zero a) (classifyingObj U E zero b) where
  f := f.left
  iso := classifyingHom U E zero a b f

/-- Identity morphisms of test schemes act as identities on classifying
objects. -/
theorem classifyingFunctor_map_id (a : Over U) :
    classifyingMap U E zero a a (𝟙 a) = 𝟙 (classifyingObj U E zero a) := sorry

/-- Classifying morphisms preserve composition of test morphisms. -/
theorem classifyingFunctor_map_comp (a b c : Over U) (f : a ⟶ b) (g : b ⟶ c) :
    classifyingMap U E zero a c (f ≫ g) =
      Hom.comp (classifyingMap U E zero a b f) (classifyingMap U E zero b c g) :=
  sorry

/-- The total functor of the classifying 1-morphism associated to `(E, zero)`. -/
def classifyingFunctor : Over U ⥤ Obj where
  obj := classifyingObj U E zero
  map {a b} f := classifyingMap U E zero a b f
  map_id := classifyingFunctor_map_id U E zero
  map_comp {a b c} f g := classifyingFunctor_map_comp U E zero a b c f g

/-- The classifying total functor sends a test morphism `a : V ⟶ U` to the
pullback of `(E, zero)` along `a`. -/
theorem classifyingFunctor_obj (a : Over U) :
    (classifyingFunctor U E zero).obj a = classifyingObj U E zero a := sorry

/-- The classifying total functor lies strictly over `Over (Spec ℤ)`. -/
theorem classifyingFunctor_forget :
    classifyingFunctor U E zero ⋙ forget = Over.forget U := sorry

/-- The classifying 1-morphism `U ⟶ M_{1,1}` associated to an elliptic curve
over `U`. -/
def classifying : GroupoidsOver.slice U ⟶ moduli :=
  FiberedCategoryOver.Groupoids.ofBasedFunctor
    { toFunctor := classifyingFunctor U E zero
      w := classifyingFunctor_forget U E zero }

/-- The total functor of `classifying` is `classifyingFunctor`. -/
theorem classifying_toFunctor :
    FiberedCategoryOver.Groupoids.toFunctor (classifying U E zero) =
      classifyingFunctor U E zero := sorry

/-- The classifying 1-morphism lies over the slice projection `Over.forget U`. -/
theorem classifying_p :
    FiberedCategoryOver.Groupoids.toFunctor (classifying U E zero) ⋙ moduli.p =
      Over.forget U := sorry

/-- Evaluating the classifying 1-morphism on a test morphism `a : V ⟶ U` yields
the pullback of `(E, zero)` along `a`. -/
theorem classifying_spec (a : Over U) :
    (FiberedCategoryOver.Groupoids.toFunctor (classifying U E zero)).obj a =
      classifyingObj U E zero a := sorry

end Moduli


end AlgebraicGeometry.EllipticCurve
