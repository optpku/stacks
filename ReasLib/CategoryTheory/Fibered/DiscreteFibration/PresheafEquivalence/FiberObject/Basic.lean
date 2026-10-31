/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Fibered.DiscreteFibration.Elements
public import ReasLib.CategoryTheory.Fibered.DiscreteFibration.Reindex
public import ReasLib.CategoryTheory.Fibered.Cleavage.Basic.Reindex.Functor
import Mathlib.Tactic.CrossRefAttribute

/-!
# Fiber-object presheaves

This leaf constructs the choice-independent presheaf of objects in the fibers
of a discrete fibration and exposes its intrinsic reindexing API.
-/

@[expose] public section

universe w u v uS vS

namespace CategoryTheory

open Opposite

variable {C : Type u} [Category.{v} C]

namespace Functor

variable {S : Type uS} [Category.{vS} S]

section FiberObjectPresheafImplementation

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

namespace Implementation

/-- Lift uniqueness determines morphisms after transporting their domains. -/
private theorem fiberObjectHomLift_hom_eq
    (p : S ⥤ C) [Functor.IsDiscreteFibration p]
    {R : C} {a : S} (f : R ⟶ p.obj a) (l₁ l₂ : HomLift p f) :
    l₁.hom = eqToHom
      (congrArg HomLift.domain ((IsDiscreteFibration.homLiftSubsingleton f).elim l₁ l₂)) ≫
        l₂.hom := by
  have h := (IsDiscreteFibration.homLiftSubsingleton f).elim l₁ l₂
  cases h
  simp

/-- A prescribed lift identifies the domain of the intrinsic reindexing object. -/
private theorem fiberObjectReindex_eq_of_isHomLift
    (p : S ⥤ C) [Functor.IsDiscreteFibration p]
    {U V : C} (f : V ⟶ U) (x : p.Fiber U)
    {a : S} (φ : a ⟶ x.1) (hφ : p.IsHomLift f φ) :
    (IsDiscreteFibration.reindexObj p f x).1 = a := by
  letI : p.IsHomLift f φ := hφ
  exact congrArg HomLift.domain
    ((IsDiscreteFibration.homLiftSubsingleton (f ≫ eqToHom x.2.symm)).elim
      (IsDiscreteFibration.lift p _) ⟨a, φ, inferInstance⟩)

/-- The intrinsic arrow inherits its lift property directly from its defining lift package. -/
private theorem fiberObjectCartesianHom_isHomLift
    (p : S ⥤ C) [Functor.IsDiscreteFibration p]
    {U V : C} (f : V ⟶ U) (x : p.Fiber U) :
    p.IsHomLift f (IsDiscreteFibration.cartesianHom p f x) := by
  exact (IsHomLift.lift_comp_eqToHom_iff p f _ x.2.symm).mp
    (IsDiscreteFibration.lift p (f ≫ eqToHom x.2.symm)).isHomLift

/-- Unique lifting supplies the full universal property of a strongly cartesian arrow. -/
private theorem fiberObject_isStronglyCartesian_of_isHomLift
    (p : S ⥤ C) [Functor.IsDiscreteFibration p]
    {R T : C} {a b : S} {f : R ⟶ T} {φ : a ⟶ b}
    (hφ : p.IsHomLift f φ) : p.IsStronglyCartesian f φ := by
  obtain ⟨⟩ := hφ
  refine { universal_property' := ?_ }
  intro a' g φ' hφ'
  let l := IsDiscreteFibration.lift p g
  letI : p.IsHomLift g l.hom := l.isHomLift
  let composite : HomLift p (g ≫ p.map φ) :=
    ⟨l.domain, l.hom ≫ φ, IsHomLift.comp p g (p.map φ) l.hom φ⟩
  let original : HomLift p (g ≫ p.map φ) := ⟨a', φ', hφ'⟩
  have domain_eq : l.domain = a' :=
    congrArg HomLift.domain
      ((IsDiscreteFibration.homLiftSubsingleton (g ≫ p.map φ)).elim composite original)
  have hom_eq : l.hom ≫ φ = eqToHom domain_eq ≫ φ' :=
    fiberObjectHomLift_hom_eq p _ composite original
  refine ⟨eqToHom domain_eq.symm ≫ l.hom, ⟨inferInstance, ?_⟩, ?_⟩
  · show (eqToHom domain_eq.symm ≫ l.hom) ≫ φ = φ'
    rw [Category.assoc, hom_eq]
    simp
  · intro ψ hψ
    simpa only [eqToHom_refl, Category.id_comp] using
      fiberObjectHomLift_hom_eq p g ⟨a', ψ, hψ.1⟩
        ⟨a', eqToHom domain_eq.symm ≫ l.hom, inferInstance⟩

/-- The transparent restriction function used to assemble `fiberObjectPresheaf`. It is the
intrinsic reindexing function determined by unique lifting, so no auxiliary cleavage is selected.
Transparency lets category-of-elements morphisms expose their defining reindexing equality
without passing through a propositional computation theorem. -/
private noncomputable abbrev fiberObjectRestriction
    (p : S ⥤ C) [Functor.IsDiscreteFibration p] {U V : Cᵒᵖ} (f : U ⟶ V) :
    p.Fiber (unop U) ⟶ p.Fiber (unop V) :=
  TypeCat.ofHom (IsDiscreteFibration.reindexObj p f.unop)

/-- Raw restriction along an identity is the identity, by uniqueness of the identity lift. -/
private theorem fiberObjectRestriction_id
    (p : S ⥤ C) [Functor.IsDiscreteFibration p] (U : Cᵒᵖ) :
    fiberObjectRestriction p (𝟙 U) = 𝟙 (p.Fiber (unop U)) := by
  apply TypeCat.homEquiv.injective
  funext x
  apply Subtype.ext
  exact fiberObjectReindex_eq_of_isHomLift p (𝟙 (unop U)) x
    (𝟙 x.1) (IsHomLift.id x.2)

/-- Raw restriction of fiber objects is contravariantly functorial, by uniqueness of the
composite lift. -/
private theorem fiberObjectRestriction_comp
    (p : S ⥤ C) [Functor.IsDiscreteFibration p] {U V W : Cᵒᵖ}
    (f : U ⟶ V) (g : V ⟶ W) :
    fiberObjectRestriction p (f ≫ g) =
      fiberObjectRestriction p f ≫ fiberObjectRestriction p g := by
  apply TypeCat.homEquiv.injective
  funext x
  apply Subtype.ext
  exact fiberObjectReindex_eq_of_isHomLift p (g.unop ≫ f.unop) x
    (IsDiscreteFibration.cartesianHom p g.unop
      (IsDiscreteFibration.reindexObj p f.unop x) ≫
        IsDiscreteFibration.cartesianHom p f.unop x)
    (@IsHomLift.comp C S _ _ p _ _ _ _ _ _ g.unop f.unop _ _
      (fiberObjectCartesianHom_isHomLift p g.unop
        (IsDiscreteFibration.reindexObj p f.unop x))
      (fiberObjectCartesianHom_isHomLift p f.unop x))

end Implementation

/-- The presheaf `U ↦ p.Fiber U` of objects in the discrete fibers of `p`. Its restriction maps
are the uniquely determined object actions of cartesian reindexing.

The definition is reducible so that a morphism in its category of elements carries, without a
propositional rewrite, the equality identifying its source with the intrinsic reindexing object. -/
@[reducible, stacks 02Y2 "fiber-object presheaf"]
noncomputable def fiberObjectPresheaf
    (p : S ⥤ C) [Functor.IsDiscreteFibration p] : Cᵒᵖ ⥤ Type uS where
  obj U := p.Fiber (unop U)
  map f := Implementation.fiberObjectRestriction p f
  map_id U := Implementation.fiberObjectRestriction_id p U
  map_comp f g := Implementation.fiberObjectRestriction_comp p f g

/- Axiom audit: the object types are explicit and the restriction functions use the unique lift
supplied by `IsDiscreteFibration`; their non-`Prop` data depend only on `Classical.choice`.
The identity/composition laws are proved directly from lift uniqueness. -/

end FiberObjectPresheafImplementation

/-- The value of the fiber-object presheaf at `U` is the standard fiber over `unop U`. -/
@[simp]
theorem fiberObjectPresheaf.obj
    (p : S ⥤ C) [Functor.IsDiscreteFibration p] (U : Cᵒᵖ) :
    p.fiberObjectPresheaf.obj U = p.Fiber (unop U) := rfl
/- Proof strategy: unfold only the object projection of `fiberObjectPresheaf`. -/

/-- The restriction map of `fiberObjectPresheaf` evaluates to the intrinsic reindexing determined
by unique lifting. This is the canonical computation rule; no cleavage occurs in its surface. -/
@[simp]
theorem fiberObjectPresheaf.map_apply
    (p : S ⥤ C) [Functor.IsDiscreteFibration p]
    {U V : Cᵒᵖ} (f : U ⟶ V) (x : p.Fiber (unop U)) :
    p.fiberObjectPresheaf.map f x =
      IsDiscreteFibration.reindexObj p f.unop x := rfl
/- Proof strategy: unfold the map projection and the private restriction function. -/

/-- The restriction map of `fiberObjectPresheaf` may be computed with any cleavage.

This is the choice-independence specification: unique lifting identifies the supplied
cartesian lift with the intrinsic lift, including its domain object. -/
theorem fiberObjectPresheaf.map_eq_reindex
    (p : S ⥤ C) [Functor.IsDiscreteFibration p] (χ : p.Cleavage)
    {U V : Cᵒᵖ} (f : U ⟶ V) (x : p.Fiber (unop U)) :
    p.fiberObjectPresheaf.map f x = (f.unop)⁎[χ] x := by
  apply Subtype.ext
  exact Implementation.fiberObjectReindex_eq_of_isHomLift p f.unop x
    (χ.cartesianHom f.unop x) (χ.reindexLift f.unop x).isStronglyCartesian.toIsHomLift

namespace fiberObjectPresheaf

/-- A total morphism identifies the tautological fiber object of its codomain, reindexed along
its projected base map, with the tautological fiber object of its domain. -/
theorem tautologicalSection.naturality
    (p : S ⥤ C) [Functor.IsDiscreteFibration p]
    {x y : Sᵒᵖ} (f : x ⟶ y) :
    p.fiberObjectPresheaf.map (p.map f.unop).op ⟨x.unop, rfl⟩ =
      ⟨y.unop, rfl⟩ := by
  apply Subtype.ext
  exact Implementation.fiberObjectReindex_eq_of_isHomLift p (p.map f.unop)
    ⟨x.unop, rfl⟩ f.unop (IsHomLift.map f.unop)

/-- The tautological section of the fiber-object presheaf pulled back to the total category.
At a total object it records that object with its reflexive fiber witness. -/
@[stacks 02Y2 "tautological fiber-object section",
  stacks 04SI "tautological fiber-object section"]
noncomputable def tautologicalSection
  (p : S ⥤ C) [Functor.IsDiscreteFibration p] :
    (p.op ⋙ p.fiberObjectPresheaf).sections :=
  ⟨fun x => ⟨x.unop, rfl⟩,
    fun f => tautologicalSection.naturality p f⟩

/-- The tautological section evaluates to the displayed object in its own standard fiber. -/
@[simp]
theorem tautologicalSection.apply
    (p : S ⥤ C) [Functor.IsDiscreteFibration p] (x : Sᵒᵖ) :
    (tautologicalSection p).1 x = ⟨x.unop, rfl⟩ := rfl

end fiberObjectPresheaf

/-- The intrinsic cartesian arrow whose source is presented exactly as the value of
`fiberObjectPresheaf.map`. This transparent endpoint form is convenient for constructions out of
the category of elements. -/
@[stacks 02Y2 "intrinsic arrow for fiber-object restriction"]
noncomputable def fiberObjectPresheaf.cartesianHom
    (p : S ⥤ C) [Functor.IsDiscreteFibration p]
    {U V : Cᵒᵖ} (f : U ⟶ V) (x : p.Fiber (unop U)) :
    (p.fiberObjectPresheaf.map f x).1 ⟶ x.1 :=
  IsDiscreteFibration.cartesianHom p f.unop x

/- Axiom audit: the morphism is the explicit intrinsic cartesian arrow and its non-`Prop` payload
depends only on `Classical.choice`; no propositional computation theorem is used to align its
domain, and the presheaf laws in its endpoint type are proved above. -/

/-- `fiberObjectPresheaf.cartesianHom` is the intrinsic cartesian arrow selected by unique
lifting. -/
@[simp]
theorem fiberObjectPresheaf.cartesianHom.eq_intrinsic
    (p : S ⥤ C) [Functor.IsDiscreteFibration p]
    {U V : Cᵒᵖ} (f : U ⟶ V) (x : p.Fiber (unop U)) :
    fiberObjectPresheaf.cartesianHom p f x =
      IsDiscreteFibration.cartesianHom p f.unop x := rfl
/- Proof strategy: unfold `fiberObjectPresheaf.cartesianHom`; reducibility of
`fiberObjectPresheaf` aligns the source objects definitionally. -/

/-- The endpoint-aligned cartesian arrow is strongly cartesian over the displayed base
morphism. -/
instance fiberObjectPresheaf.cartesianHom.isStronglyCartesian
    (p : S ⥤ C) [Functor.IsDiscreteFibration p]
    {U V : Cᵒᵖ} (f : U ⟶ V) (x : p.Fiber (unop U)) :
    p.IsStronglyCartesian f.unop
      (fiberObjectPresheaf.cartesianHom p f x) := by
  exact Implementation.fiberObject_isStronglyCartesian_of_isHomLift p
    (Implementation.fiberObjectCartesianHom_isHomLift p f.unop x)
/- Proof strategy: derive the universal property directly from unique lifting. -/

/-- The projection of the endpoint-aligned cartesian arrow is the displayed base morphism, with
the endpoint transports stored by the two fiber objects. -/
@[simp]
theorem fiberObjectPresheaf.cartesianHom.map
    (p : S ⥤ C) [Functor.IsDiscreteFibration p]
    {U V : Cᵒᵖ} (f : U ⟶ V) (x : p.Fiber (unop U)) :
    p.map (fiberObjectPresheaf.cartesianHom p f x) =
      eqToHom (p.fiberObjectPresheaf.map f x).2 ≫
        f.unop ≫ eqToHom x.2.symm := by
  letI := Implementation.fiberObjectCartesianHom_isHomLift p f.unop x
  exact IsHomLift.fac' p f.unop (IsDiscreteFibration.cartesianHom p f.unop x)
/- Proof strategy: apply mathlib's `IsHomLift.fac'` to the defining lift package. -/

end Functor

end CategoryTheory
