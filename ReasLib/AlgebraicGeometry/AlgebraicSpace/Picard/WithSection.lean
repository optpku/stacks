module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Picard.Category
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Picard.Pullback
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Pullback.Tensor

/-!
# Picard category of a morphism of algebraic spaces with a chosen section

Objects are quadruples `(T, h, L, α)` consisting of a Picard object of `f`
together with a trivialization `α : O_T ≅ σ_T^* L` of the pullback along the
section of the fibre. Morphisms are Picard morphisms compatible with the
trivializations.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.Picard
open CategoryTheory.Limits CategoryTheory.MonoidalCategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Picard.WithSection

variable {S : Scheme.{u}} {X B : AlgebraicSpace S}

/-- The cone equality exhibiting `σ_T` as a section of `X_T ⟶ T`. -/
private theorem sectionFiberLiftCondition (f : X ⟶ B) (σ : B ⟶ X) (hσ : σ ≫ f = 𝟙 B)
    (τ : CohStack.SchemesOver B) :
    (τ.hom ≫ σ) ≫ f = 𝟙 (ofOver τ.left) ≫ τ.hom := sorry

/-- The section `σ_T : T ⟶ X_T` of the fibre projection induced by `σ : B ⟶ X`. -/
@[no_expose] def sectionFiber (f : X ⟶ B) (σ : B ⟶ X) (hσ : σ ≫ f = 𝟙 B)
    (τ : CohStack.SchemesOver B) : ofOver τ.left ⟶ CohStack.fiber f τ :=
  pullback.lift (τ.hom ≫ σ) (𝟙 (ofOver τ.left)) (sectionFiberLiftCondition f σ hσ τ)

/-- The composite of `σ_T` with the projection `X_T ⟶ X` is `T ⟶ B ⟶ X`. -/
theorem sectionFiber_fst (f : X ⟶ B) (σ : B ⟶ X) (hσ : σ ≫ f = 𝟙 B)
    (τ : CohStack.SchemesOver B) :
    sectionFiber f σ hσ τ ≫ pullback.fst f τ.hom = τ.hom ≫ σ := sorry

/-- The composite of `σ_T` with the projection `X_T ⟶ T` is the identity of `T`. -/
theorem sectionFiber_snd (f : X ⟶ B) (σ : B ⟶ X) (hσ : σ ≫ f = 𝟙 B)
    (τ : CohStack.SchemesOver B) :
    sectionFiber f σ hσ τ ≫ pullback.snd f τ.hom = 𝟙 (ofOver τ.left) := sorry

/-- The pullback `σ_T^* : Pic(X_T) →+ Pic(T)` on Picard groups. -/
def sectionPicard (f : X ⟶ B) (σ : B ⟶ X) (hσ : σ ≫ f = 𝟙 B)
    (τ : CohStack.SchemesOver B) :
    (CohStack.fiber f τ).PicardGroup →+ (ofOver τ.left).PicardGroup :=
  picardPullback (sectionFiber f σ hσ τ)

/-- `sectionPicard` sends the class of an invertible module to the class of its
pullback along `σ_T`. -/
theorem sectionPicard_apply_class (f : X ⟶ B) (σ : B ⟶ X) (hσ : σ ≫ f = 𝟙 B)
    (τ : CohStack.SchemesOver B) (L : (CohStack.fiber f τ).Modules)
    [isInvertibleObject L] :
    sectionPicard f σ hσ τ (Modules.picardClass L) =
      Modules.picardClass ((Modules.pullback (sectionFiber f σ hσ τ)).obj L) := sorry

/-- Naturality of `σ_T` in morphisms of schemes over `B`. -/
theorem sectionFiber_comp_fiberMap (f : X ⟶ B) (σ : B ⟶ X) (hσ : σ ≫ f = 𝟙 B)
    {τ ρ : CohStack.SchemesOver B} (h : τ ⟶ ρ) :
    sectionFiber f σ hσ τ ≫ CohStack.fiberMap f h =
      (ofOverFunctor S).map h.left ≫ sectionFiber f σ hσ ρ := sorry

/-- Identification `g^* σ_{T'}^* ≅ σ_T^* (fiberMap)^*` of module pullbacks. -/
def sectionPullbackCompat (f : X ⟶ B) (σ : B ⟶ X) (hσ : σ ≫ f = 𝟙 B)
    {τ ρ : CohStack.SchemesOver B} (h : τ ⟶ ρ) :
    Modules.pullback (sectionFiber f σ hσ ρ) ⋙
        Modules.pullback ((ofOverFunctor S).map h.left) ≅
      Modules.pullback (CohStack.fiberMap f h) ⋙
        Modules.pullback (sectionFiber f σ hσ τ) :=
  Modules.pullbackCompIso ((ofOverFunctor S).map h.left) (sectionFiber f σ hσ ρ) ≪≫
    eqToIso (congrArg Modules.pullback (sectionFiber_comp_fiberMap f σ hσ h).symm) ≪≫
    (Modules.pullbackCompIso (sectionFiber f σ hσ τ) (CohStack.fiberMap f h)).symm

/-- An object of the Picard category of `f` with section `σ`: a Picard object
together with a trivialization of `σ_T^* L`. -/
structure Object (f : X ⟶ B) (σ : B ⟶ X) (hσ : σ ≫ f = 𝟙 B) where
  /-- The underlying Picard object `(T, h, L)`. -/
  toPicard : Picard.Obj f
  /-- The trivialization `α : O_T ≅ σ_T^* L`. -/
  trivialization :
    𝟙_ (ofOver toPicard.σ.left).Modules ≅
      (Modules.pullback (sectionFiber f σ hσ toPicard.σ)).obj toPicard.line

/-- Package an invertible module on a fibre together with a trivialization of
its pullback along `σ_T` as an object of `Object f σ hσ`. -/
def Object.ofLine {f : X ⟶ B} {σ : B ⟶ X} {hσ : σ ≫ f = 𝟙 B}
    (τ : CohStack.SchemesOver B) (L : (CohStack.fiber f τ).Modules)
    [isInvertibleObject L]
    (α : 𝟙_ (ofOver τ.left).Modules ≅
      (Modules.pullback (sectionFiber f σ hσ τ)).obj L) : Object f σ hσ where
  toPicard := Picard.ofLine τ L
  trivialization := α

/-- The composite `σ_T^* φ ∘ g^* α'` as a morphism `(g)^* 𝟙_{T'} ⟶ σ_T^* L`. -/
def pulledTrivializationHom {f : X ⟶ B} {σ : B ⟶ X} {hσ : σ ≫ f = 𝟙 B}
    {x y : Object f σ hσ} (φ : Picard.Hom x.toPicard y.toPicard) :
    (Modules.pullback ((ofOverFunctor S).map φ.base.left)).obj
        (𝟙_ (ofOver y.toPicard.σ.left).Modules) ⟶
      (Modules.pullback (sectionFiber f σ hσ x.toPicard.σ)).obj x.toPicard.line :=
  (Modules.pullback ((ofOverFunctor S).map φ.base.left)).map y.trivialization.hom ≫
    (sectionPullbackCompat f σ hσ φ.base).hom.app y.toPicard.line ≫
    (Modules.pullback (sectionFiber f σ hσ x.toPicard.σ)).map φ.iso.hom

/-- The comparison of `α` with the canonical unit pullback `(g)^* 𝟙_{T'} ⟶ 𝟙_T`. -/
def baseTrivializationHom {f : X ⟶ B} {σ : B ⟶ X} {hσ : σ ≫ f = 𝟙 B}
    {x y : Object f σ hσ} (φ : Picard.Hom x.toPicard y.toPicard) :
    (Modules.pullback ((ofOverFunctor S).map φ.base.left)).obj
        (𝟙_ (ofOver y.toPicard.σ.left).Modules) ⟶
      (Modules.pullback (sectionFiber f σ hσ x.toPicard.σ)).obj x.toPicard.line :=
  (Modules.PullbackTensor.unitIso ((ofOverFunctor S).map φ.base.left)).hom ≫ x.trivialization.hom

/-- A morphism of Picard-with-section objects is a Picard morphism compatible
with the trivializations. -/
structure Hom {f : X ⟶ B} {σ : B ⟶ X} {hσ : σ ≫ f = 𝟙 B}
    (x y : Object f σ hσ) where
  /-- The underlying morphism of Picard objects. -/
  toPicardHom : Picard.Hom x.toPicard y.toPicard
  /-- Compatibility `σ_T^* φ ∘ g^* α' = α` after identifying `g^* O_{T'}` with
  `O_T`. -/
  trivialization_compat :
    pulledTrivializationHom toPicardHom = baseTrivializationHom toPicardHom

/-- Build a Picard-with-section morphism from a Picard morphism and the
trivialization compatibility. -/
def homMk {f : X ⟶ B} {σ : B ⟶ X} {hσ : σ ≫ f = 𝟙 B} {x y : Object f σ hσ}
    (φ : Picard.Hom x.toPicard y.toPicard)
    (hcompat : pulledTrivializationHom φ = baseTrivializationHom φ) : Hom x y where
  toPicardHom := φ
  trivialization_compat := hcompat

/-- The identity Picard morphism is compatible with a trivialization. -/
private theorem idTrivializationCompat {f : X ⟶ B} {σ : B ⟶ X} {hσ : σ ≫ f = 𝟙 B}
    (x : Object f σ hσ) :
    pulledTrivializationHom (Picard.Hom.id x.toPicard) =
      baseTrivializationHom (Picard.Hom.id x.toPicard) := sorry

/-- The identity morphism uses the identity Picard morphism. -/
@[no_expose] def Hom.id {f : X ⟶ B} {σ : B ⟶ X} {hσ : σ ≫ f = 𝟙 B} (x : Object f σ hσ) :
    Hom x x where
  toPicardHom := Picard.Hom.id x.toPicard
  trivialization_compat := idTrivializationCompat x

/-- Compatibility of a composite Picard morphism with trivializations. -/
private theorem compTrivializationCompat {f : X ⟶ B} {σ : B ⟶ X} {hσ : σ ≫ f = 𝟙 B}
    {x y z : Object f σ hσ} (α : Hom x y) (β : Hom y z) :
    pulledTrivializationHom (Picard.Hom.comp α.toPicardHom β.toPicardHom) =
      baseTrivializationHom (Picard.Hom.comp α.toPicardHom β.toPicardHom) := sorry

/-- Composition of morphisms is composition of the underlying Picard morphisms. -/
@[no_expose] def Hom.comp {f : X ⟶ B} {σ : B ⟶ X} {hσ : σ ≫ f = 𝟙 B} {x y z : Object f σ hσ}
    (α : Hom x y) (β : Hom y z) : Hom x z where
  toPicardHom := Picard.Hom.comp α.toPicardHom β.toPicardHom
  trivialization_compat := compTrivializationCompat α β

/-- Composing with an identity on the left preserves a compatible morphism. -/
theorem Hom.id_comp {f : X ⟶ B} {σ : B ⟶ X} {hσ : σ ≫ f = 𝟙 B}
    {x y : Object f σ hσ} (α : Hom x y) : Hom.comp (Hom.id x) α = α := sorry

/-- Composing with an identity on the right preserves a compatible morphism. -/
theorem Hom.comp_id {f : X ⟶ B} {σ : B ⟶ X} {hσ : σ ≫ f = 𝟙 B}
    {x y : Object f σ hσ} (α : Hom x y) : Hom.comp α (Hom.id y) = α := sorry

/-- Composition of compatible morphisms is associative. -/
theorem Hom.assoc {f : X ⟶ B} {σ : B ⟶ X} {hσ : σ ≫ f = 𝟙 B}
    {w x y z : Object f σ hσ} (α : Hom w x) (β : Hom x y) (γ : Hom y z) :
    Hom.comp (Hom.comp α β) γ = Hom.comp α (Hom.comp β γ) := sorry

/-- The category of invertible modules with a trivialization along the section. -/
def category (f : X ⟶ B) (σ : B ⟶ X) (hσ : σ ≫ f = 𝟙 B) :
    Cat.{u + 1, u + 1} :=
  ⟨Object f σ hσ, {
    Hom := Hom
    id := Hom.id
    comp := fun α β ↦ Hom.comp α β
    id_comp := Hom.id_comp
    comp_id := Hom.comp_id
    assoc := Hom.assoc
  }⟩

/-- The carrier of the section-rigidified Picard category. -/
abbrev Obj (f : X ⟶ B) (σ : B ⟶ X) (hσ : σ ≫ f = 𝟙 B) : Type (u + 1) :=
  category f σ hσ

/-- Construct a rigidified Picard object from an invertible module and its trivialization. -/
def ofLine {f : X ⟶ B} {σ : B ⟶ X} {hσ : σ ≫ f = 𝟙 B}
    (τ : CohStack.SchemesOver B) (L : (CohStack.fiber f τ).Modules)
    [isInvertibleObject L]
    (α : 𝟙_ (ofOver τ.left).Modules ≅
      (Modules.pullback (sectionFiber f σ hσ τ)).obj L) : Obj f σ hσ :=
  Object.ofLine τ L α

/-- The constructed object retains both the supplied Picard object and trivialization. -/
theorem ofLine_spec {f : X ⟶ B} {σ : B ⟶ X} {hσ : σ ≫ f = 𝟙 B}
    (τ : CohStack.SchemesOver B) (L : (CohStack.fiber f τ).Modules)
    [isInvertibleObject L]
    (α : 𝟙_ (ofOver τ.left).Modules ≅
      (Modules.pullback (sectionFiber f σ hσ τ)).obj L) :
    (ofLine τ L α).toPicard = Picard.ofLine τ L ∧
      (ofLine τ L α).trivialization = α := sorry

/-- The constructed morphism retains its supplied map and satisfies trivialization compatibility. -/
theorem homMk_spec {f : X ⟶ B} {σ : B ⟶ X} {hσ : σ ≫ f = 𝟙 B}
    {x y : Object f σ hσ} (φ : Picard.Hom x.toPicard y.toPicard)
    (hcompat : pulledTrivializationHom φ = baseTrivializationHom φ) :
    (homMk φ hcompat).toPicardHom = φ ∧
      pulledTrivializationHom (homMk φ hcompat).toPicardHom =
        baseTrivializationHom (homMk φ hcompat).toPicardHom := sorry

/-- The identity compatible morphism projects to the identity of its test scheme. -/
theorem pMapId {f : X ⟶ B} {σ : B ⟶ X} {hσ : σ ≫ f = 𝟙 B}
    (x : Obj f σ hσ) : (Hom.id x).toPicardHom.base.left = 𝟙 x.toPicard.σ.left := sorry

/-- Composition of compatible morphisms projects to composition of test-scheme maps. -/
theorem pMapComp {f : X ⟶ B} {σ : B ⟶ X} {hσ : σ ≫ f = 𝟙 B}
    {x y z : Obj f σ hσ} (α : x ⟶ y) (β : y ⟶ z) :
    (Hom.comp α β).toPicardHom.base.left =
      α.toPicardHom.base.left ≫ β.toPicardHom.base.left := sorry

/-- The projection sending a rigidified invertible module to its test scheme. -/
def p (f : X ⟶ B) (σ : B ⟶ X) (hσ : σ ≫ f = 𝟙 B) : Obj f σ hσ ⥤ Over S where
  obj x := x.toPicard.σ.left
  map α := α.toPicardHom.base.left
  map_id := pMapId
  map_comp := fun α β ↦ pMapComp α β

/-- The object part of the projection is the underlying scheme over the base. -/
theorem p_obj {f : X ⟶ B} {σ : B ⟶ X} {hσ : σ ≫ f = 𝟙 B} (x : Obj f σ hσ) :
    (p f σ hσ).obj x = x.toPicard.σ.left := sorry

/-- The morphism part of the projection is the underlying map of test schemes. -/
theorem p_map {f : X ⟶ B} {σ : B ⟶ X} {hσ : σ ≫ f = 𝟙 B} {x y : Obj f σ hσ}
    (α : x ⟶ y) : (p f σ hσ).map α = α.toPicardHom.base.left := sorry

/-- Forgetting the trivialization preserves identity morphisms. -/
theorem forgetMapId {f : X ⟶ B} {σ : B ⟶ X} {hσ : σ ≫ f = 𝟙 B}
    (x : Obj f σ hσ) : (Hom.id x).toPicardHom = Picard.Hom.id x.toPicard := sorry

/-- Forgetting the trivialization preserves composition. -/
theorem forgetMapComp {f : X ⟶ B} {σ : B ⟶ X} {hσ : σ ≫ f = 𝟙 B}
    {x y z : Obj f σ hσ} (α : x ⟶ y) (β : y ⟶ z) :
    (Hom.comp α β).toPicardHom = Picard.Hom.comp α.toPicardHom β.toPicardHom := sorry

/-- The functor forgetting the trivialization along the section. -/
def forget (f : X ⟶ B) (σ : B ⟶ X) (hσ : σ ≫ f = 𝟙 B) :
    Obj f σ hσ ⥤ Picard.Obj f where
  obj x := x.toPicard
  map α := α.toPicardHom
  map_id := forgetMapId
  map_comp := fun α β ↦ forgetMapComp α β

/-- Forgetting the trivialization retains the underlying Picard object. -/
theorem forget_obj {f : X ⟶ B} {σ : B ⟶ X} {hσ : σ ≫ f = 𝟙 B}
    (x : Obj f σ hσ) : (forget f σ hσ).obj x = x.toPicard := sorry

/-- Projection agrees with forgetting the trivialization followed by Picard projection. -/
theorem p_eq_forget_comp (f : X ⟶ B) (σ : B ⟶ X) (hσ : σ ≫ f = 𝟙 B) :
    p f σ hσ = forget f σ hσ ⋙ Picard.p f := sorry

end AlgebraicGeometry.AlgebraicSpace.Picard.WithSection
