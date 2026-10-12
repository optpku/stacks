/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.FiberedCategory.Fiber
public import Mathlib.CategoryTheory.IsomorphismClasses
public import stacks_project.Chap69.Lemma_69_13_2_IdealPower
public import stacks_project.Chap69.Lemma_69_17_2_Pullback
public import stacks_project.Chap69.Lemma_69_20_4_Pullback
public import stacks_project.Chap99.Lemma_99_10_1_Picard
public import stacks_project.Chap99.Situation_99_11_1_Pullback

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
theorem sectionFiber_lift_condition (f : X ⟶ B) (σ : B ⟶ X) (hσ : σ ≫ f = 𝟙 B)
    (τ : CohStack.SchemesOver B) :
    (τ.hom ≫ σ) ≫ f = 𝟙 (ofOver τ.left) ≫ τ.hom :=
  sorry

/-- The section `σ_T : T ⟶ X_T` of the fibre projection induced by `σ : B ⟶ X`. -/
def sectionFiber (f : X ⟶ B) (σ : B ⟶ X) (hσ : σ ≫ f = 𝟙 B)
    (τ : CohStack.SchemesOver B) : ofOver τ.left ⟶ CohStack.fiber f τ :=
  pullback.lift (τ.hom ≫ σ) (𝟙 (ofOver τ.left)) (sectionFiber_lift_condition f σ hσ τ)

/-- The composite of `σ_T` with the projection `X_T ⟶ X` is `T ⟶ B ⟶ X`. -/
theorem sectionFiber_fst (f : X ⟶ B) (σ : B ⟶ X) (hσ : σ ≫ f = 𝟙 B)
    (τ : CohStack.SchemesOver B) :
    sectionFiber f σ hσ τ ≫ pullback.fst f τ.hom = τ.hom ≫ σ :=
  sorry

/-- The composite of `σ_T` with the projection `X_T ⟶ T` is the identity of `T`. -/
theorem sectionFiber_snd (f : X ⟶ B) (σ : B ⟶ X) (hσ : σ ≫ f = 𝟙 B)
    (τ : CohStack.SchemesOver B) :
    sectionFiber f σ hσ τ ≫ pullback.snd f τ.hom = 𝟙 (ofOver τ.left) :=
  sorry

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
      Modules.picardClass ((Modules.pullback (sectionFiber f σ hσ τ)).obj L) :=
  sorry

/-- Naturality of `σ_T` in morphisms of schemes over `B`. -/
theorem sectionFiber_comp_fiberMap (f : X ⟶ B) (σ : B ⟶ X) (hσ : σ ≫ f = 𝟙 B)
    {τ ρ : CohStack.SchemesOver B} (h : τ ⟶ ρ) :
    sectionFiber f σ hσ τ ≫ CohStack.fiberMap f h =
      (ofOverFunctor S).map h.left ≫ sectionFiber f σ hσ ρ :=
  sorry

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
structure Obj (f : X ⟶ B) (σ : B ⟶ X) (hσ : σ ≫ f = 𝟙 B) where
  /-- The underlying Picard object `(T, h, L)`. -/
  toPicard : Picard.Obj f
  /-- The trivialization `α : O_T ≅ σ_T^* L`. -/
  trivialization :
    𝟙_ (ofOver toPicard.σ.left).Modules ≅
      (Modules.pullback (sectionFiber f σ hσ toPicard.σ)).obj toPicard.line

/-- Package an invertible module on a fibre together with a trivialization of
its pullback along `σ_T` as an object of `Obj f σ hσ`. -/
def ofLine {f : X ⟶ B} {σ : B ⟶ X} {hσ : σ ≫ f = 𝟙 B}
    (τ : CohStack.SchemesOver B) (L : (CohStack.fiber f τ).Modules)
    [isInvertibleObject L]
    (α : 𝟙_ (ofOver τ.left).Modules ≅
      (Modules.pullback (sectionFiber f σ hσ τ)).obj L) : Obj f σ hσ where
  toPicard := Picard.ofLine τ L
  trivialization := α

/-- The underlying Picard object of `ofLine τ L α` is `Picard.ofLine τ L`. -/
theorem ofLine_toPicard {f : X ⟶ B} {σ : B ⟶ X} {hσ : σ ≫ f = 𝟙 B}
    (τ : CohStack.SchemesOver B) (L : (CohStack.fiber f τ).Modules)
    [isInvertibleObject L]
    (α : 𝟙_ (ofOver τ.left).Modules ≅
      (Modules.pullback (sectionFiber f σ hσ τ)).obj L) :
    (ofLine τ L α).toPicard = Picard.ofLine τ L :=
  sorry

/-- The trivialization of `ofLine τ L α` is the supplied isomorphism `α`. -/
theorem ofLine_trivialization {f : X ⟶ B} {σ : B ⟶ X} {hσ : σ ≫ f = 𝟙 B}
    (τ : CohStack.SchemesOver B) (L : (CohStack.fiber f τ).Modules)
    [isInvertibleObject L]
    (α : 𝟙_ (ofOver τ.left).Modules ≅
      (Modules.pullback (sectionFiber f σ hσ τ)).obj L) :
    (ofLine τ L α).trivialization = α :=
  sorry

/-- The composite `σ_T^* φ ∘ g^* α'` as a morphism `(g)^* 𝟙_{T'} ⟶ σ_T^* L`. -/
def pulledTrivializationHom {f : X ⟶ B} {σ : B ⟶ X} {hσ : σ ≫ f = 𝟙 B}
    {x y : Obj f σ hσ} (φ : Picard.Hom x.toPicard y.toPicard) :
    (Modules.pullback ((ofOverFunctor S).map φ.base.left)).obj
        (𝟙_ (ofOver y.toPicard.σ.left).Modules) ⟶
      (Modules.pullback (sectionFiber f σ hσ x.toPicard.σ)).obj x.toPicard.line :=
  (Modules.pullback ((ofOverFunctor S).map φ.base.left)).map y.trivialization.hom ≫
    (sectionPullbackCompat f σ hσ φ.base).hom.app y.toPicard.line ≫
    (Modules.pullback (sectionFiber f σ hσ x.toPicard.σ)).map φ.iso.hom

/-- The canonical identification `g^* 𝒪_Y ≅ 𝒪_Z`, given by
`IdealSubobject.pullbackUnit` conjugated by `structureModuleIsoTensorUnit`. -/
def pullbackTensorUnitIso {Y Z : AlgebraicSpace S} (h : Z ⟶ Y) :
    (Modules.pullback h).obj (𝟙_ Y.Modules) ≅ 𝟙_ Z.Modules :=
  (Modules.pullback h).mapIso (Modules.structureModuleIsoTensorUnit Y).symm ≪≫
    { hom := IdealSubobject.pullbackUnit h
      inv := Modules.structureModulePullbackInv h
      hom_inv_id := sorry
      inv_hom_id := sorry } ≪≫
    Modules.structureModuleIsoTensorUnit Z

/-- The hom of `pullbackTensorUnitIso` is `IdealSubobject.pullbackUnit` conjugated
by `structureModuleIsoTensorUnit`. -/
theorem pullbackTensorUnitIso_hom {Y Z : AlgebraicSpace S} (h : Z ⟶ Y) :
    (pullbackTensorUnitIso h).hom =
      (Modules.pullback h).map (Modules.structureModuleIsoTensorUnit Y).inv ≫
        IdealSubobject.pullbackUnit h ≫
        (Modules.structureModuleIsoTensorUnit Z).hom :=
  sorry

/-- The canonical identification `g^* 𝒪_{T'} ≅ 𝒪_T` along the underlying map of a
Picard morphism. -/
def baseUnitIso {f : X ⟶ B} {σ : B ⟶ X} {hσ : σ ≫ f = 𝟙 B}
    {x y : Obj f σ hσ} (φ : Picard.Hom x.toPicard y.toPicard) :
    (Modules.pullback ((ofOverFunctor S).map φ.base.left)).obj
        (𝟙_ (ofOver y.toPicard.σ.left).Modules) ≅
      𝟙_ (ofOver x.toPicard.σ.left).Modules :=
  pullbackTensorUnitIso ((ofOverFunctor S).map φ.base.left)

/-- `baseUnitIso φ` is the canonical monoidal-unit pullback along `g`. -/
theorem baseUnitIso_eq {f : X ⟶ B} {σ : B ⟶ X} {hσ : σ ≫ f = 𝟙 B}
    {x y : Obj f σ hσ} (φ : Picard.Hom x.toPicard y.toPicard) :
    baseUnitIso φ = pullbackTensorUnitIso ((ofOverFunctor S).map φ.base.left) :=
  sorry

/-- The hom of `baseUnitIso` is `IdealSubobject.pullbackUnit` conjugated by
`structureModuleIsoTensorUnit`. -/
theorem baseUnitIso_hom {f : X ⟶ B} {σ : B ⟶ X} {hσ : σ ≫ f = 𝟙 B}
    {x y : Obj f σ hσ} (φ : Picard.Hom x.toPicard y.toPicard) :
    (baseUnitIso φ).hom =
      (pullbackTensorUnitIso ((ofOverFunctor S).map φ.base.left)).hom :=
  sorry

/-- The comparison of `α` with the canonical unit pullback `(g)^* 𝟙_{T'} ⟶ 𝟙_T`. -/
def baseTrivializationHom {f : X ⟶ B} {σ : B ⟶ X} {hσ : σ ≫ f = 𝟙 B}
    {x y : Obj f σ hσ} (φ : Picard.Hom x.toPicard y.toPicard) :
    (Modules.pullback ((ofOverFunctor S).map φ.base.left)).obj
        (𝟙_ (ofOver y.toPicard.σ.left).Modules) ⟶
      (Modules.pullback (sectionFiber f σ hσ x.toPicard.σ)).obj x.toPicard.line :=
  (baseUnitIso φ).hom ≫ x.trivialization.hom

/-- `baseTrivializationHom` precomposes `α` with the canonical `g^* 𝒪_{T'} ≅ 𝒪_T`. -/
theorem baseTrivializationHom_eq {f : X ⟶ B} {σ : B ⟶ X} {hσ : σ ≫ f = 𝟙 B}
    {x y : Obj f σ hσ} (φ : Picard.Hom x.toPicard y.toPicard) :
    baseTrivializationHom φ = (baseUnitIso φ).hom ≫ x.trivialization.hom :=
  sorry

/-- A morphism of Picard-with-section objects is a Picard morphism compatible
with the trivializations. -/
structure Hom {f : X ⟶ B} {σ : B ⟶ X} {hσ : σ ≫ f = 𝟙 B}
    (x y : Obj f σ hσ) where
  /-- The underlying morphism of Picard objects. -/
  toPicardHom : Picard.Hom x.toPicard y.toPicard
  /-- Compatibility `σ_T^* φ ∘ g^* α' = α` after identifying `g^* O_{T'}` with
  `O_T`. -/
  trivialization_compat :
    pulledTrivializationHom toPicardHom = baseTrivializationHom toPicardHom


/-- Build a Picard-with-section morphism from a Picard morphism and the
trivialization compatibility. -/
def homMk {f : X ⟶ B} {σ : B ⟶ X} {hσ : σ ≫ f = 𝟙 B} {x y : Obj f σ hσ}
    (φ : Picard.Hom x.toPicard y.toPicard)
    (hcompat : pulledTrivializationHom φ = baseTrivializationHom φ) : Hom x y where
  toPicardHom := φ
  trivialization_compat := hcompat

/-- The underlying Picard morphism of `homMk φ hcompat` is `φ`. -/
theorem homMk_toPicardHom {f : X ⟶ B} {σ : B ⟶ X} {hσ : σ ≫ f = 𝟙 B}
    {x y : Obj f σ hσ} (φ : Picard.Hom x.toPicard y.toPicard)
    (hcompat : pulledTrivializationHom φ = baseTrivializationHom φ) :
    (homMk φ hcompat).toPicardHom = φ :=
  sorry

/-- The identity Picard morphism is compatible with a trivialization. -/
theorem id_trivialization_compat {f : X ⟶ B} {σ : B ⟶ X} {hσ : σ ≫ f = 𝟙 B}
    (x : Obj f σ hσ) :
    pulledTrivializationHom (Picard.Hom.id x.toPicard) =
      baseTrivializationHom (Picard.Hom.id x.toPicard) :=
  sorry

/-- The identity morphism uses the identity Picard morphism. -/
def Hom.id {f : X ⟶ B} {σ : B ⟶ X} {hσ : σ ≫ f = 𝟙 B} (x : Obj f σ hσ) :
    Hom x x where
  toPicardHom := Picard.Hom.id x.toPicard
  trivialization_compat := id_trivialization_compat x

/-- Compatibility of a composite Picard morphism with trivializations. -/
theorem comp_trivialization_compat {f : X ⟶ B} {σ : B ⟶ X} {hσ : σ ≫ f = 𝟙 B}
    {x y z : Obj f σ hσ} (α : Hom x y) (β : Hom y z) :
    pulledTrivializationHom (Picard.Hom.comp α.toPicardHom β.toPicardHom) =
      baseTrivializationHom (Picard.Hom.comp α.toPicardHom β.toPicardHom) :=
  sorry

/-- Composition of morphisms is composition of the underlying Picard morphisms. -/
def Hom.comp {f : X ⟶ B} {σ : B ⟶ X} {hσ : σ ≫ f = 𝟙 B} {x y z : Obj f σ hσ}
    (α : Hom x y) (β : Hom y z) : Hom x z where
  toPicardHom := Picard.Hom.comp α.toPicardHom β.toPicardHom
  trivialization_compat := comp_trivialization_compat α β

/-- Quadruples `(T, h, L, α)` and compatible morphisms `(g, φ)` form a category. -/
instance category (f : X ⟶ B) (σ : B ⟶ X) (hσ : σ ≫ f = 𝟙 B) :
    Category (Obj f σ hσ) where
  Hom := Hom
  id := Hom.id
  comp := fun α β ↦ Hom.comp α β
  id_comp := sorry
  comp_id := sorry
  assoc := sorry

/-- The projection `(T, h, L, α) ↦ T` from `Obj f σ hσ` to `(Sch/S)`. -/
def p (f : X ⟶ B) (σ : B ⟶ X) (hσ : σ ≫ f = 𝟙 B) : Obj f σ hσ ⥤ Over S where
  obj x := x.toPicard.σ.left
  map α := α.toPicardHom.base.left
  map_id := sorry
  map_comp := sorry

/-- The object part of `p` is the underlying scheme over `S`. -/
theorem p_obj {f : X ⟶ B} {σ : B ⟶ X} {hσ : σ ≫ f = 𝟙 B} (x : Obj f σ hσ) :
    (p f σ hσ).obj x = x.toPicard.σ.left :=
  sorry

/-- The morphism part of `p` is the underlying morphism of schemes over `S`. -/
theorem p_map {f : X ⟶ B} {σ : B ⟶ X} {hσ : σ ≫ f = 𝟙 B} {x y : Obj f σ hσ}
    (α : x ⟶ y) : (p f σ hσ).map α = α.toPicardHom.base.left :=
  sorry

/-- The forgetful functor from Picard-with-section objects to Picard objects. -/
def forget (f : X ⟶ B) (σ : B ⟶ X) (hσ : σ ≫ f = 𝟙 B) :
    Obj f σ hσ ⥤ Picard.Obj f where
  obj x := x.toPicard
  map α := α.toPicardHom
  map_id := sorry
  map_comp := sorry

/-- The object part of `forget` is the underlying Picard object. -/
theorem forget_obj {f : X ⟶ B} {σ : B ⟶ X} {hσ : σ ≫ f = 𝟙 B} (x : Obj f σ hσ) :
    (forget f σ hσ).obj x = x.toPicard :=
  sorry

/-- The projection `p` is the forgetful functor followed by the Picard projection. -/
theorem p_eq_forget_comp (f : X ⟶ B) (σ : B ⟶ X) (hσ : σ ≫ f = 𝟙 B) :
    p f σ hσ = forget f σ hσ ⋙ Picard.p f :=
  sorry

/-- A class in the coproduct over `h : T ⟶ B` of `Ker(σ_T^* : Pic(X_T) → Pic(T))`. -/
structure IsoClass (f : X ⟶ B) (σ : B ⟶ X) (hσ : σ ≫ f = 𝟙 B) (T : Over S) where
  /-- The test scheme over `B` presenting the index `h : T ⟶ B`. -/
  test : CohStack.SchemesOver B
  /-- The underlying scheme of the test object is `T`. -/
  left_eq : test.left = T
  /-- The Picard class of the invertible module on the fibre `X ×_{B,h} T`. -/
  lineClass : (CohStack.fiber f test).PicardGroup
  /-- Membership in `Ker(σ_T^*)`. -/
  mem_ker : sectionPicard f σ hσ test lineClass = 0

/-- Package a kernel class of `σ_T^*` as an element of the coproduct of kernels. -/
def ofKernel {f : X ⟶ B} {σ : B ⟶ X} {hσ : σ ≫ f = 𝟙 B} {T : Over S}
    (h : ofOver T ⟶ B)
    (x : (CohStack.fiber f (CostructuredArrow.mk h)).PicardGroup)
    (hx : sectionPicard f σ hσ (CostructuredArrow.mk h) x = 0) :
    IsoClass f σ hσ T where
  test := CostructuredArrow.mk h
  left_eq := rfl
  lineClass := x
  mem_ker := hx

/-- The structure morphism `h : T ⟶ B` of a kernel class. -/
def IsoClass.hom {f : X ⟶ B} {σ : B ⟶ X} {hσ : σ ≫ f = 𝟙 B} {T : Over S}
    (c : IsoClass f σ hσ T) : ofOver T ⟶ B :=
  eqToHom (congrArg ofOver c.left_eq.symm) ≫ c.test.hom

/-- `IsoClass.hom` is the transported structure morphism of the stored test object. -/
theorem IsoClass.hom_eq {f : X ⟶ B} {σ : B ⟶ X} {hσ : σ ≫ f = 𝟙 B}
    {T : Over S} (c : IsoClass f σ hσ T) :
    c.hom = eqToHom (congrArg ofOver c.left_eq.symm) ≫ c.test.hom :=
  sorry

/-- The structure morphism of `ofKernel h x hx` is `h`. -/
theorem ofKernel_hom {f : X ⟶ B} {σ : B ⟶ X} {hσ : σ ≫ f = 𝟙 B} {T : Over S}
    (h : ofOver T ⟶ B)
    (x : (CohStack.fiber f (CostructuredArrow.mk h)).PicardGroup)
    (hx : sectionPicard f σ hσ (CostructuredArrow.mk h) x = 0) :
    (ofKernel h x hx).hom = h :=
  sorry

/-- Kernel membership is vanishing of `σ_T^*` on the stored Picard class. -/
theorem IsoClass.mem_iff {f : X ⟶ B} {σ : B ⟶ X} {hσ : σ ≫ f = 𝟙 B}
    {T : Over S} (c : IsoClass f σ hσ T) :
    sectionPicard f σ hσ c.test c.lineClass = 0 ↔
      picardPullback (sectionFiber f σ hσ c.test) c.lineClass = 0 :=
  sorry

/-- The Picard class of the line bundle of a Picard object. -/
def picardClassOfObj {f : X ⟶ B} (x : Picard.Obj f) :
    (CohStack.fiber f x.σ).PicardGroup :=
  @MonoidalCategory.PicardGroup.mk (CohStack.fiber f x.σ).Modules _ _ x.line x.invertible

/-- Kernel membership of the Picard class of a fibre object. -/
theorem isoClassOfFiber_mem_ker {f : X ⟶ B} {σ : B ⟶ X} {hσ : σ ≫ f = 𝟙 B}
    {T : Over S} (x : (p f σ hσ).Fiber T) :
    sectionPicard f σ hσ x.1.toPicard.σ (picardClassOfObj x.1.toPicard) = 0 :=
  sorry

/-- The kernel class associated to a fibre object over `T`. -/
def isoClassOfFiber {f : X ⟶ B} {σ : B ⟶ X} {hσ : σ ≫ f = 𝟙 B} {T : Over S}
    (x : (p f σ hσ).Fiber T) : IsoClass f σ hσ T where
  test := x.1.toPicard.σ
  left_eq := x.property
  lineClass := picardClassOfObj x.1.toPicard
  mem_ker := isoClassOfFiber_mem_ker x

/-- The test object of `isoClassOfFiber x` is the Picard test scheme of `x`. -/
theorem isoClassOfFiber_test {f : X ⟶ B} {σ : B ⟶ X} {hσ : σ ≫ f = 𝟙 B}
    {T : Over S} (x : (p f σ hσ).Fiber T) :
    (isoClassOfFiber x).test = x.1.toPicard.σ :=
  sorry

/-- The Picard class of `isoClassOfFiber x` is the class of the line on `x`. -/
theorem isoClassOfFiber_lineClass {f : X ⟶ B} {σ : B ⟶ X} {hσ : σ ≫ f = 𝟙 B}
    {T : Over S} (x : (p f σ hσ).Fiber T) :
    (isoClassOfFiber x).lineClass = picardClassOfObj x.1.toPicard :=
  sorry

/-- Isomorphic fibre objects determine the same kernel class. -/
theorem isoClassOfFiber_eq_of_isIsomorphic {f : X ⟶ B} {σ : B ⟶ X}
    {hσ : σ ≫ f = 𝟙 B} {T : Over S} {x y : (p f σ hσ).Fiber T}
    (h : IsIsomorphic x y) : isoClassOfFiber x = isoClassOfFiber y :=
  sorry

/-- A chosen trivialization of `σ_T^* L` extracted from kernel membership via
`picardClass_eq_iff`. -/
def IsoClass.trivialization {f : X ⟶ B} {σ : B ⟶ X} {hσ : σ ≫ f = 𝟙 B}
    {T : Over S} (c : IsoClass f σ hσ T) :
    𝟙_ (ofOver c.test.left).Modules ≅
      (Modules.pullback (sectionFiber f σ hσ c.test)).obj
        (PicardGroup.repr c.lineClass) :=
  Classical.choice <|
    (picardClass_eq_iff
        (𝟙_ (ofOver c.test.left).Modules)
        ((Modules.pullback (sectionFiber f σ hσ c.test)).obj
          (PicardGroup.repr c.lineClass))).mp
      (Eq.trans (MonoidalCategory.PicardGroup.mk_unit) c.mem_ker.symm)

/-- The chosen trivialization identifies `𝒪_T` with `σ_T^*` of a representative of
`c.lineClass`. -/
theorem IsoClass.trivialization_spec {f : X ⟶ B} {σ : B ⟶ X} {hσ : σ ≫ f = 𝟙 B}
    {T : Over S} (c : IsoClass f σ hσ T) :
    Modules.picardClass
        ((Modules.pullback (sectionFiber f σ hσ c.test)).obj
          (PicardGroup.repr c.lineClass)) =
      Modules.picardClass (𝟙_ (ofOver c.test.left).Modules) :=
  sorry

/-- A fibre object over `T` reconstructed from a kernel class. -/
def fiberOfIsoClass {f : X ⟶ B} {σ : B ⟶ X} {hσ : σ ≫ f = 𝟙 B} {T : Over S}
    (c : IsoClass f σ hσ T) : (p f σ hσ).Fiber T :=
  ⟨ofLine c.test (PicardGroup.repr c.lineClass) c.trivialization, c.left_eq⟩

/-- The reconstructed fibre object is `ofLine` of the stored test object,
representative, and trivialization. -/
theorem fiberOfIsoClass_eq {f : X ⟶ B} {σ : B ⟶ X} {hσ : σ ≫ f = 𝟙 B}
    {T : Over S} (c : IsoClass f σ hσ T) :
    (fiberOfIsoClass c).1 =
      ofLine c.test (PicardGroup.repr c.lineClass) c.trivialization :=
  sorry


end AlgebraicGeometry.AlgebraicSpace.Picard.WithSection
