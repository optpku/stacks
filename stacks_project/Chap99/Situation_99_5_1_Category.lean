module

public import Mathlib.CategoryTheory.Comma.Over.Basic
public import ReasLib.AlgebraicGeometry.Scheme.Module.Flat
public import stacks_project.Chap66.«66_26_1_1_Restrict»
public import stacks_project.Chap66.Definition_66_18_9_Square
public import stacks_project.Chap66.Lemma_66_4_2_Comparison
public import stacks_project.Chap66.Lemma_66_26_3_Glueing
public import stacks_project.Chap66.Proposition_66_32_1_Comparison
public import stacks_project.Chap67.Lemma_67_28_8_FinitePresentation
public import stacks_project.Chap69.Lemma_69_11_2_Flat_base_change_BaseChange
public import stacks_project.Chap76.«76_42_5_1_ProperSupport»
public import stacks_project.Chap99.Situation_99_5_1_Fiber

/-!
# The category of finitely presented modules with proper support on fibres

Objects of `CohStack.Obj f` are triples consisting of a scheme over `B`, together
with a finitely presented module on the fibre `X_T` that is flat over `T` with
support proper over `T`. Morphisms are pairs of a morphism of schemes over `B`
and an isomorphism of the pulled-back modules along the induced fibre map.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open CategoryTheory.Limits

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.CohStack

variable {S : Scheme.{u}} {X B : AlgebraicSpace S}

/-- A module on `Y` is flat over `Z` at a point `x` if some étale scheme square
presents the restricted module as relatively flat at a germ mapping to `x`. -/
def flatOverAt {Y Z : AlgebraicSpace S} (F : Y.Modules) (f : Y ⟶ Z) (x : Points Y) : Prop :=
  ∃ (sq : EtaleSquare f) (u : sq.left.left.left),
    Points.map sq.left.hom (ofOver.pointsEquiv sq.left.left u) = x ∧
      Scheme.Modules.flatOverAt
        ((@Modules.restrictFunctor S _ _ sq.left.hom sq.left.prop ⋙
            (schemeEtaleRingedHom sq.left.left).modulePushforward.{u} ⋙
              (smallEtaleToOpensRingedHom sq.left.left.left).modulePushforward.{u} ⋙
                opensToSchemeModules sq.left.left.left).obj F)
        sq.map.left u

/-- A module on `Y` is flat over `Z` along `f` if it is flat at every point of `Y`. -/
def flatOver {Y Z : AlgebraicSpace S} (F : Y.Modules) (f : Y ⟶ Z) : Prop :=
  ∀ x : Points Y, flatOverAt F f x

/-- Pointwise relative flatness unpacks as the existence of an étale scheme
presentation whose restricted module is relatively flat at a matching germ. -/
theorem flatOverAt_iff {Y Z : AlgebraicSpace S} (F : Y.Modules) (f : Y ⟶ Z) (x : Points Y) :
    flatOverAt F f x ↔
      ∃ (sq : EtaleSquare f) (u : sq.left.left.left),
        Points.map sq.left.hom (ofOver.pointsEquiv sq.left.left u) = x ∧
          Scheme.Modules.flatOverAt
            ((@Modules.restrictFunctor S _ _ sq.left.hom sq.left.prop ⋙
                (schemeEtaleRingedHom sq.left.left).modulePushforward.{u} ⋙
                  (smallEtaleToOpensRingedHom sq.left.left.left).modulePushforward.{u} ⋙
                    opensToSchemeModules sq.left.left.left).obj F)
            sq.map.left u := sorry

/-- Global relative flatness is the pointwise condition at every point of the source. -/
theorem flatOver_iff {Y Z : AlgebraicSpace S} (F : Y.Modules) (f : Y ⟶ Z) :
    flatOver F f ↔ ∀ x : Points Y, flatOverAt F f x := sorry

/-- Successive module pullbacks along fibre maps identify with pullback along
their composite, as the left-adjoint mate `Modules.pullbackCompIso`. -/
def fiberMapCompIso (f : X ⟶ B) {σ τ ρ : SchemesOver B} (h : σ ⟶ τ) (k : τ ⟶ ρ) :
    Modules.pullback (fiberMap f h ≫ fiberMap f k) ≅
      Modules.pullback (fiberMap f k) ⋙ Modules.pullback (fiberMap f h) :=
  (Modules.pullbackCompIso (fiberMap f h) (fiberMap f k)).symm

/-- An object of the category of coherent sheaves on `X/B`: a scheme over `B`
together with a finitely presented module on the fibre, flat over the test
scheme, with support proper over the test scheme. -/
structure Obj (f : X ⟶ B) [FinitePresentation f] where
  /-- The test scheme over `B`. -/
  σ : SchemesOver B
  /-- The module on the fibre `X_T`. -/
  module : (fiber f σ).Modules
  /-- The module is of finite presentation. -/
  isFinitePresentation : module.IsFinitePresentation
  /-- The module is flat over the test scheme. -/
  isFlat : flatOver module (fiberToBase f σ)
  /-- The support of the module is proper over the test scheme. -/
  hasProperSupport : Modules.HasProperSupportOver (fiberToBase f σ) module

/-- Package a test scheme and a finitely presented flat module with proper
support as an object of `Obj f`. -/
def Obj.of {f : X ⟶ B} [FinitePresentation f] (σ : SchemesOver B)
    (module : (fiber f σ).Modules) [module.IsFinitePresentation]
    [Modules.HasProperSupportOver (fiberToBase f σ) module]
    (isFlat : flatOver module (fiberToBase f σ)) : Obj f where
  σ := σ
  module := module
  isFinitePresentation := inferInstance
  isFlat := isFlat
  hasProperSupport := inferInstance

/-- The test scheme of `Obj.of σ module isFlat` is `σ`. -/
theorem Obj.of_σ {f : X ⟶ B} [FinitePresentation f] (σ : SchemesOver B)
    (module : (fiber f σ).Modules) [module.IsFinitePresentation]
    [Modules.HasProperSupportOver (fiberToBase f σ) module]
    (isFlat : flatOver module (fiberToBase f σ)) :
    (Obj.of σ module isFlat).σ = σ := sorry

/-- The module of `Obj.of σ module isFlat` is `module`. -/
theorem Obj.of_module {f : X ⟶ B} [FinitePresentation f] (σ : SchemesOver B)
    (module : (fiber f σ).Modules) [module.IsFinitePresentation]
    [Modules.HasProperSupportOver (fiberToBase f σ) module]
    (isFlat : flatOver module (fiberToBase f σ)) :
    (Obj.of σ module isFlat).module = module := sorry

/-- An object of `Obj f` is a quasi-coherent finitely presented module on the
fibre, flat over the test scheme, with support proper over the test scheme. -/
theorem Obj.spec {f : X ⟶ B} [FinitePresentation f] (x : Obj f) :
    x.module.IsQuasicoherent ∧ x.module.IsFinitePresentation ∧
      flatOver x.module (fiberToBase f x.σ) ∧
      Modules.HasProperSupportOver (fiberToBase f x.σ) x.module := sorry

/-- For a finitely presented module on a fibre, proper support over the test
scheme is properness of the scheme-theoretic support. -/
theorem hasProperSupport_iff {f : X ⟶ B} [FinitePresentation f] (σ : SchemesOver B)
    (F : (fiber f σ).Modules) [F.IsFinitePresentation] :
    Modules.HasProperSupportOver (fiberToBase f σ) F ↔
      Proper ((Modules.schemeTheoreticSupport F).ι ≫ fiberToBase f σ) := sorry

/-- A morphism `(T, g, F) ⟶ (T', g', F')` is a morphism of schemes over `B`
together with an isomorphism `(h')^* y.module ≅ x.module` along the base change
of that morphism. -/
structure Hom {f : X ⟶ B} [FinitePresentation f] (x y : Obj f) where
  /-- The underlying morphism of schemes over `B`. -/
  base : x.σ ⟶ y.σ
  /-- The isomorphism `(h')^* y.module ≅ x.module` of modules on the fibre. -/
  iso : (Modules.pullback (fiberMap f base)).obj y.module ≅ x.module

/-- Build a morphism of `Obj f` from a morphism of schemes over `B` and a
module isomorphism along the induced fibre map. -/
def homMk {f : X ⟶ B} [FinitePresentation f] {x y : Obj f} (base : x.σ ⟶ y.σ)
    (iso : (Modules.pullback (fiberMap f base)).obj y.module ≅ x.module) : Hom x y where
  base := base
  iso := iso

/-- The underlying morphism of schemes of `homMk` is the supplied base map. -/
theorem homMk_base {f : X ⟶ B} [FinitePresentation f] {x y : Obj f} (base : x.σ ⟶ y.σ)
    (iso : (Modules.pullback (fiberMap f base)).obj y.module ≅ x.module) :
    (homMk base iso).base = base := sorry

/-- The module component of `homMk` is the supplied isomorphism. -/
theorem homMk_iso {f : X ⟶ B} [FinitePresentation f] {x y : Obj f} (base : x.σ ⟶ y.σ)
    (iso : (Modules.pullback (fiberMap f base)).obj y.module ≅ x.module) :
    (homMk base iso).iso = iso := sorry

/-- `fiberMap f (𝟙 σ)` is the identity on the fibre, by uniqueness of maps into
a pullback together with `yoneda.map_id`. -/
def fiberMap_id_eq (f : X ⟶ B) (σ : SchemesOver B) :
    fiberMap f (𝟙 σ) = 𝟙 (fiber f σ) :=
  pullback.hom_ext
    (((pullback.lift_fst _ _ _).trans (Category.comp_id (pullback.fst f σ.hom))).trans
      (Category.id_comp (pullback.fst f σ.hom)).symm)
    (((pullback.lift_snd _ _ _).trans
        ((congrArg (fun i => pullback.snd f σ.hom ≫ i)
            (CategoryTheory.Functor.map_id yoneda σ.left)).trans
          (Category.comp_id (pullback.snd f σ.hom)))).trans
      (Category.id_comp (pullback.snd f σ.hom)).symm)

/-- Identification of module pullback along `fiberMapIdIso.hom` with pullback along
the identity morphism of the fibre. -/
def pullbackFiberMapIdIso (f : X ⟶ B) (σ : SchemesOver B) :
    Modules.pullback (fiberMapIdIso f σ).hom ≅ Modules.pullback (𝟙 (fiber f σ)) :=
  eqToIso (congrArg Modules.pullback (fiberMap_id_eq f σ))

/-- The identity comparison `(fiberMap f (𝟙))^* x.module ≅ x.module`, obtained by
transporting `modulesPullbackId` along `fiberMapIdIso.hom`. -/
def Hom.idIso {f : X ⟶ B} [FinitePresentation f] (x : Obj f) :
    (Modules.pullback (fiberMap f (𝟙 x.σ))).obj x.module ≅ x.module :=
  (pullbackFiberMapIdIso f x.σ).app x.module ≪≫
    (SmallEtaleModuleGlueing.modulesPullbackId (fiber f x.σ)).app x.module

/-- The identity morphism uses the identity scheme map over `B` and the comparison
isomorphism along `fiberMap f (𝟙)`. -/
def Hom.id {f : X ⟶ B} [FinitePresentation f] (x : Obj f) : Hom x x where
  base := 𝟙 x.σ
  iso := Hom.idIso x

/-- The module isomorphism of a composite morphism, conjugating by
`Modules.pullbackCompIso` along the fibre maps of the factors. -/
def Hom.compIso {f : X ⟶ B} [FinitePresentation f] {x y z : Obj f}
    (α : Hom x y) (β : Hom y z) :
    (Modules.pullback (fiberMap f α.base ≫ fiberMap f β.base)).obj z.module ≅ x.module :=
  (Modules.pullbackCompIso (fiberMap f α.base) (fiberMap f β.base)).symm.app z.module ≪≫
    (Modules.pullback (fiberMap f α.base)).mapIso β.iso ≪≫ α.iso

/-- `fiberMap` is functorial on morphisms of schemes over `B`, by uniqueness of
maps into a pullback together with `yoneda.map_comp`. -/
def fiberMap_comp_eq (f : X ⟶ B) {σ τ ρ : SchemesOver B} (h : σ ⟶ τ) (k : τ ⟶ ρ) :
    fiberMap f (h ≫ k) = fiberMap f h ≫ fiberMap f k :=
  pullback.hom_ext
    (Eq.trans
      (Eq.trans (pullback.lift_fst _ _ _) (Category.comp_id (pullback.fst f σ.hom)))
      (Eq.symm
        (Eq.trans
          (Eq.symm (Category.assoc (fiberMap f h) (fiberMap f k) (pullback.fst f ρ.hom)))
          (Eq.trans
            (congrArg (fun φ => fiberMap f h ≫ φ)
              (Eq.trans (pullback.lift_fst _ _ _)
                (Category.comp_id (pullback.fst f τ.hom))))
            (Eq.trans (pullback.lift_fst _ _ _)
              (Category.comp_id (pullback.fst f σ.hom)))))))
    (Eq.trans (pullback.lift_snd _ _ _)
      (Eq.trans
        (congrArg (fun i => pullback.snd f σ.hom ≫ i)
          (CategoryTheory.Functor.map_comp yoneda h.left k.left))
        (Eq.trans
          (Eq.symm
            (Category.assoc (pullback.snd f σ.hom) ((ofOverFunctor S).map h.left)
              ((ofOverFunctor S).map k.left)))
          (Eq.trans
            (congrArg (fun φ => φ ≫ (ofOverFunctor S).map k.left)
              (Eq.symm (pullback.lift_snd _ _ _)))
            (Eq.trans
              (Category.assoc (fiberMap f h) (pullback.snd f τ.hom)
                ((ofOverFunctor S).map k.left))
              (Eq.trans
                (congrArg (fun φ => fiberMap f h ≫ φ)
                  (Eq.symm (pullback.lift_snd _ _ _)))
                (Category.assoc (fiberMap f h) (fiberMap f k)
                  (pullback.snd f ρ.hom))))))))

/-- Identification of module pullback along `fiberMap f (h ≫ k)` with pullback
along the composite of the individual fibre maps. -/
def pullbackFiberMapCompIso (f : X ⟶ B) {σ τ ρ : SchemesOver B} (h : σ ⟶ τ) (k : τ ⟶ ρ) :
    Modules.pullback (fiberMap f (h ≫ k)) ≅
      Modules.pullback (fiberMap f h ≫ fiberMap f k) :=
  eqToIso (congrArg Modules.pullback (fiberMap_comp_eq f h k))

/-- Composition of morphisms is composition of scheme maps over `B` and of
the conjugated module isomorphisms along `fiberMap` of the composite. -/
def Hom.comp {f : X ⟶ B} [FinitePresentation f] {x y z : Obj f}
    (α : Hom x y) (β : Hom y z) : Hom x z where
  base := α.base ≫ β.base
  iso := (pullbackFiberMapCompIso f α.base β.base).app z.module ≪≫ Hom.compIso α β

/-- Triples `(T, g, F)` and iso-morphisms `(h, φ)` form a category. -/
instance category (f : X ⟶ B) [FinitePresentation f] : Category (Obj f) where
  Hom := Hom
  id := Hom.id
  comp := fun α β ↦ Hom.comp α β
  id_comp := sorry
  comp_id := sorry
  assoc := sorry

/-- Morphisms in `Obj f` are pairs consisting of a morphism of schemes over `B`
and an isomorphism of the modules pulled back along the induced fibre map. -/
def homSigma {f : X ⟶ B} [FinitePresentation f] (x y : Obj f) :
    (x ⟶ y) ≃
      Σ (h : x.σ ⟶ y.σ),
        (Modules.pullback (fiberMap f h)).obj y.module ≅ x.module where
  toFun := fun φ ↦ ⟨φ.base, φ.iso⟩
  invFun := fun pair ↦ homMk pair.1 pair.2
  left_inv := fun _ ↦ rfl
  right_inv := fun _ ↦ rfl

/-- Applying `homSigma` extracts the base morphism and module isomorphism. -/
theorem homSigma_apply {f : X ⟶ B} [FinitePresentation f] {x y : Obj f} (φ : x ⟶ y) :
    homSigma x y φ = ⟨φ.base, φ.iso⟩ := sorry

/-- The inverse of `homSigma` reconstructs a morphism from a base map and a
module isomorphism along the induced fibre map. -/
theorem homSigma_symm_apply {f : X ⟶ B} [FinitePresentation f] {x y : Obj f}
    (pair : Σ (h : x.σ ⟶ y.σ),
      (Modules.pullback (fiberMap f h)).obj y.module ≅ x.module) :
    (homSigma x y).symm pair = homMk pair.1 pair.2 := sorry

/-- The projection `(T, g, F) ↦ T` from `Obj f` to `(Sch/S)`. -/
def p (f : X ⟶ B) [FinitePresentation f] : Obj f ⥤ Over S where
  obj x := x.σ.left
  map α := α.base.left
  map_id := sorry
  map_comp := sorry

/-- The object part of `p` is the underlying scheme over `S`. -/
theorem p_obj {f : X ⟶ B} [FinitePresentation f] (x : Obj f) :
    (p f).obj x = x.σ.left := sorry

/-- The morphism part of `p` is the underlying morphism of schemes over `S`. -/
theorem p_map {f : X ⟶ B} [FinitePresentation f] {x y : Obj f} (α : x ⟶ y) :
    (p f).map α = α.base.left := sorry

end AlgebraicGeometry.AlgebraicSpace.CohStack
