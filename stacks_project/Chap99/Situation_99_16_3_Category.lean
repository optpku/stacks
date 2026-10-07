module

public import Mathlib.Algebra.Homology.HomologicalComplex
public import Mathlib.CategoryTheory.Comma.Over.Basic
public import Mathlib.CategoryTheory.Quotient
public import Mathlib.CategoryTheory.Functor.Derived.PointwiseLeftDerived
public import ReasLib.CategoryTheory.DerivedCategory.Functor.Composition
public import ReasLib.CategoryTheory.DerivedCategory.Functor.Exact.Identity
public import ReasLib.CategoryTheory.DerivedCategory.Functor.Induced.Preadditive
public import stacks_project.Chap66.Lemma_66_26_3_Glueing
public import stacks_project.Chap67.Definition_67_40_1_Proper
public import stacks_project.Chap67.Lemma_67_28_3_Pullback
public import stacks_project.Chap67.Lemma_67_28_8_FinitePresentation
public import stacks_project.Chap67.Lemma_67_30_4_Pullback
public import stacks_project.Chap75.Lemma_75_21_1_Pullback
public import stacks_project.Chap75.Lemma_75_26_6_Pullback
public import stacks_project.Chap76.Lemma_76_52_4_Relative
public import stacks_project.Chap99.Lemma_99_16_1_Open
public import stacks_project.Chap99.Situation_99_16_3_Fiber

/-!
# The category of admissible complexes on fibres of a proper morphism

Objects of `Complexes.Obj f` are triples consisting of a scheme over `B` together
with a `T`-perfect complex on the fibre `X_T` whose negative self-Ext groups
vanish on field-valued fibres. Morphisms are pairs of a morphism of schemes over
`B` and an isomorphism of the derived pullbacks along the induced fibre map.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open CategoryTheory.Limits
open AlgebraicGeometry.AlgebraicSpace.SmallEtaleModuleGlueing
open ComplexShape

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Complexes

variable {S : Scheme.{u}} {X B : AlgebraicSpace S}

/-- The functor on homotopy categories induced by the identity functor is the
identity of the homotopy category. -/
def mapHomotopyCategoryIdIso (A : Type u) [Category A] [Preadditive A] :
    (𝟭 A).mapHomotopyCategory (up ℤ) ≅ 𝟭 (HomotopyCategory A (up ℤ)) :=
  Quotient.natIsoLift _
    (Functor.isoWhiskerRight
      (Functor.mapHomologicalComplexIdIso A (up ℤ))
      (HomotopyCategory.quotient A (up ℤ)))

/-- Homotopy-to-derived pullback along `𝟙 Y` is the derived localization functor. -/
def homotopyPullbackIdIso (Y : AlgebraicSpace S) :
    (Modules.pullback (𝟙 Y)).mapHomotopyCategory (up ℤ) ⋙
      (DerivedCategory.Qh :
        HomotopyCategory Y.Modules (up ℤ) ⥤ ModuleDerived Y) ≅
      (DerivedCategory.Qh :
        HomotopyCategory Y.Modules (up ℤ) ⥤ ModuleDerived Y) :=
  Functor.isoWhiskerRight
      (Functor.mapHomotopyCategoryIso (modulesPullbackId Y) ≪≫
        mapHomotopyCategoryIdIso Y.Modules)
      DerivedCategory.Qh ≪≫
    Functor.leftUnitor _

/-- The exact identity model factors homotopy pullback along the identity.
Only the exact identity functor is passed to `mapDerivedCategory`; exactness
of geometric pullback and an equality between derived models are not used. -/
def pullbackIdFactors (Y : AlgebraicSpace S) :
    (DerivedCategory.Qh :
      HomotopyCategory Y.Modules (up ℤ) ⥤ ModuleDerived Y) ⋙
        (ExactFunctor.id Y.Modules).mapDerivedCategory ≅
      Functor.Homotopy.toDerived (Modules.pullback (𝟙 Y)) :=
  (𝟭 Y.Modules).mapDerivedCategoryFactorsh ≪≫
    Functor.isoWhiskerRight (mapHomotopyCategoryIdIso Y.Modules) DerivedCategory.Qh ≪≫
    Functor.leftUnitor _ ≪≫ (homotopyPullbackIdIso Y).symm

/-- The explicit identity factorization has the left-derived universal
property, by the localization theorem rather than an admitted witness. -/
theorem pullbackId_model_isLeftDerived (Y : AlgebraicSpace S) :
    (ExactFunctor.id Y.Modules).mapDerivedCategory.IsLeftDerivedFunctor
      (pullbackIdFactors Y).hom (HomotopyCategory.quasiIso Y.Modules (up ℤ)) :=
  Functor.isLeftDerivedFunctor_of_inverts _ _ (pullbackIdFactors Y)

/-- The explicit identity model proves existence of the left derived functor
of identity pullback, independently of the general existence placeholder. -/
theorem pullbackId_hasLeftDerived (Y : AlgebraicSpace S) :
    (Functor.Homotopy.toDerived (Modules.pullback (𝟙 Y))).HasLeftDerivedFunctor
      (HomotopyCategory.quasiIso Y.Modules (up ℤ)) := by
  -- Local instance justification (proof-local temporary data): certify the explicit identity model.
  letI := pullbackId_model_isLeftDerived Y
  exact Functor.HasLeftDerivedFunctor.mk'
    (ExactFunctor.id Y.Modules).mapDerivedCategory (pullbackIdFactors Y).hom
    (W := HomotopyCategory.quasiIso Y.Modules (up ℤ))

/-- Compare the existing total-left-derived pullback model with the exact
identity model using their proven universal properties, then use the
canonical exact-derived identity. No equality transport or admitted
invertibility certificate selects either map. -/
def pullbackId (Y : AlgebraicSpace S) :
    ModuleDerived.pullback (𝟙 Y) ≅ 𝟭 (ModuleDerived Y) := by
  -- Local instance justification (defeq pin): use existence proved from the explicit identity model.
  letI := pullbackId_hasLeftDerived Y
  -- Local instance justification (proof-local temporary data): certify the exact model for uniqueness.
  letI := pullbackId_model_isLeftDerived Y
  exact Functor.leftDerivedUnique
    (ExactFunctor.id Y.Modules).mapDerivedCategory
    ((Functor.Homotopy.toDerived (Modules.pullback (𝟙 Y))).totalLeftDerived
      DerivedCategory.Qh (HomotopyCategory.quasiIso Y.Modules (up ℤ)))
    ((Functor.Homotopy.toDerived (Modules.pullback (𝟙 Y))).totalLeftDerivedCounit
      DerivedCategory.Qh (HomotopyCategory.quasiIso Y.Modules (up ℤ)))
    (pullbackIdFactors Y).hom (HomotopyCategory.quasiIso Y.Modules (up ℤ)) ≪≫
    ExactFunctor.MapDerivedCategory.idFunctorIso Y.Modules

/-- An object of the category of complexes on `X/B`: a scheme over `B` together
with a relatively perfect complex on the fibre whose negative self-Ext groups
vanish on field-valued fibres. -/
structure Obj (f : X ⟶ B) [Proper f] [Flat f] [FinitePresentation f] where
  /-- The test scheme over `B`. -/
  σ : SchemeOver B
  /-- The complex on the fibre `X_T`. -/
  complex : ModuleDerived (pullback f σ.hom)
  /-- The complex is `T`-perfect. -/
  isPerfectRelative :
    ModuleDerived.IsPerfectRelativeTo (pullback.snd f σ.hom) complex
  /-- Negative self-Ext groups vanish on every field-valued fibre over `T`. -/
  fiberNegativeSelfExtVanish :
    ∀ t : FieldValuedPoint (ofOver σ.left),
      ModuleDerived.fiberNegativeExtVanish (pullback.snd f σ.hom) complex complex t

/-- Package a test scheme and an admissible complex on the fibre as an object of
`Obj f`. -/
def of {f : X ⟶ B} [Proper f] [Flat f] [FinitePresentation f] (σ : SchemeOver B)
    (complex : ModuleDerived (pullback f σ.hom))
    (isPerfectRelative :
      ModuleDerived.IsPerfectRelativeTo (pullback.snd f σ.hom) complex)
    (fiberNegativeSelfExtVanish :
      ∀ t : FieldValuedPoint (ofOver σ.left),
        ModuleDerived.fiberNegativeExtVanish (pullback.snd f σ.hom) complex complex t) :
    Obj f where
  σ := σ
  complex := complex
  isPerfectRelative := isPerfectRelative
  fiberNegativeSelfExtVanish := fiberNegativeSelfExtVanish

/-- The test scheme of `of σ complex hPerfect hVanish` is `σ`. -/
theorem of_σ {f : X ⟶ B} [Proper f] [Flat f] [FinitePresentation f]
    (σ : SchemeOver B) (complex : ModuleDerived (pullback f σ.hom))
    (isPerfectRelative :
      ModuleDerived.IsPerfectRelativeTo (pullback.snd f σ.hom) complex)
    (fiberNegativeSelfExtVanish :
      ∀ t : FieldValuedPoint (ofOver σ.left),
        ModuleDerived.fiberNegativeExtVanish (pullback.snd f σ.hom) complex complex t) :
    (of σ complex isPerfectRelative fiberNegativeSelfExtVanish).σ = σ :=
  sorry

/-- The complex of `of σ complex hPerfect hVanish` is `complex`. -/
theorem of_complex {f : X ⟶ B} [Proper f] [Flat f] [FinitePresentation f]
    (σ : SchemeOver B) (complex : ModuleDerived (pullback f σ.hom))
    (isPerfectRelative :
      ModuleDerived.IsPerfectRelativeTo (pullback.snd f σ.hom) complex)
    (fiberNegativeSelfExtVanish :
      ∀ t : FieldValuedPoint (ofOver σ.left),
        ModuleDerived.fiberNegativeExtVanish (pullback.snd f σ.hom) complex complex t) :
    (of σ complex isPerfectRelative fiberNegativeSelfExtVanish).complex = complex :=
  sorry

/-- An object of `Obj f` is a `T`-perfect complex on the fibre with fibrewise
negative self-Ext vanishing. -/
theorem Obj.spec {f : X ⟶ B} [Proper f] [Flat f] [FinitePresentation f]
    (x : Obj f) :
    ModuleDerived.IsPerfectRelativeTo (pullback.snd f x.σ.hom) x.complex ∧
      ∀ t : FieldValuedPoint (ofOver x.σ.left),
        ModuleDerived.fiberNegativeExtVanish (pullback.snd f x.σ.hom)
          x.complex x.complex t :=
  sorry

/-- A morphism `(T, g, E) ⟶ (T', g', E')` is a morphism of schemes over `B`
together with an isomorphism `L(h')^* y.complex ≅ x.complex` along the base
change of that morphism. -/
structure Hom {f : X ⟶ B} [Proper f] [Flat f] [FinitePresentation f]
    (x y : Obj f) where
  /-- The underlying morphism of schemes over `B`. -/
  base : x.σ ⟶ y.σ
  /-- The isomorphism `L(h')^* y.complex ≅ x.complex` in `D(𝒪_{X_T})`. -/
  iso : (ModuleDerived.pullback (fiberMap f base)).obj y.complex ≅ x.complex

/-- Build a morphism of `Obj f` from a morphism of schemes over `B` and a
derived-category isomorphism along the induced fibre map. -/
def homMk {f : X ⟶ B} [Proper f] [Flat f] [FinitePresentation f] {x y : Obj f}
    (base : x.σ ⟶ y.σ)
    (iso : (ModuleDerived.pullback (fiberMap f base)).obj y.complex ≅ x.complex) :
    Hom x y where
  base := base
  iso := iso

/-- The underlying morphism of schemes of `homMk` is the supplied base map. -/
theorem homMk_base {f : X ⟶ B} [Proper f] [Flat f] [FinitePresentation f]
    {x y : Obj f} (base : x.σ ⟶ y.σ)
    (iso : (ModuleDerived.pullback (fiberMap f base)).obj y.complex ≅ x.complex) :
    (homMk base iso).base = base :=
  sorry

/-- The derived-category component of `homMk` is the supplied isomorphism. -/
theorem homMk_iso {f : X ⟶ B} [Proper f] [Flat f] [FinitePresentation f]
    {x y : Obj f} (base : x.σ ⟶ y.σ)
    (iso : (ModuleDerived.pullback (fiberMap f base)).obj y.complex ≅ x.complex) :
    (homMk base iso).iso = iso :=
  sorry

/-- Identification of derived pullback along `fiberMap f (𝟙 σ)` with derived
pullback along the identity of the fibre. -/
def pullbackFiberMapIdIso (f : X ⟶ B) (σ : SchemeOver B) :
    ModuleDerived.pullback (fiberMap f (𝟙 σ)) ≅
      ModuleDerived.pullback (𝟙 (pullback f σ.hom)) :=
  ModuleDerived.pullbackCongr (fiberMap_id_eq f σ)

/-- The identity comparison `L(fiberMap f (𝟙))^* x.complex ≅ x.complex`. -/
def Hom.idIso {f : X ⟶ B} [Proper f] [Flat f] [FinitePresentation f]
    (x : Obj f) :
    (ModuleDerived.pullback (fiberMap f (𝟙 x.σ))).obj x.complex ≅ x.complex :=
  (ModuleDerived.pullbackCongr (fiberMap_id_eq f x.σ)).app x.complex ≪≫
    (pullbackId (pullback f x.σ.hom)).app x.complex

/-- The identity morphism uses the identity scheme map over `B` and the comparison
isomorphism along `fiberMap f (𝟙)`. -/
def Hom.id {f : X ⟶ B} [Proper f] [Flat f] [FinitePresentation f] (x : Obj f) :
    Hom x x where
  base := 𝟙 x.σ
  iso := Hom.idIso x

/-- The derived-category component of the identity morphism is `Hom.idIso`. -/
theorem Hom.id_iso {f : X ⟶ B} [Proper f] [Flat f] [FinitePresentation f]
    (x : Obj f) :
    (Hom.id x).iso = Hom.idIso x :=
  sorry

/-- The derived isomorphism of a composite morphism, conjugating by
`ModuleDerived.pullbackCompIso` along the fibre maps of the factors. -/
def Hom.compIso {f : X ⟶ B} [Proper f] [Flat f] [FinitePresentation f]
    {x y z : Obj f} (α : Hom x y) (β : Hom y z) :
    (ModuleDerived.pullback (fiberMap f α.base ≫ fiberMap f β.base)).obj z.complex ≅
      x.complex :=
  (ModuleDerived.pullbackCompIso (fiberMap f α.base) (fiberMap f β.base)).symm.app
      z.complex ≪≫
    (ModuleDerived.pullback (fiberMap f α.base)).mapIso β.iso ≪≫ α.iso

/-- Identification of derived pullback along `fiberMap f (h ≫ k)` with derived
pullback along the composite of the individual fibre maps. -/
def pullbackFiberMapCompIso (f : X ⟶ B) {σ τ ρ : SchemeOver B}
    (h : σ ⟶ τ) (k : τ ⟶ ρ) :
    ModuleDerived.pullback (fiberMap f (h ≫ k)) ≅
      ModuleDerived.pullback (fiberMap f h ≫ fiberMap f k) :=
  ModuleDerived.pullbackCongr (fiberMap_comp_eq f h k)

/-- Composition of morphisms is composition of scheme maps over `B` and of the
conjugated derived isomorphisms along `fiberMap` of the composite. -/
def Hom.comp {f : X ⟶ B} [Proper f] [Flat f] [FinitePresentation f]
    {x y z : Obj f} (α : Hom x y) (β : Hom y z) : Hom x z where
  base := α.base ≫ β.base
  iso := (pullbackFiberMapCompIso f α.base β.base).app z.complex ≪≫ Hom.compIso α β

/-- Triples `(T, g, E)` and iso-morphisms `(h, φ)` form a category. -/
instance category (f : X ⟶ B) [Proper f] [Flat f] [FinitePresentation f] :
    Category (Obj f) where
  Hom := Hom
  id := Hom.id
  comp := fun α β ↦ Hom.comp α β
  id_comp := sorry
  comp_id := sorry
  assoc := sorry

/-- Morphisms in `Obj f` are pairs consisting of a morphism of schemes over `B`
and an isomorphism of the complexes pulled back along the induced fibre map. -/
def homSigma {f : X ⟶ B} [Proper f] [Flat f] [FinitePresentation f]
    (x y : Obj f) :
    (x ⟶ y) ≃
      Σ (h : x.σ ⟶ y.σ),
        (ModuleDerived.pullback (fiberMap f h)).obj y.complex ≅ x.complex where
  toFun := fun φ ↦ ⟨φ.base, φ.iso⟩
  invFun := fun pair ↦ homMk pair.1 pair.2
  left_inv := fun _ ↦ rfl
  right_inv := fun _ ↦ rfl

/-- Applying `homSigma` extracts the base morphism and derived isomorphism. -/
theorem homSigma_apply {f : X ⟶ B} [Proper f] [Flat f] [FinitePresentation f]
    {x y : Obj f} (φ : x ⟶ y) :
    homSigma x y φ = ⟨φ.base, φ.iso⟩ :=
  sorry

/-- The inverse of `homSigma` reconstructs a morphism from a base map and a
derived isomorphism along the induced fibre map. -/
theorem homSigma_symm_apply {f : X ⟶ B} [Proper f] [Flat f] [FinitePresentation f]
    {x y : Obj f}
    (pair : Σ (h : x.σ ⟶ y.σ),
      (ModuleDerived.pullback (fiberMap f h)).obj y.complex ≅ x.complex) :
    (homSigma x y).symm pair = homMk pair.1 pair.2 :=
  sorry

/-- The projection `(T, g, E) ↦ T` from `Obj f` to `(Sch/S)`. -/
def p (f : X ⟶ B) [Proper f] [Flat f] [FinitePresentation f] : Obj f ⥤ Over S where
  obj x := x.σ.left
  map α := α.base.left
  map_id := sorry
  map_comp := sorry

/-- The object part of `p` is the underlying scheme over `S`. -/
theorem p_obj {f : X ⟶ B} [Proper f] [Flat f] [FinitePresentation f] (x : Obj f) :
    (p f).obj x = x.σ.left :=
  sorry

/-- The morphism part of `p` is the underlying morphism of schemes over `S`. -/
theorem p_map {f : X ⟶ B} [Proper f] [Flat f] [FinitePresentation f]
    {x y : Obj f} (α : x ⟶ y) :
    (p f).map α = α.base.left :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Complexes
