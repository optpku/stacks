module

public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.CategoryTheory.FiberedCategory.Fiber
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Pasting
public import ReasLib.AlgebraicGeometry.Scheme.Module.Ample.Relative.BaseChange
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FinitePresentation.Operations
public import ReasLib.AlgebraicGeometry.Polarized

/-!
# Restriction of polarized families

Scheme-theoretic base change of a polarized family `(X ⟶ S', L)` along a morphism
of bases `S ⟶ S'`, and the induced restriction functors on Polarized fibre
categories.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry CategoryTheory.Limits
open CategoryTheory.Functor

noncomputable section

universe u

namespace AlgebraicGeometry.Polarized

/-- The projection `pullback.snd x.hom u` is proper. -/
def instIsProper_pullback_snd (x : Obj) {S : Scheme.{u}} (u : S ⟶ x.S) :
    IsProper (pullback.snd x.hom u) :=
  MorphismProperty.pullback_snd x.hom u x.isProper

/-- The projection `pullback.snd x.hom u` is flat. -/
def instFlat_pullback_snd (x : Obj) {S : Scheme.{u}} (u : S ⟶ x.S) :
    Flat (pullback.snd x.hom u) :=
  MorphismProperty.pullback_snd x.hom u x.isFlat

/-- The projection `pullback.snd x.hom u` is of finite presentation. -/
def instFinitePresentation_pullback_snd (x : Obj) {S : Scheme.{u}} (u : S ⟶ x.S) :
    Scheme.Hom.FinitePresentation (pullback.snd x.hom u) :=
  Scheme.Hom.FinitePresentation.pullback_snd x.finitePresentation u

/-- The pullback of a relatively ample line along `pullback.fst` remains relatively ample. -/
def instRelativelyAmple_pullback (x : Obj) {S : Scheme.{u}} (u : S ⟶ x.S) :
    RelativelyAmple (pullback.snd x.hom u)
      ((Scheme.Modules.pullback (pullback.fst x.hom u)).obj x.line) :=
  RelativelyAmple.of_isPullback (IsPullback.of_hasPullback x.hom u) x.relativelyAmple

/-- Scheme-theoretic base change of a polarized family along a morphism of bases. -/
def restrictObj (x : Obj) {S : Scheme.{u}} (u : S ⟶ x.S) : Obj :=
  @of _ _ (pullback.snd x.hom u)
    ((Scheme.Modules.pullback (pullback.fst x.hom u)).obj x.line)
    (instIsProper_pullback_snd x u) (instFlat_pullback_snd x u)
    (instFinitePresentation_pullback_snd x u) (instRelativelyAmple_pullback x u)

/-- The source of `restrictObj x u` is the fibre product of `x.hom` along `u`. -/
theorem restrictObj_X (x : Obj) {S : Scheme.{u}} (u : S ⟶ x.S) :
    (restrictObj x u).X = pullback x.hom u :=
  sorry

/-- The base of `restrictObj x u` is the source of `u`. -/
theorem restrictObj_S (x : Obj) {S : Scheme.{u}} (u : S ⟶ x.S) :
    (restrictObj x u).S = S :=
  sorry

/-- The structure morphism of `restrictObj x u` is the projection `pullback.snd`. -/
theorem restrictObj_hom (x : Obj) {S : Scheme.{u}} (u : S ⟶ x.S) :
    (restrictObj x u).hom = pullback.snd x.hom u :=
  sorry

/-- The line bundle of `restrictObj x u` is the pullback of `x.line` along `pullback.fst`. -/
theorem restrictObj_line (x : Obj) {S : Scheme.{u}} (u : S ⟶ x.S) :
    (restrictObj x u).line =
      (Scheme.Modules.pullback (pullback.fst x.hom u)).obj x.line :=
  sorry

/-- Restriction of polarized objects along equal base morphisms is isomorphic. -/
def restrictObjCongr (x : Obj) {S : Scheme.{u}} {u v : S ⟶ x.S} (huv : u = v) :
    restrictObj x u ≅ restrictObj x v :=
  eqToIso (congrArg (restrictObj x) huv)

/-- Commutativity of the lifted cospan for base change of a polarized morphism. -/
def restrictMap_w {x y : Obj} (φ : x ⟶ y) {S : Scheme.{u}} (u : S ⟶ x.S) :
    (pullback.fst x.hom u ≫ φ.map) ≫ y.hom =
      pullback.snd x.hom u ≫ (u ≫ φ.base) :=
  (Category.assoc (pullback.fst x.hom u) φ.map y.hom).trans
    ((congrArg (pullback.fst x.hom u ≫ ·) φ.isPullback.w).trans
      ((Category.assoc (pullback.fst x.hom u) x.hom φ.base).symm.trans
        ((congrArg (· ≫ φ.base)
            (pullback.condition :
              pullback.fst x.hom u ≫ x.hom = pullback.snd x.hom u ≫ u)).trans
          (Category.assoc (pullback.snd x.hom u) u φ.base))))

/-- The source map of the polarized morphism induced by base change of a cartesian
square. -/
def restrictMap_src {x y : Obj} (φ : x ⟶ y) {S : Scheme.{u}} (u : S ⟶ x.S) :
    (restrictObj x u).X ⟶ (restrictObj y (u ≫ φ.base)).X :=
  pullback.lift (pullback.fst x.hom u ≫ φ.map) (pullback.snd x.hom u) (restrictMap_w φ u)

/-- `restrictMap_src` commutes with the projections to the original sources. -/
def restrictMap_src_fst {x y : Obj} (φ : x ⟶ y) {S : Scheme.{u}} (u : S ⟶ x.S) :
    restrictMap_src φ u ≫ pullback.fst y.hom (u ≫ φ.base) =
      pullback.fst x.hom u ≫ φ.map :=
  pullback.lift_fst (pullback.fst x.hom u ≫ φ.map) (pullback.snd x.hom u) (restrictMap_w φ u)

/-- Base change of a cartesian polarized morphism gives a cartesian square over the new base. -/
theorem restrictMap_isPullback {x y : Obj} (φ : x ⟶ y) {S : Scheme.{u}} (u : S ⟶ x.S) :
    IsPullback (restrictMap_src φ u) (restrictObj x u).hom
      (restrictObj y (u ≫ φ.base)).hom (𝟙 S) := sorry

/-- Base change of a polarized morphism along a map into the source base. -/
def restrictMap {x y : Obj} (φ : x ⟶ y) {S : Scheme.{u}} (u : S ⟶ x.S) :
    restrictObj x u ⟶ restrictObj y (u ≫ φ.base) :=
  homMk (restrictMap_src φ u) (𝟙 S) (restrictMap_isPullback φ u)
    ((Scheme.Modules.pullbackComp (restrictMap_src φ u)
        (pullback.fst y.hom (u ≫ φ.base))).app y.line ≪≫
      (Scheme.Modules.pullbackCongr (restrictMap_src_fst φ u)).app y.line ≪≫
      (Scheme.Modules.pullbackComp (pullback.fst x.hom u) φ.map).symm.app y.line ≪≫
      (Scheme.Modules.pullback (pullback.fst x.hom u)).mapIso φ.iso)

/-- The source map of `restrictMap` is `restrictMap_src`. -/
theorem restrictMap_map {x y : Obj} (φ : x ⟶ y) {S : Scheme.{u}} (u : S ⟶ x.S) :
    (restrictMap φ u).map = restrictMap_src φ u :=
  sorry

/-- The base of `restrictMap` is the identity of the new base. -/
theorem restrictMap_base {x y : Obj} (φ : x ⟶ y) {S : Scheme.{u}} (u : S ⟶ x.S) :
    (restrictMap φ u).base = 𝟙 S :=
  sorry

/-- The source map of iterated restriction, as the canonical pasting isomorphism
`(X ×_{x.S} S') ×_{S'} S ≅ X ×_{x.S} S`. -/
def restrictObj_comp_hom_map (x : Obj) {S S' : Scheme.{u}} (u : S' ⟶ x.S) (v : S ⟶ S') :
    (restrictObj (restrictObj x u) v).X ⟶ (restrictObj x (v ≫ u)).X :=
  (pullbackLeftPullbackSndIso x.hom u v).hom

/-- The inverse source map of iterated restriction. -/
def restrictObj_comp_inv_map (x : Obj) {S S' : Scheme.{u}} (u : S' ⟶ x.S) (v : S ⟶ S') :
    (restrictObj x (v ≫ u)).X ⟶ (restrictObj (restrictObj x u) v).X :=
  (pullbackLeftPullbackSndIso x.hom u v).inv

/-- Line-bundle comparison for the forward map of iterated restriction. -/
def restrictObj_comp_hom_iso (x : Obj) {S S' : Scheme.{u}} (u : S' ⟶ x.S) (v : S ⟶ S') :
    (Scheme.Modules.pullback (restrictObj_comp_hom_map x u v)).obj
        (restrictObj x (v ≫ u)).line ≅
      (restrictObj (restrictObj x u) v).line :=
  (Scheme.Modules.pullbackComp (restrictObj_comp_hom_map x u v)
      (pullback.fst x.hom (v ≫ u))).app x.line ≪≫
    (Scheme.Modules.pullbackCongr (pullbackLeftPullbackSndIso_hom_fst x.hom u v)).app x.line ≪≫
    (Scheme.Modules.pullbackComp (pullback.fst (pullback.snd x.hom u) v)
        (pullback.fst x.hom u)).symm.app x.line

/-- The forward iterated-pullback comparison is cartesian over the identity of the base. -/
theorem restrictObj_comp_hom_isPullback (x : Obj) {S S' : Scheme.{u}}
    (u : S' ⟶ x.S) (v : S ⟶ S') :
    IsPullback (restrictObj_comp_hom_map x u v) (restrictObj (restrictObj x u) v).hom
      (restrictObj x (v ≫ u)).hom (𝟙 S) := sorry

/-- The inverse iterated-pullback comparison is cartesian over the identity of the base. -/
theorem restrictObj_comp_inv_isPullback (x : Obj) {S S' : Scheme.{u}}
    (u : S' ⟶ x.S) (v : S ⟶ S') :
    IsPullback (restrictObj_comp_inv_map x u v) (restrictObj x (v ≫ u)).hom
      (restrictObj (restrictObj x u) v).hom (𝟙 S) := sorry

/-- The polarized morphism of iterated restriction along `v` then `u` versus restriction
along `v ≫ u`. -/
def restrictObj_comp_hom (x : Obj) {S S' : Scheme.{u}} (u : S' ⟶ x.S) (v : S ⟶ S') :
    restrictObj (restrictObj x u) v ⟶ restrictObj x (v ≫ u) :=
  homMk (restrictObj_comp_hom_map x u v) (𝟙 S) (restrictObj_comp_hom_isPullback x u v)
    (restrictObj_comp_hom_iso x u v)

/-- The inverse polarized morphism of iterated restriction. -/
def restrictObj_comp_inv (x : Obj) {S S' : Scheme.{u}} (u : S' ⟶ x.S) (v : S ⟶ S') :
    restrictObj x (v ≫ u) ⟶ restrictObj (restrictObj x u) v :=
  homMk (restrictObj_comp_inv_map x u v) (𝟙 S) (restrictObj_comp_inv_isPullback x u v)
    ((Scheme.Modules.pullback (restrictObj_comp_inv_map x u v)).mapIso
        (restrictObj_comp_hom_iso x u v).symm ≪≫
      (Scheme.Modules.pullbackComp (restrictObj_comp_inv_map x u v)
          (restrictObj_comp_hom_map x u v)).app (restrictObj x (v ≫ u)).line ≪≫
      (Scheme.Modules.pullbackCongr
          (Iso.inv_hom_id (pullbackLeftPullbackSndIso x.hom u v))).app
        (restrictObj x (v ≫ u)).line ≪≫
      (Scheme.Modules.pullbackId (restrictObj x (v ≫ u)).X).app
        (restrictObj x (v ≫ u)).line)

/-- The forward and inverse iterated-restriction comparisons compose to the identity. -/
theorem restrictObj_comp_hom_inv_id (x : Obj) {S S' : Scheme.{u}}
    (u : S' ⟶ x.S) (v : S ⟶ S') :
    restrictObj_comp_hom x u v ≫ restrictObj_comp_inv x u v =
      𝟙 (restrictObj (restrictObj x u) v) := sorry

/-- The inverse and forward iterated-restriction comparisons compose to the identity. -/
theorem restrictObj_comp_inv_hom_id (x : Obj) {S S' : Scheme.{u}}
    (u : S' ⟶ x.S) (v : S ⟶ S') :
    restrictObj_comp_inv x u v ≫ restrictObj_comp_hom x u v =
      𝟙 (restrictObj x (v ≫ u)) := sorry

/-- Iterated restriction along `v` then `u` is isomorphic to restriction along `v ≫ u`. -/
def restrictObj_comp (x : Obj) {S S' : Scheme.{u}} (u : S' ⟶ x.S) (v : S ⟶ S') :
    restrictObj (restrictObj x u) v ≅ restrictObj x (v ≫ u) where
  hom := restrictObj_comp_hom x u v
  inv := restrictObj_comp_inv x u v
  hom_inv_id := restrictObj_comp_hom_inv_id x u v
  inv_hom_id := restrictObj_comp_inv_hom_id x u v

/-- The base morphism `S ⟶ x.S` associated to a fibre object over `S'` and a map
`S ⟶ S'`. -/
def fiberBase {S S' : Scheme.{u}} (h : S ⟶ S') (x : p.Fiber S') : S ⟶ x.1.S :=
  h ≫ eqToHom x.property.symm

/-- Fibre morphisms are vertical, so restriction of the two ends along `h` uses
compatible base maps. -/
theorem fiberBase_comp {S S' : Scheme.{u}} (h : S ⟶ S') {x y : p.Fiber S'} (φ : x ⟶ y) :
    fiberBase h x ≫ φ.1.base = fiberBase h y :=
  sorry

/-- Restriction of a vertical polarized morphism remains vertical over the new base. -/
theorem restrictFiberMap_mem {S S' : Scheme.{u}} (h : S ⟶ S')
    {x y : p.Fiber S'} (φ : x ⟶ y) :
    IsHomLift p (𝟙 S) (restrictMap φ.1 (fiberBase h x) ≫
      (restrictObjCongr y.1 (fiberBase_comp h φ)).hom) := sorry

/-- The morphism in the new fibre induced by restriction of a vertical polarized morphism. -/
def restrictFiberMap {S S' : Scheme.{u}} (h : S ⟶ S') {x y : p.Fiber S'} (φ : x ⟶ y) :
    Fiber.mk (p := p) (a := restrictObj x.1 (fiberBase h x)) rfl ⟶
      Fiber.mk (p := p) (a := restrictObj y.1 (fiberBase h y)) rfl :=
  ⟨restrictMap φ.1 (fiberBase h x) ≫
      (restrictObjCongr y.1 (fiberBase_comp h φ)).hom, restrictFiberMap_mem h φ⟩

/-- Restriction of vertical morphisms preserves identities. -/
theorem restrict_map_id {S S' : Scheme.{u}} (h : S ⟶ S') (x : p.Fiber S') :
    restrictFiberMap h (𝟙 x) =
      𝟙 (Fiber.mk (p := p) (a := restrictObj x.1 (fiberBase h x)) rfl) := sorry

/-- Restriction of vertical morphisms preserves composition. -/
theorem restrict_map_comp {S S' : Scheme.{u}} (h : S ⟶ S')
    {x y z : p.Fiber S'} (φ : x ⟶ y) (ψ : y ⟶ z) :
    restrictFiberMap h (φ ≫ ψ) = restrictFiberMap h φ ≫ restrictFiberMap h ψ := sorry

/-- Restriction of Polarized fibre categories along a morphism of bases. -/
def restrict {S S' : Scheme.{u}} (h : S ⟶ S') : p.Fiber S' ⥤ p.Fiber S where
  obj x := Fiber.mk (a := restrictObj x.1 (fiberBase h x)) rfl
  map φ := restrictFiberMap h φ
  map_id := restrict_map_id h
  map_comp := restrict_map_comp h

/-- The underlying polarized object of `restrict h` is `restrictObj` of `fiberBase h`. -/
theorem restrict_obj {S S' : Scheme.{u}} (h : S ⟶ S') (x : p.Fiber S') :
    ((restrict h).obj x).1 = restrictObj x.1 (fiberBase h x) :=
  sorry

/-- The underlying polarized morphism of `restrict h` is `restrictMap` transported along
`fiberBase_comp`. -/
theorem restrict_map {S S' : Scheme.{u}} (h : S ⟶ S') {x y : p.Fiber S'} (φ : x ⟶ y) :
    ((restrict h).map φ).1 =
      restrictMap φ.1 (fiberBase h x) ≫
        (restrictObjCongr y.1 (fiberBase_comp h φ)).hom :=
  sorry

/-- The forward comparison of single and successive restriction is vertical over the base. -/
theorem restrictCompAppHom_mem {S S' S'' : Scheme.{u}}
    (g : S ⟶ S') (h : S' ⟶ S'') (x : p.Fiber S'') :
    IsHomLift p (𝟙 S)
      ((restrictObjCongr x.1 (Category.assoc g h (eqToHom x.property.symm))).hom ≫
        (restrictObj_comp x.1 (fiberBase h x) g).inv ≫
          (restrictObjCongr (restrictObj x.1 (fiberBase h x))
            (Category.comp_id g).symm).hom) := sorry

/-- The inverse comparison of single and successive restriction is vertical over the base. -/
theorem restrictCompAppInv_mem {S S' S'' : Scheme.{u}}
    (g : S ⟶ S') (h : S' ⟶ S'') (x : p.Fiber S'') :
    IsHomLift p (𝟙 S)
      ((restrictObjCongr (restrictObj x.1 (fiberBase h x)) (Category.comp_id g)).hom ≫
        (restrictObj_comp x.1 (fiberBase h x) g).hom ≫
          (restrictObjCongr x.1
            (Category.assoc g h (eqToHom x.property.symm)).symm).hom) := sorry

/-- The forward fibre morphism comparing single restriction with successive restriction. -/
def restrictCompAppHom {S S' S'' : Scheme.{u}}
    (g : S ⟶ S') (h : S' ⟶ S'') (x : p.Fiber S'') :
    (restrict (g ≫ h)).obj x ⟶ (restrict h ⋙ restrict g).obj x :=
  ⟨(restrictObjCongr x.1 (Category.assoc g h (eqToHom x.property.symm))).hom ≫
      (restrictObj_comp x.1 (fiberBase h x) g).inv ≫
        (restrictObjCongr (restrictObj x.1 (fiberBase h x))
          (Category.comp_id g).symm).hom, restrictCompAppHom_mem g h x⟩

/-- The inverse fibre morphism comparing successive restriction with single restriction. -/
def restrictCompAppInv {S S' S'' : Scheme.{u}}
    (g : S ⟶ S') (h : S' ⟶ S'') (x : p.Fiber S'') :
    (restrict h ⋙ restrict g).obj x ⟶ (restrict (g ≫ h)).obj x :=
  ⟨(restrictObjCongr (restrictObj x.1 (fiberBase h x)) (Category.comp_id g)).hom ≫
      (restrictObj_comp x.1 (fiberBase h x) g).hom ≫
        (restrictObjCongr x.1
          (Category.assoc g h (eqToHom x.property.symm)).symm).hom,
    restrictCompAppInv_mem g h x⟩

/-- The forward and inverse fibre comparisons compose to the identity. -/
theorem restrict_comp_app_hom_inv_id {S S' S'' : Scheme.{u}}
    (g : S ⟶ S') (h : S' ⟶ S'') (x : p.Fiber S'') :
    restrictCompAppHom g h x ≫ restrictCompAppInv g h x =
      𝟙 ((restrict (g ≫ h)).obj x) := sorry

/-- The inverse and forward fibre comparisons compose to the identity. -/
theorem restrict_comp_app_inv_hom_id {S S' S'' : Scheme.{u}}
    (g : S ⟶ S') (h : S' ⟶ S'') (x : p.Fiber S'') :
    restrictCompAppInv g h x ≫ restrictCompAppHom g h x =
      𝟙 ((restrict h ⋙ restrict g).obj x) := sorry

/-- The fibre isomorphism comparing `restrict (g ≫ h)` with successive restriction. -/
def restrict_comp_app {S S' S'' : Scheme.{u}} (g : S ⟶ S') (h : S' ⟶ S'') (x : p.Fiber S'') :
    (restrict (g ≫ h)).obj x ≅ (restrict h ⋙ restrict g).obj x where
  hom := restrictCompAppHom g h x
  inv := restrictCompAppInv g h x
  hom_inv_id := restrict_comp_app_hom_inv_id g h x
  inv_hom_id := restrict_comp_app_inv_hom_id g h x

/-- The comparison of single and successive restriction is natural in the polarized family. -/
theorem restrict_comp_naturality {S S' S'' : Scheme.{u}}
    (g : S ⟶ S') (h : S' ⟶ S'') {x y : p.Fiber S''} (φ : x ⟶ y) :
    (restrict (g ≫ h)).map φ ≫ (restrict_comp_app g h y).hom =
      (restrict_comp_app g h x).hom ≫ (restrict h ⋙ restrict g).map φ := sorry

/-- Successive restriction along `h` then `g` agrees with restriction along `g ≫ h`. -/
def restrict_comp {S S' S'' : Scheme.{u}} (g : S ⟶ S') (h : S' ⟶ S'') :
    restrict (g ≫ h) ≅ restrict h ⋙ restrict g :=
  NatIso.ofComponents (fun x ↦ restrict_comp_app g h x) (restrict_comp_naturality g h)

end AlgebraicGeometry.Polarized
