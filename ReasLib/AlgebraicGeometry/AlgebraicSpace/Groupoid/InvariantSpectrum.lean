/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Sites.Descent.IsStack
public import ReasLib.AlgebraicGeometry.GroupoidScheme.InvariantSpectrum.Quotient
public import ReasLib.AlgebraicGeometry.GroupoidScheme.Morphism
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Groupoid.OfScheme
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Groupoid.Quotient.Small
public import ReasLib.CategoryTheory.Fibered.ChosenCleavage.Pseudofunctor
public import ReasLib.CategoryTheory.Fibered.Cleavage.SliceSection
public import ReasLib.CategoryTheory.Fibered.Fiber.Isomorphism
public import ReasLib.CategoryTheory.Fibered.Representable.Slice.Map

/-!
# Invariant spectra and quotient stacks

The atlas of a groupoid descends along an affine finite locally free equivalence-relation
quotient to a morphism from the invariant spectrum to the quotient stack.
-/

@[expose] public section

set_option backward.privateInPublic true

open CategoryTheory AlgebraicGeometry CategoryTheory.Limits
open AlgebraicGeometry.AlgebraicSpace
open FiberedCategoryOver.Groupoids
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidAlgebraicSpace

variable {S : Scheme.{u}} (P G : GroupoidScheme S)
variable {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
variable (tSharp : A →+* B)
variable (eU : Spec (CommRingCat.of A) ≅ P.U.left)
variable (eR : Spec (CommRingCat.of B) ≅ P.R.left)
variable
  (h_source : eR.hom ≫ P.s.left =
    Spec.map (CommRingCat.ofHom (algebraMap A B)) ≫ eU.hom)
variable
  (h_target : eR.hom ≫ P.t.left =
    Spec.map (CommRingCat.ofHom tSharp) ≫ eU.hom)
variable [IsFiniteLocallyFree P.s.left] [IsFiniteLocallyFree P.t.left]
variable [IsEquivalenceRelation P.t P.s]
variable (hU : P.U = G.U)

/-- The invariant spectrum of an affine finite locally free equivalence relation, as a
scheme over `S`. -/
abbrev invariantSpectrum : Over S :=
  GroupoidScheme.invariantSpectrumOver P tSharp eU
    (GroupoidScheme.invariantSpectrumMap_effectiveEpi P tSharp eU eR h_source h_target)
    (GroupoidScheme.invariantSpectrumMap_respectsBase P tSharp eU eR h_source h_target)

/-- The atlas of `[U/R]`, pulled back along the slice comparison of the object
scheme of `G`. -/
def atlasFromSlice : GroupoidsOver.slice G.U ⟶ (SmallQuotient.quotientStack (ofScheme G)) :=
  (ofOverSliceEquiv G.U).inv ≫ (SmallQuotient.atlas (ofScheme G))

/-- The atlas of `[U/R]` transported along an identification of object schemes. -/
def atlasFromSlice_eqToHom :
    GroupoidsOver.slice P.U ⟶ (SmallQuotient.quotientStack (ofScheme G)) :=
  eqToHom (congrArg (fun W ↦ GroupoidsOver.slice W) hU) ≫ atlasFromSlice G

/-- The cleavage of `[U/R]` selected from its fibreing. -/
private def quotientCleavage : (SmallQuotient.quotientStack (ofScheme G)).p.Cleavage :=
  Functor.Cleavage.ofIsFibered (SmallQuotient.quotientStack (ofScheme G)).p

/-- The kernel-pair comparison of `U ⟶ Ū` is an isomorphism, so a pair of maps to `U`
over `Ū` determines an arrow of `P`. -/
private def relationLift (ι : GroupoidScheme.Hom P G) {Y : Over S} (f₁ f₂ : Y ⟶ P.U)
    (hf : f₁ ≫ GroupoidScheme.invariantSpectrumQuotient P tSharp eU eR h_source h_target =
      f₂ ≫ GroupoidScheme.invariantSpectrumQuotient P tSharp eU eR h_source h_target) :
    Y ⟶ G.R :=
  pullback.lift f₂ f₁ hf.symm ≫
    (GroupoidScheme.invariantKernelPairIso P tSharp eU eR h_source h_target).inv ≫
    ι.arrow

/-- A `T`-valued point of the object scheme of `G`, as an object of `[U /ₚ R]`. -/
private def preQuotientPoint {Y : Over S} (f : Y ⟶ G.U) :
    (SmallQuotient.preQuotient (ofScheme G)).total :=
  { base := Y
    fiber := f }

/-- A represented arrow with prescribed source has the same source on functor-of-points. -/
private theorem preQuotientHom_source {Y : Over S} {f₁ f₂ : Y ⟶ G.U}
    (r : Y ⟶ G.R) (hs : r ≫ G.s = f₁) (ht : r ≫ G.t = f₂) :
    (ofScheme G).s.left.app (Opposite.op Y) r = f₁ := sorry

/-- A represented arrow with prescribed target has the target restricted along the identity. -/
private theorem preQuotientHom_target {Y : Over S} {f₁ f₂ : Y ⟶ G.U}
    (r : Y ⟶ G.R) (hs : r ≫ G.s = f₁) (ht : r ≫ G.t = f₂) :
    (ofScheme G).t.left.app (Opposite.op Y) r =
      (ofScheme G).U.left.functorOfPoints.map (𝟙 (Opposite.op Y)) f₂ := sorry

/-- The morphism of `[U /ₚ R]` over `Y` induced by an arrow of `R`. -/
private def preQuotientHom {Y : Over S} {f₁ f₂ : Y ⟶ G.U} (r : Y ⟶ G.R)
    (hs : r ≫ G.s = f₁) (ht : r ≫ G.t = f₂) :
    preQuotientPoint G f₁ ⟶ preQuotientPoint G f₂ :=
  { base := 𝟙 Y
    fiber := FunctorPointHom.ofArrow r
      (preQuotientHom_source G r hs ht) (preQuotientHom_target G r hs ht) }

/-- The image of a `T`-valued point of `U` under the atlas of `[U/R]`. -/
private def atlasPoint {Y : Over S} (f : Y ⟶ G.U) : (SmallQuotient.quotientStack (ofScheme G)).total :=
  (toFunctor (SmallQuotient.stackificationHom (ofScheme G))).obj (preQuotientPoint G f)

/-- The kernel-pair lift has the first point as its source after identifying object schemes. -/
private theorem atlasDescentHom_source (ι : GroupoidScheme.Hom P G)
    (hι : ι.IsIdentityOnObjects hU) {Y : Over S} (f₁ f₂ : Y ⟶ P.U)
    (hf : f₁ ≫ GroupoidScheme.invariantSpectrumQuotient P tSharp eU eR h_source h_target =
      f₂ ≫ GroupoidScheme.invariantSpectrumQuotient P tSharp eU eR h_source h_target) :
    relationLift P G tSharp eU eR h_source h_target ι f₁ f₂ hf ≫ G.s =
      f₁ ≫ eqToHom hU := sorry

/-- The kernel-pair lift has the second point as its target after identifying object schemes. -/
private theorem atlasDescentHom_target (ι : GroupoidScheme.Hom P G)
    (hι : ι.IsIdentityOnObjects hU) {Y : Over S} (f₁ f₂ : Y ⟶ P.U)
    (hf : f₁ ≫ GroupoidScheme.invariantSpectrumQuotient P tSharp eU eR h_source h_target =
      f₂ ≫ GroupoidScheme.invariantSpectrumQuotient P tSharp eU eR h_source h_target) :
    relationLift P G tSharp eU eR h_source h_target ι f₁ f₂ hf ≫ G.t =
      f₂ ≫ eqToHom hU := sorry

/-- The total-category morphism of `[U/R]` induced by a `P`-arrow between two maps
to `U` over `Ū`. -/
private def atlasDescentHom (ι : GroupoidScheme.Hom P G)
    (hι : ι.IsIdentityOnObjects hU) {Y : Over S} (f₁ f₂ : Y ⟶ P.U)
    (hf : f₁ ≫ GroupoidScheme.invariantSpectrumQuotient P tSharp eU eR h_source h_target =
      f₂ ≫ GroupoidScheme.invariantSpectrumQuotient P tSharp eU eR h_source h_target) :
    atlasPoint G (f₁ ≫ eqToHom hU) ⟶ atlasPoint G (f₂ ≫ eqToHom hU) :=
  (toFunctor (SmallQuotient.stackificationHom (ofScheme G))).map
    (preQuotientHom G (relationLift P G tSharp eU eR h_source h_target ι f₁ f₂ hf)
      (atlasDescentHom_source P G tSharp eU eR h_source h_target hU ι hι f₁ f₂ hf)
      (atlasDescentHom_target P G tSharp eU eR h_source h_target hU ι hι f₁ f₂ hf))

/-- The projection of `atlasPoint f` is the test scheme of `f`. -/
private theorem atlasPoint_p {Y : Over S} (f : Y ⟶ G.U) :
    (SmallQuotient.quotientStack (ofScheme G)).p.obj (atlasPoint G f) = Y := sorry

/-- The atlas point of `f`, as a standard fibre object. -/
private def atlasPointFiber {Y : Over S} (f : Y ⟶ G.U) :
    (SmallQuotient.quotientStack (ofScheme G)).p.Fiber Y :=
  ⟨atlasPoint G f, atlasPoint_p G f⟩

/-- The atlas point over the identified object scheme, in the standard fiber. -/
private def atlasFiberOnP : (SmallQuotient.quotientStack (ofScheme G)).p.Fiber P.U :=
  atlasPointFiber G (eqToHom hU)

/-- The identity arrow at a restricted point has that point as source. -/
private theorem atlasPointRestriction_source {Y : Over S} (f : Y ⟶ P.U) :
    (ofScheme G).s.left.app (Opposite.op Y) (f ≫ eqToHom hU ≫ G.e) =
      f ≫ eqToHom hU := sorry

/-- The identity arrow at a restricted point targets the restriction of the atlas point. -/
private theorem atlasPointRestriction_target {Y : Over S} (f : Y ⟶ P.U) :
    (ofScheme G).t.left.app (Opposite.op Y) (f ≫ eqToHom hU ≫ G.e) =
      (ofScheme G).U.left.functorOfPoints.map f.op (eqToHom hU) := sorry

/-- Restriction of the identified atlas point along a map to the object scheme. -/
private def atlasPointRestriction {Y : Over S} (f : Y ⟶ P.U) :
    atlasPoint G (f ≫ eqToHom hU) ⟶ (atlasFiberOnP P G hU).1 :=
  (toFunctor (SmallQuotient.stackificationHom (ofScheme G))).map
    { base := f
      fiber := FunctorPointHom.ofArrow (f ≫ eqToHom hU ≫ G.e)
        (atlasPointRestriction_source P G hU f) (atlasPointRestriction_target P G hU f) }

/-- Restriction of an atlas point is cartesian over the restricting map. -/
private theorem atlasPointRestriction_isCartesian {Y : Over S} (f : Y ⟶ P.U) :
    (SmallQuotient.quotientStack (ofScheme G)).p.IsCartesian f
      (atlasPointRestriction P G hU f) := sorry

/-- Chosen restriction of the atlas point is isomorphic to its concrete restriction. -/
private def atlasReindexIso {Y : Over S} (f : Y ⟶ P.U) :
    ((Functor.fiberPseudofunctor (SmallQuotient.quotientStack (ofScheme G)).p).map
      f.op.toLoc).toFunctor.obj (atlasFiberOnP P G hU) ≅
        atlasPointFiber G (f ≫ eqToHom hU) :=
  let p := (SmallQuotient.quotientStack (ofScheme G)).p
  let φ := atlasPointRestriction P G hU f
  let φ' := Functor.Chosen.cartesianHom p f (atlasFiberOnP P G hU)
  let hφ := atlasPointRestriction_isCartesian P G hU f
  let hφ' : p.IsCartesian f φ' := inferInstance
  let e := @Functor.IsCartesian.domainUniqueUpToIso _ _ _ _ p _ _ _ _ f φ hφ _ φ' hφ'
  eqToIso (Functor.FiberPseudofunctor.map.obj p f (atlasFiberOnP P G hU)) ≪≫
    Functor.Fiber.isoMk e
      (@Functor.IsCartesian.domainUniqueUpToIso_inv_isHomLift _ _ _ _ p _ _ _ _
        f φ hφ _ φ' hφ')

/-- The atlas arrow induced by the kernel pair is vertical over its test scheme. -/
private theorem atlasDescentHom_isHomLift (ι : GroupoidScheme.Hom P G)
    (hι : ι.IsIdentityOnObjects hU) {Y : Over S} (f₁ f₂ : Y ⟶ P.U)
    (hf : f₁ ≫ GroupoidScheme.invariantSpectrumQuotient P tSharp eU eR h_source h_target =
      f₂ ≫ GroupoidScheme.invariantSpectrumQuotient P tSharp eU eR h_source h_target) :
    (SmallQuotient.quotientStack (ofScheme G)).p.IsHomLift (𝟙 Y)
      (atlasDescentHom P G tSharp eU eR h_source h_target hU ι hι f₁ f₂ hf) := sorry

/-- The atlas transition between two restrictions over the invariant spectrum. -/
private def atlasDescentTransition (ι : GroupoidScheme.Hom P G)
    (hι : ι.IsIdentityOnObjects hU) {Y : Over S} (f₁ f₂ : Y ⟶ P.U)
    (hf : f₁ ≫ GroupoidScheme.invariantSpectrumQuotient P tSharp eU eR h_source h_target =
      f₂ ≫ GroupoidScheme.invariantSpectrumQuotient P tSharp eU eR h_source h_target) :
    ((Functor.fiberPseudofunctor (SmallQuotient.quotientStack (ofScheme G)).p).map
      f₁.op.toLoc).toFunctor.obj (atlasFiberOnP P G hU) ⟶
    ((Functor.fiberPseudofunctor (SmallQuotient.quotientStack (ofScheme G)).p).map
      f₂.op.toLoc).toFunctor.obj (atlasFiberOnP P G hU) :=
  (atlasReindexIso P G hU f₁).hom ≫
    Functor.Fiber.Hom.mk
      (x := atlasPointFiber G (f₁ ≫ eqToHom hU))
      (y := atlasPointFiber G (f₂ ≫ eqToHom hU))
      (atlasDescentHom P G tSharp eU eR h_source h_target hU ι hι f₁ f₂ hf)
      (atlasDescentHom_isHomLift P G tSharp eU eR h_source h_target hU ι hι f₁ f₂ hf) ≫
    (atlasReindexIso P G hU f₂).inv

/-- Atlas transitions commute with pullback along a morphism of test schemes. -/
private theorem atlasDescentTransition_pullHom (ι : GroupoidScheme.Hom P G)
    (hι : ι.IsIdentityOnObjects hU) {Y' Y : Over S} (g : Y' ⟶ Y)
    (q : Y ⟶ invariantSpectrum P tSharp eU eR h_source h_target)
    (q' : Y' ⟶ invariantSpectrum P tSharp eU eR h_source h_target) (hq : g ≫ q = q')
    (f₁ f₂ : Y ⟶ P.U)
    (hf₁ : f₁ ≫ GroupoidScheme.invariantSpectrumQuotient P tSharp eU eR h_source h_target = q)
    (hf₂ : f₂ ≫ GroupoidScheme.invariantSpectrumQuotient P tSharp eU eR h_source h_target = q)
    (gf₁ gf₂ : Y' ⟶ P.U) (hgf₁ : g ≫ f₁ = gf₁) (hgf₂ : g ≫ f₂ = gf₂) :
    let π := GroupoidScheme.invariantSpectrumQuotient P tSharp eU eR h_source h_target
    Pseudofunctor.LocallyDiscreteOpToCat.pullHom
        (atlasDescentTransition P G tSharp eU eR h_source h_target hU ι hι f₁ f₂
          (hf₁.trans hf₂.symm)) g gf₁ gf₂ hgf₁ hgf₂ =
      atlasDescentTransition P G tSharp eU eR h_source h_target hU ι hι gf₁ gf₂
        ((congrArg (fun f ↦ f ≫ π) hgf₁).symm.trans
          ((Category.assoc g f₁ π).trans
            ((congrArg (fun f ↦ g ≫ f) (hf₁.trans hf₂.symm)).trans
              ((Category.assoc g f₂ π).symm.trans (congrArg (fun f ↦ f ≫ π) hgf₂))))) := sorry

/-- The atlas transition from a restriction to itself is its identity. -/
private theorem atlasDescentTransition_self (ι : GroupoidScheme.Hom P G)
    (hι : ι.IsIdentityOnObjects hU) {Y : Over S}
    (q : Y ⟶ invariantSpectrum P tSharp eU eR h_source h_target) (f : Y ⟶ P.U)
    (hf : f ≫ GroupoidScheme.invariantSpectrumQuotient P tSharp eU eR h_source h_target = q) :
    atlasDescentTransition P G tSharp eU eR h_source h_target hU ι hι f f
      (hf.trans hf.symm) = 𝟙 _ := sorry

/-- Atlas transitions satisfy the cocycle identity on three restrictions. -/
private theorem atlasDescentTransition_comp (ι : GroupoidScheme.Hom P G)
    (hι : ι.IsIdentityOnObjects hU) {Y : Over S}
    (q : Y ⟶ invariantSpectrum P tSharp eU eR h_source h_target) (f₁ f₂ f₃ : Y ⟶ P.U)
    (hf₁ : f₁ ≫ GroupoidScheme.invariantSpectrumQuotient P tSharp eU eR h_source h_target = q)
    (hf₂ : f₂ ≫ GroupoidScheme.invariantSpectrumQuotient P tSharp eU eR h_source h_target = q)
    (hf₃ : f₃ ≫ GroupoidScheme.invariantSpectrumQuotient P tSharp eU eR h_source h_target = q) :
    atlasDescentTransition P G tSharp eU eR h_source h_target hU ι hι f₁ f₂
        (hf₁.trans hf₂.symm) ≫
      atlasDescentTransition P G tSharp eU eR h_source h_target hU ι hι f₂ f₃
        (hf₂.trans hf₃.symm) =
      atlasDescentTransition P G tSharp eU eR h_source h_target hU ι hι f₁ f₃
        (hf₁.trans hf₃.symm) := sorry

/-- Descent data for the atlas of `[U/R]` along the fppf cover `U ⟶ Ū`, using that
`P` is identity-on-objects in `G`. -/
private def atlasDescentData (ι : GroupoidScheme.Hom P G)
    (hι : ι.IsIdentityOnObjects hU) :
    (Functor.fiberPseudofunctor (SmallQuotient.quotientStack (ofScheme G)).p).DescentData
      (fun _ : Unit ↦ GroupoidScheme.invariantSpectrumQuotient P tSharp eU eR h_source h_target) where
  obj _ := atlasFiberOnP P G hU
  hom _ _ _ _ f₁ f₂ hf₁ hf₂ :=
    atlasDescentTransition P G tSharp eU eR h_source h_target hU ι hι f₁ f₂
      (hf₁.trans hf₂.symm)
  pullHom_hom _ _ g q q' hq _ _ f₁ f₂ hf₁ hf₂ gf₁ gf₂ hgf₁ hgf₂ :=
    atlasDescentTransition_pullHom P G tSharp eU eR h_source h_target hU ι hι
      g q q' hq f₁ f₂ hf₁ hf₂ gf₁ gf₂ hgf₁ hgf₂
  hom_self _ q _ f hf :=
    atlasDescentTransition_self P G tSharp eU eR h_source h_target hU ι hι q f hf
  hom_comp _ q _ _ _ f₁ f₂ f₃ hf₁ hf₂ hf₃ :=
    atlasDescentTransition_comp P G tSharp eU eR h_source h_target hU ι hι
      q f₁ f₂ f₃ hf₁ hf₂ hf₃

/-- The single arrow `U ⟶ Ū` generates an fppf covering sieve. -/
private theorem invariantSpectrumQuotient_covers :
    Sieve.ofArrows (fun _ : Unit ↦ P.U)
        (fun _ ↦ GroupoidScheme.invariantSpectrumQuotient P tSharp eU eR h_source h_target) ∈
      Scheme.fppfTopology.over S
        (invariantSpectrum P tSharp eU eR h_source h_target) := sorry

/-- Effective descent along the invariant-spectrum quotient in the quotient stack. -/
private def atlasDescentEquivalence :
    (SmallQuotient.quotientStack (ofScheme G)).p.Fiber
        (invariantSpectrum P tSharp eU eR h_source h_target) ≌
      (Functor.fiberPseudofunctor (SmallQuotient.quotientStack (ofScheme G)).p).DescentData
        (fun _ : Unit ↦ GroupoidScheme.invariantSpectrumQuotient P tSharp eU eR
          h_source h_target) :=
  let F := Functor.fiberPseudofunctor (SmallQuotient.quotientStack (ofScheme G)).p
  let q := fun _ : Unit ↦ GroupoidScheme.invariantSpectrumQuotient P tSharp eU eR
    h_source h_target
  @Functor.asEquivalence _ _ _ _ (F.toDescentData q)
    (@Pseudofunctor.isEquivalence_toDescentData _ _ F (Scheme.fppfTopology.over S)
      (SmallQuotient.quotientStack_isStack (ofScheme G)).toIsStack
      _ _ _ q (invariantSpectrumQuotient_covers P tSharp eU eR h_source h_target))

/-- The descended atlas object of `[U/R]` over `Ū`. -/
private def atlasDescentObject (ι : GroupoidScheme.Hom P G)
    (hι : ι.IsIdentityOnObjects hU) :
    (SmallQuotient.quotientStack (ofScheme G)).p.Fiber
      (invariantSpectrum P tSharp eU eR h_source h_target) :=
  (atlasDescentEquivalence P G tSharp eU eR h_source h_target).inverse.obj
    (atlasDescentData P G tSharp eU eR h_source h_target hU ι hι)

/-- A morphism of represented invariant-spectrum points commutes with their structure maps. -/
private theorem invariantSpectrumToOverQuotientMap_over
    {x y : (ofOver (invariantSpectrum P tSharp eU eR h_source h_target)).toGroupoids.total}
    (f : x ⟶ y) :
    f.unop.val.unop ≫ y.unop.snd = x.unop.snd := sorry

/-- The map between cartesian restrictions of the descended atlas induced by a point morphism. -/
private def invariantSpectrumToOverQuotientMap (ι : GroupoidScheme.Hom P G)
    (hι : ι.IsIdentityOnObjects hU)
    {x y : (ofOver (invariantSpectrum P tSharp eU eR h_source h_target)).toGroupoids.total}
    (f : x ⟶ y) :
    ((quotientCleavage G).reindexObj x.unop.snd
        (atlasDescentObject P G tSharp eU eR h_source h_target hU ι hι)).1 ⟶
      ((quotientCleavage G).reindexObj y.unop.snd
        (atlasDescentObject P G tSharp eU eR h_source h_target hU ι hι)).1 :=
  Functor.Cleavage.SliceSection.map (quotientCleavage G)
    (atlasDescentObject P G tSharp eU eR h_source h_target hU ι hι)
    (a := Over.mk x.unop.snd) (b := Over.mk y.unop.snd)
    (Over.homMk f.unop.val.unop
      (invariantSpectrumToOverQuotientMap_over P tSharp eU eR h_source h_target f))

/-- Cartesian restriction of the descended atlas sends identity point morphisms to identities. -/
private theorem invariantSpectrumToOverQuotientMap_id (ι : GroupoidScheme.Hom P G)
    (hι : ι.IsIdentityOnObjects hU)
    (x : (ofOver (invariantSpectrum P tSharp eU eR h_source h_target)).toGroupoids.total) :
    invariantSpectrumToOverQuotientMap P G tSharp eU eR h_source h_target hU ι hι (𝟙 x) =
      𝟙 _ := sorry

/-- Cartesian restriction of the descended atlas preserves composition of point morphisms. -/
private theorem invariantSpectrumToOverQuotientMap_comp (ι : GroupoidScheme.Hom P G)
    (hι : ι.IsIdentityOnObjects hU)
    {x y z : (ofOver (invariantSpectrum P tSharp eU eR h_source h_target)).toGroupoids.total}
    (f : x ⟶ y) (g : y ⟶ z) :
    invariantSpectrumToOverQuotientMap P G tSharp eU eR h_source h_target hU ι hι (f ≫ g) =
      invariantSpectrumToOverQuotientMap P G tSharp eU eR h_source h_target hU ι hι f ≫
        invariantSpectrumToOverQuotientMap P G tSharp eU eR h_source h_target hU ι hι g := sorry

/-- The functor on total categories sending a `T`-point of `Ū` to the cartesian
reindexing of the descended atlas. -/
private def invariantSpectrumToOverQuotientFunctor (ι : GroupoidScheme.Hom P G)
    (hι : ι.IsIdentityOnObjects hU) :
    (ofOver (invariantSpectrum P tSharp eU eR h_source h_target)).toGroupoids.total ⥤
      (SmallQuotient.quotientStack (ofScheme G)).total where
  obj x :=
    ((quotientCleavage G).reindexObj x.unop.snd
      (atlasDescentObject P G tSharp eU eR h_source h_target hU ι hι)).1
  map f := invariantSpectrumToOverQuotientMap P G tSharp eU eR h_source h_target hU ι hι f
  map_id := invariantSpectrumToOverQuotientMap_id P G tSharp eU eR h_source h_target hU ι hι
  map_comp := invariantSpectrumToOverQuotientMap_comp P G tSharp eU eR h_source h_target hU ι hι

/-- The functor `invariantSpectrumToOverQuotientFunctor` lies over `Over S`. -/
private theorem invariantSpectrumToOverQuotientFunctor_w (ι : GroupoidScheme.Hom P G)
    (hι : ι.IsIdentityOnObjects hU) :
    invariantSpectrumToOverQuotientFunctor P G tSharp eU eR h_source h_target hU ι hι ⋙
        (SmallQuotient.quotientStack (ofScheme G)).p =
      (ofOver (invariantSpectrum P tSharp eU eR h_source h_target)).toGroupoids.p := sorry

/-- The canonical 1-morphism `(ofOver Ū).toGroupoids ⟶ [U/R]` whose value on a
`T`-point of `Ū` is the cartesian reindexing of the descended atlas. -/
private def invariantSpectrumToOverQuotient (ι : GroupoidScheme.Hom P G)
    (hι : ι.IsIdentityOnObjects hU) :
    (ofOver (invariantSpectrum P tSharp eU eR h_source h_target)).toGroupoids ⟶
      (SmallQuotient.quotientStack (ofScheme G)) :=
  ofBasedFunctor
    (BasedFunctor.ofFunctor
      (invariantSpectrumToOverQuotientFunctor P G tSharp eU eR h_source h_target hU ι hι)
      (invariantSpectrumToOverQuotientFunctor_w P G tSharp eU eR h_source h_target hU ι
        hι))

/-- The canonical 1-morphism `Ū ⟶ [U/R]` through which the atlas of `G` factors
along the invariant-spectrum quotient of `P`. -/
def invariantSpectrumToQuotient (ι : GroupoidScheme.Hom P G)
    (hι : ι.IsIdentityOnObjects hU) :
    GroupoidsOver.slice (invariantSpectrum P tSharp eU eR h_source h_target) ⟶
      (SmallQuotient.quotientStack (ofScheme G)) :=
  (ofOverSliceEquiv (invariantSpectrum P tSharp eU eR h_source h_target)).inv ≫
    invariantSpectrumToOverQuotient P G tSharp eU eR h_source h_target hU ι hι

/-- Precomposition with `U ⟶ Ū` recovers the atlas of `[U/R]` up to a 2-isomorphism. -/
theorem invariantSpectrumToQuotient_comp_atlas (ι : GroupoidScheme.Hom P G)
    (hι : ι.IsIdentityOnObjects hU) :
    Nonempty
      (overMap (GroupoidScheme.invariantSpectrumQuotient P tSharp eU eR h_source h_target) ≫
          invariantSpectrumToQuotient P G tSharp eU eR h_source h_target hU ι hι ≅
        atlasFromSlice_eqToHom P G hU) := sorry

end AlgebraicGeometry.GroupoidAlgebraicSpace
