module

public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Pullbacks
public import Mathlib.CategoryTheory.Sites.Descent.IsStack
public import ReasLib.AlgebraicGeometry.GroupoidScheme.InvariantSpectrum.Quotient
public import ReasLib.AlgebraicGeometry.GroupoidScheme.Morphism
public import ReasLib.CategoryTheory.Fibered.ChosenCleavage.Pseudofunctor
public import ReasLib.CategoryTheory.Fibered.Cleavage.SliceSection
public import ReasLib.CategoryTheory.Fibered.Fiber.Hom
public import ReasLib.CategoryTheory.Fibered.Representable.Slice.Map
public import stacks_project.Chap67.Lemma_67_24_2_FieldPoints
public import stacks_project.Chap94.Definition_94_16_5_Quotient

/-!
# Invariant spectrum to quotient stack

This module converts a groupoid scheme into a groupoid in algebraic spaces and
records the atlas of `[U/R]` on the slice of the object scheme. The comparison
`Ū ⟶ [U/R]` is the cleavage slice section of the atlas of `G` after effective
descent along the fppf quotient `U ⟶ Ū` of the identity-component equivalence
relation `P`, using that `P` is identity-on-objects in `G`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry CategoryTheory.Limits
open AlgebraicGeometry.AlgebraicSpace
open FiberedCategoryOver.Groupoids
open FiberedCategoryOver.Groupoids.slice
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- The fibre product of an over-morphism cospan, as an algebraic space, obtained
as the presheaf fibre product of the Yoneda embeddings. -/
def ofOverPullback {S : Scheme.{u}} {U R : Over S} (s t : R ⟶ U) : AlgebraicSpace S :=
  ofFunctor (pullback (yoneda.map s) (yoneda.map t)) sorry sorry sorry

/-- The functor of points of `ofOverPullback s t` is the presheaf fibre product of
`yoneda.map s` and `yoneda.map t`. -/
theorem ofOverPullback_functorOfPoints {S : Scheme.{u}} {U R : Over S} (s t : R ⟶ U) :
    (ofOverPullback s t).functorOfPoints = pullback (yoneda.map s) (yoneda.map t) := sorry

/-- The Yoneda comparison identifying the scheme-theoretic fibre product with
`ofOverPullback`. -/
def ofOverPullbackIso {S : Scheme.{u}} {U R : Over S} (s t : R ⟶ U) :
    ofOver (pullback s t) ≅ ofOverPullback s t where
  hom := (PreservesPullback.iso yoneda s t).hom
  inv := (PreservesPullback.iso yoneda s t).inv
  hom_inv_id := sorry
  inv_hom_id := sorry

/-- The forward component of `ofOverPullbackIso` is the Yoneda preservation map. -/
theorem ofOverPullbackIso_hom {S : Scheme.{u}} {U R : Over S} (s t : R ⟶ U) :
    (ofOverPullbackIso s t).hom = (PreservesPullback.iso yoneda s t).hom := sorry

end AlgebraicGeometry.AlgebraicSpace

namespace AlgebraicGeometry.GroupoidAlgebraicSpace

/-- The object scheme of a groupoid scheme, as an algebraic space over `S`. -/
def objectOver {S : Scheme.{u}} (G : GroupoidScheme S) :
    Over (ofOver (Over.mk (𝟙 S))) :=
  Over.mk (toBase (ofOver G.U))

/-- The arrow scheme of a groupoid scheme, as an algebraic space over `S`. -/
def arrowOver {S : Scheme.{u}} (G : GroupoidScheme S) :
    Over (ofOver (Over.mk (𝟙 S))) :=
  Over.mk (toBase (ofOver G.R))

/-- The source morphism of a groupoid scheme, as a morphism of algebraic spaces. -/
def sourceOver {S : Scheme.{u}} (G : GroupoidScheme S) :
    arrowOver G ⟶ objectOver G :=
  Over.homMk (ofOverMap G.s) (eq_toBase (ofOverMap G.s ≫ toBase (ofOver G.U)))

/-- The target morphism of a groupoid scheme, as a morphism of algebraic spaces. -/
def targetOver {S : Scheme.{u}} (G : GroupoidScheme S) :
    arrowOver G ⟶ objectOver G :=
  Over.homMk (ofOverMap G.t) (eq_toBase (ofOverMap G.t ≫ toBase (ofOver G.U)))

/-- The identity-arrow morphism of a groupoid scheme, as a morphism of algebraic
spaces. -/
def identityOver {S : Scheme.{u}} (G : GroupoidScheme S) :
    objectOver G ⟶ arrowOver G :=
  Over.homMk (ofOverMap G.e) (eq_toBase (ofOverMap G.e ≫ toBase (ofOver G.R)))

/-- The inverse-arrow morphism of a groupoid scheme, as a morphism of algebraic
spaces. -/
def inverseOver {S : Scheme.{u}} (G : GroupoidScheme S) :
    arrowOver G ⟶ arrowOver G :=
  Over.homMk (ofOverMap G.i) (eq_toBase (ofOverMap G.i ≫ toBase (ofOver G.R)))

/-- Comparison from the algebraic-space kernel pair of `sourceOver` and
`targetOver` to the Yoneda fibre product of the original source and target. -/
def kernelPairToOfOverPullback {S : Scheme.{u}} (G : GroupoidScheme S) :
    (pullback (sourceOver G) (targetOver G)).left ⟶ ofOverPullback G.s G.t :=
  (pullback.lift (pullback.fst (sourceOver G) (targetOver G)).left
      (pullback.snd (sourceOver G) (targetOver G)).left sorry :
    (pullback (sourceOver G) (targetOver G)).left.functorOfPoints ⟶
      pullback (yoneda.map G.s) (yoneda.map G.t))

/-- The composition morphism of a groupoid scheme, as a morphism of algebraic
spaces out of the kernel pair. -/
def composeOver {S : Scheme.{u}} (G : GroupoidScheme S) :
    pullback (sourceOver G) (targetOver G) ⟶ arrowOver G :=
  Over.homMk
    (kernelPairToOfOverPullback G ≫ (ofOverPullbackIso G.s G.t).inv ≫ ofOverMap G.c)
    sorry

/-- A groupoid scheme over `S`, regarded as a groupoid in algebraic spaces over
`S` by applying `ofOver` to objects, arrows, and structure maps. -/
def ofScheme {S : Scheme.{u}} (G : GroupoidScheme S) :
    GroupoidAlgebraicSpace (ofOver (Over.mk (𝟙 S))) where
  U := objectOver G
  R := arrowOver G
  s := sourceOver G
  t := targetOver G
  c := composeOver G
  e := identityOver G
  i := inverseOver G
  comp_source := sorry
  comp_target := sorry
  identity_source := sorry
  identity_target := sorry
  inverse_source := sorry
  inverse_target := sorry
  associativity := sorry
  right_identity := sorry
  left_identity := sorry
  inverse_comp := sorry
  comp_inverse := sorry

/-- The object space of `ofScheme G` is `ofOver` of the object scheme. -/
theorem ofScheme_U {S : Scheme.{u}} (G : GroupoidScheme S) :
    (ofScheme G).U.left = ofOver G.U := sorry

/-- The arrow space of `ofScheme G` is `ofOver` of the arrow scheme. -/
theorem ofScheme_R {S : Scheme.{u}} (G : GroupoidScheme S) :
    (ofScheme G).R.left = ofOver G.R := sorry

/-- The ring of invariant functions of an affine groupoid presentation, as the
equalizer of the target and source comorphisms. -/
abbrev invariantFunctions {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
    (tSharp : A →+* B) : Subring A :=
  tSharp.eqLocus (algebraMap A B)

/-- Inverses of invariant functions remain invariant when the object ring is a field. -/
theorem invariantFunctions.inv_mem {A B : Type u} [Field A] [CommRing B] [Algebra A B]
    (tSharp : A →+* B) {x : A} (hx : x ∈ invariantFunctions tSharp) :
    x⁻¹ ∈ invariantFunctions tSharp := sorry

/-- If the object ring of an affine groupoid presentation is a field, then the
ring of invariant functions is a field. -/
instance instFieldInvariantFunctions {A B : Type u} [Field A] [CommRing B] [Algebra A B]
    (tSharp : A →+* B) : Field (invariantFunctions tSharp) where
  inv x := ⟨x.val⁻¹, invariantFunctions.inv_mem tSharp x.property⟩
  exists_pair_ne := sorry
  mul_inv_cancel := sorry
  inv_zero := sorry
  nnqsmul := _
  qsmul := _

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

/-- The quotient morphism from the object scheme to the invariant spectrum. -/
abbrev invariantSpectrumQuotient :
    P.U ⟶ invariantSpectrum P tSharp eU eR h_source h_target :=
  GroupoidScheme.invariantSpectrumQuotientMap P tSharp eU
    (GroupoidScheme.invariantSpectrumMap_effectiveEpi P tSharp eU eR h_source h_target)
    (GroupoidScheme.invariantSpectrumMap_respectsBase P tSharp eU eR h_source h_target)

/-- The atlas of `[U/R]`, pulled back along the slice comparison of the object
scheme of `G`. -/
def atlasFromSlice : GroupoidsOver.slice G.U ⟶ (ofScheme G).quotientStack :=
  (ofOverSliceEquiv G.U).inv ≫ (ofScheme G).atlas

/-- The atlas of `[U/R]` transported along an identification of object schemes. -/
def atlasFromSlice_eqToHom :
    GroupoidsOver.slice P.U ⟶ (ofScheme G).quotientStack :=
  eqToHom (congrArg (fun W ↦ GroupoidsOver.slice W) hU) ≫ atlasFromSlice G

/-- `atlasFromSlice_eqToHom` is the atlas of `G` after `eqToHom` on slices. -/
theorem atlasFromSlice_eqToHom_eq :
    atlasFromSlice_eqToHom P G hU =
      eqToHom (congrArg (fun W ↦ GroupoidsOver.slice W) hU) ≫ atlasFromSlice G :=
  sorry

/-- The invariant-spectrum quotient equalizes the target and source maps of `P`. -/
theorem invariantSpectrumQuotient_equalizes :
    P.toPreRelation.t ≫ invariantSpectrumQuotient P tSharp eU eR h_source h_target =
      P.toPreRelation.s ≫ invariantSpectrumQuotient P tSharp eU eR h_source h_target :=
  sorry

/-- The kernel pair of `U ⟶ Ū` is the identity-component equivalence relation `P`. -/
theorem invariantSpectrum_kernelPair :
    IsIso
      (P.toPreRelation.kernelPairLift
        (invariantSpectrumQuotient P tSharp eU eR h_source h_target)
        (invariantSpectrumQuotient_equalizes P tSharp eU eR h_source h_target)) :=
  GroupoidScheme.invariantKernelPairComparison_isIso P tSharp eU eR h_source h_target

/-- The underlying scheme of the invariant spectrum is the spectrum of the ring of
invariant functions. -/
theorem invariantSpectrum_left :
    (invariantSpectrum P tSharp eU eR h_source h_target).left =
      Spec (CommRingCat.of (invariantFunctions tSharp)) :=
  sorry

/-- The identity `G.U`-point, as an object of the groupoid fibration of the object
space of `G`. -/
def identityPoint : (ofOver G.U).toGroupoids.total :=
  Opposite.op ⟨Opposite.op G.U, 𝟙 G.U⟩

/-- The atlas object of `[U/R]` over the object scheme of `G`. -/
def atlasObject : (ofScheme G).quotientStack.total :=
  (toFunctor (ofScheme G).atlas).obj (identityPoint G)

/-- The atlas object of `[U/R]`, as a standard fibre object over `G.U`. -/
def atlasFiber : (ofScheme G).quotientStack.p.Fiber G.U :=
  Functor.Fiber.mk
    (congrArg (fun F ↦ F.obj (identityPoint G)) (toBasedFunctor (ofScheme G).atlas).w)

/-- The cleavage of `[U/R]` selected from its fibreing. -/
def quotientCleavage : (ofScheme G).quotientStack.p.Cleavage :=
  Functor.Cleavage.ofIsFibered (ofScheme G).quotientStack.p

/-- The atlas fibre of `G`, reindexed along the identification `P.U = G.U`. -/
def atlasFiberOnP : (ofScheme G).quotientStack.p.Fiber P.U :=
  (quotientCleavage G).reindexObj (eqToHom hU) (atlasFiber G)

/-- The kernel-pair comparison of `U ⟶ Ū` is an isomorphism, so a pair of maps to `U`
over `Ū` determines an arrow of `P`. -/
def relationLift (ι : GroupoidScheme.Hom P G) {Y : Over S} (f₁ f₂ : Y ⟶ P.U)
    (hf : f₁ ≫ invariantSpectrumQuotient P tSharp eU eR h_source h_target =
      f₂ ≫ invariantSpectrumQuotient P tSharp eU eR h_source h_target) :
    Y ⟶ G.R :=
  pullback.lift f₁ f₂ hf ≫
    (GroupoidScheme.invariantKernelPairIso P tSharp eU eR h_source h_target).inv ≫
    ι.arrow

/-- A `T`-valued point of the object scheme of `G`, as an object of `[U /ₚ R]`. -/
def preQuotientPoint {Y : Over S} (f : Y ⟶ G.U) :
    (ofScheme G).preQuotient.total :=
  { base := Y
    fiber := f }

/-- The morphism of `[U /ₚ R]` over `Y` induced by an arrow of `R`. -/
def preQuotientHom {Y : Over S} {f₁ f₂ : Y ⟶ G.U} (r : Y ⟶ G.R)
    (hs : r ≫ G.s = f₁) (ht : r ≫ G.t = f₂) :
    preQuotientPoint G f₁ ⟶ preQuotientPoint G f₂ :=
  { base := 𝟙 Y
    fiber := FunctorPointHom.ofArrow r sorry sorry }

/-- The image of a `T`-valued point of `U` under the atlas of `[U/R]`. -/
def atlasPoint {Y : Over S} (f : Y ⟶ G.U) : (ofScheme G).quotientStack.total :=
  (toFunctor (ofScheme G).stackificationHom).obj (preQuotientPoint G f)

/-- The total-category morphism of `[U/R]` induced by a `P`-arrow between two maps
to `U` over `Ū`. -/
def atlasDescentHom (ι : GroupoidScheme.Hom P G)
    (hι : ι.IsIdentityOnObjects hU) {Y : Over S} (f₁ f₂ : Y ⟶ P.U)
    (hf : f₁ ≫ invariantSpectrumQuotient P tSharp eU eR h_source h_target =
      f₂ ≫ invariantSpectrumQuotient P tSharp eU eR h_source h_target) :
    atlasPoint G (f₁ ≫ eqToHom hU) ⟶ atlasPoint G (f₂ ≫ eqToHom hU) :=
  (toFunctor (ofScheme G).stackificationHom).map
    (preQuotientHom G (relationLift P G tSharp eU eR h_source h_target ι f₁ f₂ hf)
      sorry sorry)


/-- The projection of `atlasPoint f` is the test scheme of `f`. -/
theorem atlasPoint_p {Y : Over S} (f : Y ⟶ G.U) :
    (ofScheme G).quotientStack.p.obj (atlasPoint G f) = Y := sorry

/-- The atlas point of `f`, as a standard fibre object. -/
def atlasPointFiber {Y : Over S} (f : Y ⟶ G.U) :
    (ofScheme G).quotientStack.p.Fiber Y :=
  ⟨atlasPoint G f, atlasPoint_p G f⟩

/-- The underlying total object of `atlasPointFiber f` is `atlasPoint f`. -/
theorem atlasPointFiber_obj {Y : Over S} (f : Y ⟶ G.U) :
    Functor.Fiber.fiberInclusion.obj (atlasPointFiber G f) = atlasPoint G f := sorry

/-- Reindexing the atlas fibre of `P` along `f : Y ⟶ U` is the atlas point of `f`. -/
theorem atlasReindex_eq_atlasPoint {Y : Over S} (f : Y ⟶ P.U) :
    ((Functor.fiberPseudofunctor (ofScheme G).quotientStack.p).map f.op.toLoc).toFunctor.obj
        (atlasFiberOnP P G hU) =
      atlasPointFiber G (f ≫ eqToHom hU) := sorry

/-- Descent data for the atlas of `[U/R]` along the fppf cover `U ⟶ Ū`, using that
`P` is identity-on-objects in `G`. -/
def atlasDescentData (ι : GroupoidScheme.Hom P G)
    (hι : ι.IsIdentityOnObjects hU) :
    (Functor.fiberPseudofunctor (ofScheme G).quotientStack.p).DescentData
      (fun _ : Unit ↦ invariantSpectrumQuotient P tSharp eU eR h_source h_target) where
  obj _ := atlasFiberOnP P G hU
  hom Y q i₁ i₂ f₁ f₂ hf₁ hf₂ :=
    eqToHom (atlasReindex_eq_atlasPoint P G hU f₁) ≫
      Functor.Fiber.Hom.mk
        (eqToHom (atlasPointFiber_obj G (f₁ ≫ eqToHom hU)) ≫
          atlasDescentHom P G tSharp eU eR h_source h_target hU ι hι f₁ f₂
            (hf₁.trans hf₂.symm) ≫
          eqToHom (atlasPointFiber_obj G (f₂ ≫ eqToHom hU)).symm)
        sorry ≫
      eqToHom (atlasReindex_eq_atlasPoint P G hU f₂).symm
  pullHom_hom := sorry
  hom_self := sorry
  hom_comp := sorry

/-- The single arrow `U ⟶ Ū` generates an fppf covering sieve. -/
theorem invariantSpectrumQuotient_covers :
    Sieve.ofArrows (fun _ : Unit ↦ P.U)
        (fun _ ↦ invariantSpectrumQuotient P tSharp eU eR h_source h_target) ∈
      Scheme.fppfTopology.over S
        (invariantSpectrum P tSharp eU eR h_source h_target) :=
  sorry

/-- Effective descent for the atlas cover `U ⟶ Ū` in `[U/R]`. -/
instance instIsEquivalence_atlasDescentData :
    ((Functor.fiberPseudofunctor (ofScheme G).quotientStack.p).toDescentData
        (fun _ : Unit ↦
          invariantSpectrumQuotient P tSharp eU eR h_source h_target)).IsEquivalence :=
  Pseudofunctor.isEquivalence_toDescentData _
    (fun _ : Unit ↦ invariantSpectrumQuotient P tSharp eU eR h_source h_target)
    (invariantSpectrumQuotient_covers P tSharp eU eR h_source h_target)

/-- The descended atlas object of `[U/R]` over `Ū`. -/
def atlasDescentObject (ι : GroupoidScheme.Hom P G)
    (hι : ι.IsIdentityOnObjects hU) :
    (ofScheme G).quotientStack.p.Fiber
      (invariantSpectrum P tSharp eU eR h_source h_target) :=
  ((Functor.fiberPseudofunctor (ofScheme G).quotientStack.p).toDescentData
        (fun _ : Unit ↦
          invariantSpectrumQuotient P tSharp eU eR h_source h_target)).inv.obj
    (atlasDescentData P G tSharp eU eR h_source h_target hU ι hι)

/-- The functor on total categories sending a `T`-point of `Ū` to the cartesian
reindexing of the descended atlas. -/
def invariantSpectrumToOverQuotientFunctor (ι : GroupoidScheme.Hom P G)
    (hι : ι.IsIdentityOnObjects hU) :
    (ofOver (invariantSpectrum P tSharp eU eR h_source h_target)).toGroupoids.total ⥤
      (ofScheme G).quotientStack.total where
  obj x :=
    ((quotientCleavage G).reindexObj x.unop.snd
      (atlasDescentObject P G tSharp eU eR h_source h_target hU ι hι)).1
  map {x y} f :=
    Functor.Cleavage.SliceSection.map (quotientCleavage G)
      (atlasDescentObject P G tSharp eU eR h_source h_target hU ι hι)
      (a := Over.mk x.unop.snd) (b := Over.mk y.unop.snd)
      (Over.homMk f.unop.val.unop sorry)
  map_id := sorry
  map_comp := sorry

/-- The functor `invariantSpectrumToOverQuotientFunctor` lies over `Over S`. -/
theorem invariantSpectrumToOverQuotientFunctor_w (ι : GroupoidScheme.Hom P G)
    (hι : ι.IsIdentityOnObjects hU) :
    invariantSpectrumToOverQuotientFunctor P G tSharp eU eR h_source h_target hU ι hι ⋙
        (ofScheme G).quotientStack.p =
      (ofOver (invariantSpectrum P tSharp eU eR h_source h_target)).toGroupoids.p :=
  sorry

/-- The canonical 1-morphism `(ofOver Ū).toGroupoids ⟶ [U/R]` whose value on a
`T`-point of `Ū` is the cartesian reindexing of the descended atlas. -/
def invariantSpectrumToOverQuotient (ι : GroupoidScheme.Hom P G)
    (hι : ι.IsIdentityOnObjects hU) :
    (ofOver (invariantSpectrum P tSharp eU eR h_source h_target)).toGroupoids ⟶
      (ofScheme G).quotientStack :=
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
      (ofScheme G).quotientStack :=
  (ofOverSliceEquiv (invariantSpectrum P tSharp eU eR h_source h_target)).inv ≫
    invariantSpectrumToOverQuotient P G tSharp eU eR h_source h_target hU ι hι

/-- Precomposition with `U ⟶ Ū` recovers the atlas of `[U/R]` up to a 2-isomorphism. -/
theorem invariantSpectrumToQuotient_comp_atlas (ι : GroupoidScheme.Hom P G)
    (hι : ι.IsIdentityOnObjects hU) :
    Nonempty
      (overMap (invariantSpectrumQuotient P tSharp eU eR h_source h_target) ≫
          invariantSpectrumToQuotient P G tSharp eU eR h_source h_target hU ι hι ≅
        atlasFromSlice_eqToHom P G hU) :=
  sorry

/-- A 1-morphism `Ū ⟶ [U/R]` through which the atlas of `G` factors along `U ⟶ Ū`
is unique up to a unique 2-isomorphism. -/
theorem invariantSpectrumToQuotient_unique (ι : GroupoidScheme.Hom P G)
    (hι : ι.IsIdentityOnObjects hU)
    {toQuotient toQuotient' :
      GroupoidsOver.slice (invariantSpectrum P tSharp eU eR h_source h_target) ⟶
        (ofScheme G).quotientStack}
    (h_toQuotient :
      overMap (invariantSpectrumQuotient P tSharp eU eR h_source h_target) ≫
          toQuotient ≅
        atlasFromSlice_eqToHom P G hU)
    (h_toQuotient' :
      overMap (invariantSpectrumQuotient P tSharp eU eR h_source h_target) ≫
          toQuotient' ≅
        atlasFromSlice_eqToHom P G hU) :
    ∃! β : toQuotient ≅ toQuotient',
      (pullbackFunctor
            (invariantSpectrumQuotient P tSharp eU eR h_source h_target)).mapIso β ≪≫
          h_toQuotient' =
        h_toQuotient :=
  sorry

end AlgebraicGeometry.GroupoidAlgebraicSpace
