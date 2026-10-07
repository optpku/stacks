module

public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs
public import ReasLib.CategoryTheory.Fibered.Inertia.Cartesian.Map.Absolute.Construction
public import ReasLib.CategoryTheory.Fibered.Stack.Inertia.Groupoids.AbsoluteMaps
public import ReasLib.CategoryTheory.Inertia.Relative
public import stacks_project.Chap78.Lemma_78_25_3_Square
public import stacks_project.Chap78.Lemma_78_26_1_Comparison
public import stacks_project.Chap78.Lemma_78_26_1_Presentation

/-!
# Stabilizer square of a quotient stack

A groupoid in algebraic spaces determines a morphism of groupoids from the inertia
presentation `(G, R')` to `(U, R)`, cartesian functors `𝒮_G ⟶ I_{[U/R]}` and
`𝒮_G ⟶ 𝒮_U`, and the cospan `I_{[U/R]} ⟶ [U/R] ← 𝒮_U`. After aligning Hom-universes
these form a cone on `(inertia.forget, atlas)`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.GroupoidAlgebraicSpace CategoryTheory.Limits Opposite
open CategoryTheory.Bicategory CategoryTheory.Functor
open Functor.IsFibered.InGroupoids.Stackification
open CategoryTheory.Pseudofunctor.CoGrothendieck
open scoped CategoryTheory.Bicategory CategoryTheory.Pseudofunctor.StrongTrans

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidAlgebraicSpace

variable {S : Scheme.{u}} {B : AlgebraicSpace S} (G : GroupoidAlgebraicSpace B)

/-- The canonical morphism of groupoids `(G, R', s', t', c') ⟶ (U, R, s, t, c)` with object
map the structure morphism of the stabilizer and arrow map the first projection of
`R' = R ×_{s, U} G`. -/
def inertiaHom : Hom (inertiaPresentation G) G where
  obj := G.toPreRelation.stabilizer.hom
  arrow := pullback.fst G.s G.toPreRelation.stabilizer.hom
  map_s := pullback.condition.symm
  map_t := sorry
  map_c := sorry

/-- The object component of `inertiaHom` is the structure morphism of the stabilizer. -/
theorem inertiaHom_obj : (inertiaHom G).obj = G.toPreRelation.stabilizer.hom := sorry

/-- The arrow component of `inertiaHom` is the first projection of `R ×_{s, U} G`. -/
theorem inertiaHom_arrow :
    (inertiaHom G).arrow = pullback.fst G.s G.toPreRelation.stabilizer.hom := sorry

/-- The source square of `inertiaHom` is the defining pullback square of `R'`. -/
theorem inertiaHom_isPullback :
    IsPullback (inertiaHom G).arrow (inertiaPresentation G).s G.s (inertiaHom G).obj :=
  sorry

/-- The scheme-valued arrow of `R` carried by a point of the stabilizer. -/
def stabilizerArrowPoint
    (x : (stackInSets (inertiaPresentation G).U.left).total) :
    ofOver x.unop.fst.unop ⟶ G.R.left :=
  yonedaEquiv.symm x.unop.snd ≫ G.toPreRelation.stabilizerToArrows.left

/-- The object of `[U/_p R]` associated to a point of the stabilizer, via the atlas of
`(U, R)`. -/
def stabilizerPreInertiaObj
    (x : (stackInSets (inertiaPresentation G).U.left).total) :
    (preQuotient G).total :=
  (atlasToPreQuotientFunctor G).obj
    ((stackInSets.map G.toPreRelation.stabilizer.hom.left).toFunctor.obj x)

/-- The automorphism of `stabilizerPreInertiaObj` with underlying arrow the stabilizer
element. -/
def stabilizerPreInertiaAutHom
    (x : (stackInSets (inertiaPresentation G).U.left).total) :
    stabilizerPreInertiaObj G x ⟶ stabilizerPreInertiaObj G x where
  base := 𝟙 (stabilizerPreInertiaObj G x).base
  fiber :=
    SpacePointHom.ofArrow (stabilizerArrowPoint G x) sorry sorry

/-- The inverse automorphism of `stabilizerPreInertiaObj`, using groupoid inversion. -/
def stabilizerPreInertiaAutInv
    (x : (stackInSets (inertiaPresentation G).U.left).total) :
    stabilizerPreInertiaObj G x ⟶ stabilizerPreInertiaObj G x where
  base := 𝟙 (stabilizerPreInertiaObj G x).base
  fiber :=
    SpacePointHom.ofArrow (stabilizerArrowPoint G x ≫ G.i.left) sorry sorry

/-- The chosen automorphism of the atlas image of a stabilizer point. -/
def stabilizerPreInertiaAut
    (x : (stackInSets (inertiaPresentation G).U.left).total) :
    Aut (stabilizerPreInertiaObj G x) where
  hom := stabilizerPreInertiaAutHom G x
  inv := stabilizerPreInertiaAutInv G x
  hom_inv_id := sorry
  inv_hom_id := sorry

/-- The object of `I_{[U/_p R]}` sending a `T`-point of the stabilizer to the pair
consisting of its atlas image in `[U/_p R]` and the automorphism given by
`stabilizerToArrows`. -/
def stabilizerToPreInertiaObj
    (x : (stackInSets (inertiaPresentation G).U.left).total) :
    RelativeInertia (preQuotient G).p where
  obj := stabilizerPreInertiaObj G x
  aut := stabilizerPreInertiaAut G x
  mapAut_eq_one := sorry

/-- The morphism of `I_{[U/_p R]}` induced by a morphism of `𝒮_G`. -/
def stabilizerToPreInertiaMap
    {x y : (stackInSets (inertiaPresentation G).U.left).total} (φ : x ⟶ y) :
    stabilizerToPreInertiaObj G x ⟶ stabilizerToPreInertiaObj G y :=
  let f : (stabilizerToPreInertiaObj G x).obj ⟶ (stabilizerToPreInertiaObj G y).obj :=
    (atlasToPreQuotientFunctor G).map
      ((stackInSets.map G.toPreRelation.stabilizer.hom.left).toFunctor.map φ)
  RelativeInertia.homMk (preQuotient G).p f sorry

/-- The total functor `𝒮_G ⟶ I_{[U/_p R]}`. -/
def stabilizerToPreInertiaFunctor :
    (stackInSets (inertiaPresentation G).U.left).total ⥤
      RelativeInertia (preQuotient G).p where
  obj := stabilizerToPreInertiaObj G
  map := stabilizerToPreInertiaMap G
  map_id := sorry
  map_comp := sorry

/-- `stabilizerToPreInertiaFunctor` commutes with projection to `(Sch/S)_fppf`. -/
theorem stabilizerToPreInertia_comm :
    stabilizerToPreInertiaFunctor G ⋙
        RelativeInertia.projection (preQuotient G).p (preQuotient G).p =
      (stackInSets (inertiaPresentation G).U.left).p :=
  sorry

/-- The cartesian `1`-morphism `𝒮_G ⟶ I_{[U/_p R]}`. -/
def stabilizerToPreInertia :
    CartesianBasedFunctor (stackInSets (inertiaPresentation G).U.left).p
      (BasedCategory.inertia
        (BasedCategory.ofFunctor (preQuotient G).p)).p :=
  CartesianBasedFunctor.ofTargetInGroupoids
    (BasedFunctor.ofFunctor (stabilizerToPreInertiaFunctor G)
      (stabilizerToPreInertia_comm G))

/-- The cartesian `1`-morphism `𝒮_G ⟶ I_{[U/R]}` obtained by applying inertia of the
selected fppf stackification comparison. -/
def stabilizerToInertia :
    CartesianBasedFunctor (stackInSets (inertiaPresentation G).U.left).p
      (BasedCategory.inertia
        (BasedCategory.ofFunctor (fppfQuotientStack G).p)).p :=
  (stabilizerToPreInertia G).comp
    (CartesianBasedFunctor.Inertia.map (fppfQuotientStackPresentation G).comparison)

/-- Universe-aligned cartesian form of `𝒮_G ⟶ I_{[U/R]}`. -/
def stabilizerToInertiaULift :
    CartesianBasedFunctor (stackInSetsULift (inertiaPresentation G).U.left).p
      (BasedCategory.inertia
        (BasedCategory.ofFunctor (fppfQuotientStack G).p)).p :=
  (stackInSetsULift.down (inertiaPresentation G).U.left).comp (stabilizerToInertia G)

/-- The cartesian forgetful functor `I_{[U/R]} ⟶ [U/R]` of the selected fppf quotient stack. -/
def inertiaForgetCartesian :
    CartesianBasedFunctor
      (BasedCategory.inertia
        (BasedCategory.ofFunctor (fppfQuotientStack G).p)).p
      (fppfQuotientStack G).p :=
  CartesianBasedFunctor.ofTargetInGroupoids
    (BasedCategory.Inertia.forget
      (BasedCategory.ofFunctor (fppfQuotientStack G).p))

/-- After forgetting automorphisms, `stabilizerToInertia` is the atlas of the image of
the stabilizer in `U`. -/
theorem stabilizerToInertia_comp_forget :
    (stabilizerToInertia G).comp (inertiaForgetCartesian G) =
      (stackInSets.map G.toPreRelation.stabilizer.hom.left).comp (fppfAtlas G) :=
  sorry

/-- The left vertical arrow `𝒮_G ⟶ I_{[U/R]}` of the stabilizer square, as a morphism of
stacks in groupoids. -/
def inertiaConeFst :
    stackInSetsULift (inertiaPresentation G).U.left ⟶
      StackOver.Groupoids.inertia.{u + 1, u, u + 1, u + 1} (fppfQuotientStack G) :=
  StackOver.Groupoids.Hom.lift
    (FiberedCategoryOver.Groupoids.ofBasedFunctor
      (stabilizerToInertiaULift G).toBasedFunctor)

/-- The top arrow `𝒮_G ⟶ 𝒮_U` of the stabilizer square. -/
def inertiaConeSnd :
    stackInSetsULift (inertiaPresentation G).U.left ⟶ stackInSetsULift G.U.left :=
  stackInSetsULift.map (inertiaHom G).obj.left

/-- The top arrow of the stabilizer square is `𝒮` of the structure morphism of the
stabilizer. -/
theorem inertiaConeSnd_eq :
    inertiaConeSnd G =
      stackInSetsULift.map G.toPreRelation.stabilizer.hom.left :=
  sorry

/-- The forgetful arrow `I_{[U/R]} ⟶ [U/R]` of the stabilizer square. -/
def inertiaConeRight :
    StackOver.Groupoids.inertia.{u + 1, u, u + 1, u + 1} (fppfQuotientStack G) ⟶
      fppfQuotientStack G :=
  StackOver.Groupoids.inertia.forget.{u + 1, u, u + 1, u + 1} (fppfQuotientStack G)

/-- The atlas `𝒮_U ⟶ [U/R]` of the stabilizer square. -/
def inertiaConeBottom :
    stackInSetsULift G.U.left ⟶ fppfQuotientStack G :=
  atlasULiftHom G

/-- The cartesian functors underlying the two paths around the stabilizer square agree. -/
theorem inertiaIsoULift_eq :
    StackOver.Groupoids.Hom.toCartesianBasedFunctor
        (inertiaConeFst G ≫ inertiaConeRight G) =
      StackOver.Groupoids.Hom.toCartesianBasedFunctor
        (inertiaConeSnd G ≫ inertiaConeBottom G) :=
  sorry

/-- The cartesian-level naturality `2`-isomorphism of the two paths around the stabilizer
square. -/
def inertiaIsoULift :
    StackOver.Groupoids.Hom.toCartesianBasedFunctor
        (inertiaConeFst G ≫ inertiaConeRight G) ≅
      StackOver.Groupoids.Hom.toCartesianBasedFunctor
        (inertiaConeSnd G ≫ inertiaConeBottom G) :=
  eqToIso (inertiaIsoULift_eq G)

/-- The packaged `2`-isomorphism of the stabilizer square. -/
def inertiaConeIso :
    inertiaConeFst G ≫ inertiaConeRight G ≅
      inertiaConeSnd G ≫ inertiaConeBottom G :=
  StackOver.Groupoids.Hom.isoMk
    (FiberedCategoryOver.Groupoids.BasedFunctorIso.lift
      (CartesianBasedFunctor.toBasedIso (inertiaIsoULift G)))

/-- The `2`-commutative square with apex `𝒮_G`, first leg `𝒮_G ⟶ I_{[U/R]}`, second leg
`𝒮_G ⟶ 𝒮_U`, and cospan `(I_{[U/R]} ⟶ [U/R], 𝒮_U ⟶ [U/R])`. -/
def inertiaCone :
    PseudoPullbackCone (inertiaConeRight G) (inertiaConeBottom G) where
  pt := stackInSetsULift (inertiaPresentation G).U.left
  fst := inertiaConeFst G
  snd := inertiaConeSnd G
  iso := inertiaConeIso G

/-- The apex of `inertiaCone G` is `𝒮_G`. -/
theorem inertiaCone_pt :
    (inertiaCone G).pt = stackInSetsULift (inertiaPresentation G).U.left := sorry

/-- The first projection of `inertiaCone G` is `𝒮_G ⟶ I_{[U/R]}`. -/
theorem inertiaCone_fst : (inertiaCone G).fst = inertiaConeFst G := sorry

/-- The second projection of `inertiaCone G` is `𝒮_G ⟶ 𝒮_U`. -/
theorem inertiaCone_snd : (inertiaCone G).snd = inertiaConeSnd G := sorry

/-- The `2`-cell of `inertiaCone G` is `inertiaConeIso G`. -/
theorem inertiaCone_iso : (inertiaCone G).iso = inertiaConeIso G := sorry

end AlgebraicGeometry.GroupoidAlgebraicSpace

