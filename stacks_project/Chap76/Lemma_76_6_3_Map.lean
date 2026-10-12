/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Conormal.CommRingAdjunction

public import stacks_project.Chap76.Definition_76_6_5_Conormal
public import stacks_project.Chap76.«76_6_1_1_Piece»
public import stacks_project.Chap76.Lemma_76_5_3_Map

/-!
# Functoriality of total conormal algebras of immersions of algebraic spaces

A commutative square of algebraic spaces whose horizontal arrows are immersions
induces a canonical morphism of quasi-coherent `𝒪_Z`-algebras
`f^* C_{Z'/X',*} ⟶ C_{Z/X,*}`. The domain is the inverse-image-plus-pushout of
`ConormalAlgebra.total i'` along `f`, matching the construction of `total`. The
comparison is assembled from `Ideal.AssociatedGraded.map` after reduction to
closed immersions on `Hom.Conormal.compatibleOpen`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor CategoryTheory.ConcreteCategory Opposite
open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open SheafOfModules.RingedSite

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.ConormalAlgebra

variable {S : Scheme.{u}}

/-- The total conormal algebra sheaf of `i'`, pulled back along `f` by inverse image of
commutative-ring sheaves and pushout along the inverse-image structure map. -/
noncomputable def pullbackSheaf {Z Z' X' : AlgebraicSpace S}
    (f : Z ⟶ Z') (i' : Z' ⟶ X') [IsImmersion i'] :
    Sheaf (smallEtaleTopology Z) CommRingCat.{u} :=
  pushout (inverseImageStructureSheafHom f)
    ((commRingInverseImage f).map (structureMap i'))

/-- `pullbackSheaf f i'` is the indicated pushout of inverse-image structure and total
conormal algebra data. -/
theorem pullbackSheaf_eq {Z Z' X' : AlgebraicSpace S}
    (f : Z ⟶ Z') (i' : Z' ⟶ X') [IsImmersion i'] :
    pullbackSheaf f i' =
      pushout (inverseImageStructureSheafHom f)
        ((commRingInverseImage f).map (structureMap i')) :=
  rfl

/-- The structure map making `f^* C_{Z'/X',*}` an `𝒪_Z`-algebra. -/
noncomputable def pullbackStructureMap {Z Z' X' : AlgebraicSpace S}
    (f : Z ⟶ Z') (i' : Z' ⟶ X') [IsImmersion i'] :
    commRingStructureSheaf Z ⟶ pullbackSheaf f i' :=
  pushout.inl (inverseImageStructureSheafHom f)
    ((commRingInverseImage f).map (structureMap i'))

/-- The structure map of the pulled-back total conormal algebra is the first pushout
inclusion. -/
theorem pullbackStructureMap_eq {Z Z' X' : AlgebraicSpace S}
    (f : Z ⟶ Z') (i' : Z' ⟶ X') [IsImmersion i'] :
    pullbackStructureMap f i' =
      pushout.inl (inverseImageStructureSheafHom f)
        ((commRingInverseImage f).map (structureMap i')) :=
  rfl

/-- The inverse image `f^* C_{Z'/X',*}` of a total conormal algebra, as a quasi-coherent
`𝒪_Z`-algebra. -/
noncomputable def pullback {Z Z' X' : AlgebraicSpace S}
    (f : Z ⟶ Z') (i' : Z' ⟶ X') [IsImmersion i'] : Z.QcAlgebraUnder where
  obj := Under.mk (pullbackStructureMap f i')
  property := sorry

/-- The underlying `𝒪_Z`-algebra of `pullback f i'` is `Under.mk` of its structure map. -/
theorem pullback_obj {Z Z' X' : AlgebraicSpace S}
    (f : Z ⟶ Z') (i' : Z' ⟶ X') [IsImmersion i'] :
    (pullback f i').obj = Under.mk (pullbackStructureMap f i') :=
  rfl

/-- The right-hand sheaf of `pullback f i'` is `pullbackSheaf f i'`. -/
theorem pullback_sheaf {Z Z' X' : AlgebraicSpace S}
    (f : Z ⟶ Z') (i' : Z' ⟶ X') [IsImmersion i'] :
    (pullback f i').obj.right = pullbackSheaf f i' :=
  rfl

/-- `f^* C_{Z'/X',*}` is the pushout of `j^{-1} 𝒪_{Z'} ⟶ 𝒪_Z` against the inverse image of
the total conormal algebra of `i'`. -/
theorem pullback_spec {Z Z' X' : AlgebraicSpace S}
    (f : Z ⟶ Z') (i' : Z' ⟶ X') [IsImmersion i'] :
    (pullback f i').obj = Under.mk (pullbackStructureMap f i') ∧
      pullbackSheaf f i' =
        pushout (inverseImageStructureSheafHom f)
          ((commRingInverseImage f).map (structureMap i')) :=
  sorry

/-- The ideal-power `I^n ⊂ 𝒪_X` of the kernel ideal of a closed immersion. -/
noncomputable def closedIdealPower {Z X : AlgebraicSpace S}
    (i : Z ⟶ X) [IsClosedImmersion i] (n : ℕ) : IdealSubobject X :=
  Modules.idealPowerProductSubobject (Hom.idealSheafSubobject i)
    (SheafOfModules.unit (structureSheaf X)) n

/-- `closedIdealPower i n` is the ideal-power product of the kernel ideal of `i`. -/
theorem closedIdealPower_eq {Z X : AlgebraicSpace S}
    (i : Z ⟶ X) [IsClosedImmersion i] (n : ℕ) :
    closedIdealPower i n =
      Modules.idealPowerProductSubobject (Hom.idealSheafSubobject i)
        (SheafOfModules.unit (structureSheaf X)) n :=
  rfl

/-- The successive quotient `I^n / I^{n+1}` of a closed immersion, as an `𝒪_X`-module. -/
noncomputable def closedQuotient {Z X : AlgebraicSpace S}
    (i : Z ⟶ X) [IsClosedImmersion i] (n : ℕ) : X.Modules :=
  Modules.quotientByIdeal (Hom.idealSheafSubobject i) (closedIdealPower i n).toModule

/-- `closedQuotient i n` is the quotient of `I^n` by the action of `I`. -/
theorem closedQuotient_eq {Z X : AlgebraicSpace S}
    (i : Z ⟶ X) [IsClosedImmersion i] (n : ℕ) :
    closedQuotient i n =
      Modules.quotientByIdeal (Hom.idealSheafSubobject i)
        (closedIdealPower i n).toModule :=
  rfl

/-- The coborder successive quotient is the closed-immersion successive quotient of the
coborder lift. -/
theorem closedQuotient_liftCoborder {Z X : AlgebraicSpace S}
    (i : Z ⟶ X) [IsImmersion i] (n : ℕ) :
    closedQuotient (IsImmersion.liftCoborder i) n = coborderQuotient i n :=
  rfl

/-- The pulled-back power `g^* (I')^n` factors through `I^n`. -/
theorem pulledPower_factors {Z X Z' X' : AlgebraicSpace S}
    {f : Z ⟶ Z'} {i : Z ⟶ X} {i' : Z' ⟶ X'} {g : X ⟶ X'}
    [IsClosedImmersion i] [IsClosedImmersion i'] (sq : CommSq f i i' g) (n : ℕ) :
    (closedIdealPower i n).Factors
      (IdealSubobject.pullbackMap (closedIdealPower i' n) g) :=
  sorry

/-- The comparison `g^* (I')^n ⟶ I^n` of kernel-ideal powers of closed immersions in a
commutative square. -/
noncomputable def pulledPowerToPower {Z X Z' X' : AlgebraicSpace S}
    {f : Z ⟶ Z'} {i : Z ⟶ X} {i' : Z' ⟶ X'} {g : X ⟶ X'}
    [IsClosedImmersion i] [IsClosedImmersion i'] (sq : CommSq f i i' g) (n : ℕ) :
    (Modules.pullback g).obj (closedIdealPower i' n).toModule ⟶
      (closedIdealPower i n).toModule :=
  (closedIdealPower i n).factorThru
    (IdealSubobject.pullbackMap (closedIdealPower i' n) g) (pulledPower_factors sq n)

/-- The pulled power-sheaf action followed by `pulledPowerToPower ≫ π` is zero. -/
theorem pulledPowerAction_comp_π {Z X Z' X' : AlgebraicSpace S}
    {f : Z ⟶ Z'} {i : Z ⟶ X} {i' : Z' ⟶ X'} {g : X ⟶ X'}
    [IsClosedImmersion i] [IsClosedImmersion i'] (sq : CommSq f i i' g) (n : ℕ) :
    (Modules.pullback g).map
          (Modules.idealAction (Hom.idealSheafSubobject i') (closedIdealPower i' n).toModule) ≫
        pulledPowerToPower sq n ≫
          Modules.quotientByIdeal.π (Hom.idealSheafSubobject i) (closedIdealPower i n).toModule =
      0 :=
  sorry

/-- For closed immersions, the source comparison `g^{-1}((I')^n/(I')^{n+1}) ⟶ I^n/I^{n+1}`. -/
noncomputable def closedQuotientMap {Z X Z' X' : AlgebraicSpace S}
    {f : Z ⟶ Z'} {i : Z ⟶ X} {i' : Z' ⟶ X'} {g : X ⟶ X'}
    [IsClosedImmersion i] [IsClosedImmersion i'] (sq : CommSq f i i' g) (n : ℕ) :
    (Modules.pullback g).obj (closedQuotient i' n) ⟶ closedQuotient i n :=
  (PreservesCokernel.iso (Modules.pullback g)
      (Modules.idealAction (Hom.idealSheafSubobject i')
        (closedIdealPower i' n).toModule)).hom ≫
    cokernel.desc
      ((Modules.pullback g).map
        (Modules.idealAction (Hom.idealSheafSubobject i') (closedIdealPower i' n).toModule))
      (pulledPowerToPower sq n ≫
        Modules.quotientByIdeal.π (Hom.idealSheafSubobject i) (closedIdealPower i n).toModule)
      (pulledPowerAction_comp_π sq n)

/-- Restriction of the coborder successive quotient of `i` along the compatible open. -/
noncomputable def compatibleOpenQuotientMap {Z X Z' X' : AlgebraicSpace S}
    {f : Z ⟶ Z'} {i : Z ⟶ X} {i' : Z' ⟶ X'} {g : X ⟶ X'}
    [IsImmersion i] [IsImmersion i'] (sq : CommSq f i i' g) (n : ℕ) :
    (Modules.pullback (Hom.Conormal.compatibleOpenToCoborder i i' g)).obj
        (coborderQuotient i n) ⟶
      closedQuotient (Hom.Conormal.liftToCompatibleOpen sq) n :=
  closedQuotientMap (Hom.Conormal.coborderSq sq) n

/-- `compatibleOpenQuotientMap sq n` is the closed-immersion successive-quotient map of the
coborder square of `sq`. -/
theorem compatibleOpenQuotientMap_eq {Z X Z' X' : AlgebraicSpace S}
    {f : Z ⟶ Z'} {i : Z ⟶ X} {i' : Z' ⟶ X'} {g : X ⟶ X'}
    [IsImmersion i] [IsImmersion i'] (sq : CommSq f i i' g) (n : ℕ) :
    compatibleOpenQuotientMap sq n =
      closedQuotientMap (Hom.Conormal.coborderSq sq) n :=
  rfl

/-- Restriction of the coborder successive quotient along the compatible open is an
isomorphism. -/
instance instIsIso_compatibleOpenQuotientMap {Z X Z' X' : AlgebraicSpace S}
    {f : Z ⟶ Z'} {i : Z ⟶ X} {i' : Z' ⟶ X'} {g : X ⟶ X'}
    [IsImmersion i] [IsImmersion i'] (sq : CommSq f i i' g) (n : ℕ) :
    IsIso (compatibleOpenQuotientMap sq n) :=
  sorry

/-- The degree-`n` comparison `f^{-1} C_{Z'/X',n} ⟶ C_{Z/X,n}` induced by a commutative
square of immersions. -/
noncomputable def mapPiece {Z X Z' X' : AlgebraicSpace S}
    {f : Z ⟶ Z'} {i : Z ⟶ X} {i' : Z' ⟶ X'} {g : X ⟶ X'}
    [IsImmersion i] [IsImmersion i'] (sq : CommSq f i i' g) (n : ℕ) :
    (Modules.pullback f).obj (piece i' n) ⟶ piece i n :=
  (Modules.pullbackComp f (IsImmersion.liftCoborder i')).hom.app (coborderQuotient i' n) ≫
    (eqToIso (congrArg Modules.pullback (Hom.Conormal.restrictedSq sq).w)).hom.app
      (coborderQuotient i' n) ≫
    (Modules.pullbackComp (Hom.Conormal.liftToCompatibleOpen sq)
        (Hom.Conormal.restrictToCompatibleOpen i i' g)).inv.app
      (coborderQuotient i' n) ≫
    (Modules.pullback (Hom.Conormal.liftToCompatibleOpen sq)).map
      (closedQuotientMap (Hom.Conormal.restrictedSq sq) n) ≫
    (Modules.pullback (Hom.Conormal.liftToCompatibleOpen sq)).map
      (inv (compatibleOpenQuotientMap sq n)) ≫
    (Modules.pullbackComp (Hom.Conormal.liftToCompatibleOpen sq)
        (Hom.Conormal.compatibleOpenToCoborder i i' g)).hom.app
      (coborderQuotient i n) ≫
    (eqToIso (congrArg Modules.pullback
        (Hom.Conormal.liftToCompatibleOpen_comp_toCoborder sq))).hom.app
      (coborderQuotient i n)

/-- Restriction of sections carries the closed-immersion kernel ideal into the next kernel
ideal. -/
theorem closedKernel_sectionIdeal_le_comap {Z X : AlgebraicSpace S}
    (i : Z ⟶ X) [IsClosedImmersion i]
    {U V : (smallEtaleSite X)ᵒᵖ} (h : U ⟶ V) :
    KernelIdeal.sectionIdeal (commRingStructureSheafMap i) U ≤
      Ideal.comap (((commRingStructureSheaf X).obj.map h).hom)
        (KernelIdeal.sectionIdeal (commRingStructureSheafMap i) V) :=
  sorry

/-- The sectionwise associated graded ring of the kernel ideal of a closed immersion. -/
noncomputable def closedGradeObj {Z X : AlgebraicSpace S}
    (i : Z ⟶ X) [IsClosedImmersion i] (U : (smallEtaleSite X)ᵒᵖ) : CommRingCat.{u} :=
  CommRingCat.of
    (Ideal.AssociatedGraded.ring (KernelIdeal.sectionIdeal (commRingStructureSheafMap i) U))

/-- Restriction of the sectionwise closed-immersion associated graded rings. -/
noncomputable def closedGradeMap {Z X : AlgebraicSpace S}
    (i : Z ⟶ X) [IsClosedImmersion i] {U V : (smallEtaleSite X)ᵒᵖ} (h : U ⟶ V) :
    closedGradeObj i U ⟶ closedGradeObj i V :=
  CommRingCat.ofHom
    (Ideal.AssociatedGraded.map (((commRingStructureSheaf X).obj.map h).hom)
      (closedKernel_sectionIdeal_le_comap i h))

/-- The closed-immersion associated graded as a presheaf of commutative rings. -/
noncomputable def closedGradePresheaf {Z X : AlgebraicSpace S}
    (i : Z ⟶ X) [IsClosedImmersion i] :
    (smallEtaleSite X)ᵒᵖ ⥤ CommRingCat.{u} where
  obj := closedGradeObj i
  map := closedGradeMap i
  map_id := sorry
  map_comp := sorry

/-- The closed-immersion associated graded, as the sheafification of the sectionwise
associated graded of the kernel ideal. -/
noncomputable def closedGradeSheaf {Z X : AlgebraicSpace S}
    (i : Z ⟶ X) [IsClosedImmersion i] :
    Sheaf (smallEtaleTopology X) CommRingCat.{u} :=
  (presheafToSheaf (smallEtaleTopology X) CommRingCat.{u}).obj (closedGradePresheaf i)

/-- `closedGradeSheaf i` is the sheafification of `closedGradePresheaf i`. -/
theorem closedGradeSheaf_eq {Z X : AlgebraicSpace S}
    (i : Z ⟶ X) [IsClosedImmersion i] :
    closedGradeSheaf i =
      (presheafToSheaf (smallEtaleTopology X) CommRingCat.{u}).obj
        (closedGradePresheaf i) :=
  rfl

/-- The component at `U` of the closed-immersion associated graded structure map. -/
noncomputable def closedGradeStructureMap_app {Z X : AlgebraicSpace S}
    (i : Z ⟶ X) [IsClosedImmersion i] (U : (smallEtaleSite X)ᵒᵖ) :
    (commRingStructureSheaf X).obj.obj U ⟶ closedGradeObj i U :=
  CommRingCat.ofHom
    (algebraMap ((commRingStructureSheaf X).obj.obj U)
      (Ideal.AssociatedGraded.ring (KernelIdeal.sectionIdeal (commRingStructureSheafMap i) U)))

/-- The structure map from `𝒪_X` to the closed-immersion associated graded, as a morphism
of presheaves. -/
noncomputable def closedGradeStructureMapPresheaf {Z X : AlgebraicSpace S}
    (i : Z ⟶ X) [IsClosedImmersion i] :
    (commRingStructureSheaf X).obj ⟶ closedGradePresheaf i where
  app U := closedGradeStructureMap_app i U
  naturality := fun _ _ _ ↦ sorry

/-- The structure map from `𝒪_X` to the sheafified closed-immersion associated graded. -/
noncomputable def closedGradeStructureMap {Z X : AlgebraicSpace S}
    (i : Z ⟶ X) [IsClosedImmersion i] :
    commRingStructureSheaf X ⟶ closedGradeSheaf i :=
  CategoryTheory.Sheaf.homEquiv.symm
    (closedGradeStructureMapPresheaf i ≫
      toSheafify (smallEtaleTopology X) (closedGradePresheaf i))

/-- The total conormal algebra sheaf of a closed immersion, as the pushout of
`i^{-1} 𝒪_X ⟶ 𝒪_Z` against the inverse image of the associated graded. -/
noncomputable def closedTotalSheaf {Z X : AlgebraicSpace S}
    (i : Z ⟶ X) [IsClosedImmersion i] :
    Sheaf (smallEtaleTopology Z) CommRingCat.{u} :=
  pushout (inverseImageStructureSheafHom i)
    ((commRingInverseImage i).map (closedGradeStructureMap i))

/-- The structure map making the closed-immersion total conormal algebra an `𝒪_Z`-algebra. -/
noncomputable def closedStructureMap {Z X : AlgebraicSpace S}
    (i : Z ⟶ X) [IsClosedImmersion i] :
    commRingStructureSheaf Z ⟶ closedTotalSheaf i :=
  pushout.inl (inverseImageStructureSheafHom i)
    ((commRingInverseImage i).map (closedGradeStructureMap i))

/-- The total conormal algebra of a closed immersion, as a quasi-coherent `𝒪_Z`-algebra. -/
noncomputable def closedTotal {Z X : AlgebraicSpace S}
    (i : Z ⟶ X) [IsClosedImmersion i] : Z.QcAlgebraUnder where
  obj := Under.mk (closedStructureMap i)
  property := sorry

/-- The inverse image `f^*` of a closed-immersion total conormal algebra, as a sheaf. -/
noncomputable def closedPullbackSheaf {Z Z' X' : AlgebraicSpace S}
    (f : Z ⟶ Z') (i' : Z' ⟶ X') [IsClosedImmersion i'] :
    Sheaf (smallEtaleTopology Z) CommRingCat.{u} :=
  pushout (inverseImageStructureSheafHom f)
    ((commRingInverseImage f).map (closedStructureMap i'))

/-- The structure map of the pulled-back closed-immersion total conormal algebra. -/
noncomputable def closedPullbackStructureMap {Z Z' X' : AlgebraicSpace S}
    (f : Z ⟶ Z') (i' : Z' ⟶ X') [IsClosedImmersion i'] :
    commRingStructureSheaf Z ⟶ closedPullbackSheaf f i' :=
  pushout.inl (inverseImageStructureSheafHom f)
    ((commRingInverseImage f).map (closedStructureMap i'))

/-- The inverse image `f^*` of a closed-immersion total conormal algebra, as a
quasi-coherent `𝒪_Z`-algebra. -/
noncomputable def closedPullback {Z Z' X' : AlgebraicSpace S}
    (f : Z ⟶ Z') (i' : Z' ⟶ X') [IsClosedImmersion i'] : Z.QcAlgebraUnder where
  obj := Under.mk (closedPullbackStructureMap f i')
  property := sorry

/-- The `g^♯` component of an étale square carries closed-immersion kernel ideals into
kernel ideals. -/
theorem closedKernel_le_comap_square {Z X Z' X' : AlgebraicSpace S}
    {f : Z ⟶ Z'} {i : Z ⟶ X} {i' : Z' ⟶ X'} {g : X ⟶ X'}
    [IsClosedImmersion i] [IsClosedImmersion i'] (sq : CommSq f i i' g)
    {V : smallEtaleSite X'}
    (a : StructuredArrow (op ((etaleBaseChange g).obj V)) (smallEtaleInclusion X).op) :
    KernelIdeal.sectionIdeal (commRingStructureSheafMap i') (op V) ≤
      Ideal.comap (etaleSquareOfArrow g V a).map.left.appTop.hom
        (KernelIdeal.sectionIdeal (commRingStructureSheafMap i)
          (op (etaleSquareOfArrow g V a).left)) :=
  sorry

/-- The associated-graded component of an étale square, before sheafification on `X`. -/
noncomputable def mapClosedGradeToObj {Z X Z' X' : AlgebraicSpace S}
    {f : Z ⟶ Z'} {i : Z ⟶ X} {i' : Z' ⟶ X'} {g : X ⟶ X'}
    [IsClosedImmersion i] [IsClosedImmersion i'] (sq : CommSq f i i' g)
    {V : smallEtaleSite X'}
    (a : StructuredArrow (op ((etaleBaseChange g).obj V)) (smallEtaleInclusion X).op) :
    closedGradeObj i' (op V) ⟶ closedGradeObj i (op (etaleSquareOfArrow g V a).left) :=
  CommRingCat.ofHom
    (Ideal.AssociatedGraded.map (etaleSquareOfArrow g V a).map.left.appTop.hom
      (closedKernel_le_comap_square sq a))

/-- The cone of associated-graded maps presenting `gr(I')(V) ⟶ (g_* gr(I))(V)`. -/
noncomputable def mapClosedGradeCone {Z X Z' X' : AlgebraicSpace S}
    {f : Z ⟶ Z'} {i : Z ⟶ X} {i' : Z' ⟶ X'} {g : X ⟶ X'}
    [IsClosedImmersion i] [IsClosedImmersion i'] (sq : CommSq f i i' g)
    (V : smallEtaleSite X') :
    Cone
      (StructuredArrow.proj (op ((etaleBaseChange g).obj V)) (smallEtaleInclusion X).op ⋙
        (closedGradeSheaf i).obj) where
  pt := closedGradeObj i' (op V)
  π :=
    { app := fun a ↦
        mapClosedGradeToObj sq a ≫
          (toSheafify (smallEtaleTopology X) (closedGradePresheaf i)).app
            (op (etaleSquareOfArrow g V a).left)
      naturality := fun _ _ _ ↦ sorry }

/-- The component at `V` of the pushforward-side associated-graded comparison. -/
noncomputable def mapClosedGradeApp {Z X Z' X' : AlgebraicSpace S}
    {f : Z ⟶ Z'} {i : Z ⟶ X} {i' : Z' ⟶ X'} {g : X ⟶ X'}
    [IsClosedImmersion i] [IsClosedImmersion i'] (sq : CommSq f i i' g)
    (V : (smallEtaleSite X')ᵒᵖ) :
    closedGradeObj i' V ⟶
      ((commRingPushforward g).obj (closedGradeSheaf i)).obj.obj V :=
  @CommRingCat.ofHom (closedGradeObj i' V)
    (((commRingPushforward g).obj (closedGradeSheaf i)).obj.obj V)
    (inferInstanceAs (CommRing (closedGradeObj i' V)))
    (inferInstanceAs (CommRing (((commRingPushforward g).obj (closedGradeSheaf i)).obj.obj V)))
    { toFun := fun x ↦
        ((commRingPushforwardUnderlyingIso g).inv.app (closedGradeSheaf i)).hom.app V
          (EtaleTopos.allChartLift X ((commRingUnderlying X).obj (closedGradeSheaf i))
            ((etaleBaseChange g).obj V.unop)
            ((forget CommRingCat.{u}).mapCone (mapClosedGradeCone sq V.unop)) x)
      map_zero' := sorry
      map_one' := sorry
      map_add' := sorry
      map_mul' := sorry }


/-- The presheaf morphism whose sheafification is the pushforward-side associated-graded
comparison. -/
noncomputable def mapClosedGradePresheaf {Z X Z' X' : AlgebraicSpace S}
    {f : Z ⟶ Z'} {i : Z ⟶ X} {i' : Z' ⟶ X'} {g : X ⟶ X'}
    [IsClosedImmersion i] [IsClosedImmersion i'] (sq : CommSq f i i' g) :
    closedGradePresheaf i' ⟶ ((commRingPushforward g).obj (closedGradeSheaf i)).obj where
  app := mapClosedGradeApp sq
  naturality := fun _ _ _ ↦ sorry

/-- The pushforward-side associated-graded comparison, as a morphism of sheaves on `X'`. -/
noncomputable def mapClosedGradeSheaf {Z X Z' X' : AlgebraicSpace S}
    {f : Z ⟶ Z'} {i : Z ⟶ X} {i' : Z' ⟶ X'} {g : X ⟶ X'}
    [IsClosedImmersion i] [IsClosedImmersion i'] (sq : CommSq f i i' g) :
    closedGradeSheaf i' ⟶ (commRingPushforward g).obj (closedGradeSheaf i) :=
  ⟨sheafifyLift (smallEtaleTopology X') (mapClosedGradePresheaf sq)
    ((commRingPushforward g).obj (closedGradeSheaf i)).property⟩

/-- Inverse image of the closed-immersion associated graded along `g`, compared with the
associated graded of `i`. -/
noncomputable def mapClosedGradeInverseImage {Z X Z' X' : AlgebraicSpace S}
    {f : Z ⟶ Z'} {i : Z ⟶ X} {i' : Z' ⟶ X'} {g : X ⟶ X'}
    [IsClosedImmersion i] [IsClosedImmersion i'] (sq : CommSq f i i' g) :
    (commRingInverseImage g).obj (closedGradeSheaf i') ⟶ closedGradeSheaf i :=
  ((commRingInverseImageAdjunction g).homEquiv _ _).symm (mapClosedGradeSheaf sq)

/-- The right-hand pushout inclusion of the closed-immersion associated graded into the
closed total conormal algebra sheaf. -/
noncomputable def closedTotalInr {Z X : AlgebraicSpace S}
    (i : Z ⟶ X) [IsClosedImmersion i] :
    (commRingInverseImage i).obj (closedGradeSheaf i) ⟶ closedTotalSheaf i :=
  pushout.inr (inverseImageStructureSheafHom i)
    ((commRingInverseImage i).map (closedGradeStructureMap i))

/-- The generic big-site direct image of commutative-ring sheaves, rewritten through
spaces-étale pullback. The small-chart direct image uses `commRingPushforwardComp`. -/
noncomputable def commRingPushforwardFactor {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    sheafPushforward CommRingCat.{u} f ≅
      (smallEtaleInclusion X).sheafPushforwardCocontinuous CommRingCat.{u}
          (smallEtaleTopology X) (spacesEtaleTopology X) ⋙
        (spacesEtalePullback f).sheafPushforwardContinuous CommRingCat.{u}
          (spacesEtaleTopology Y) (spacesEtaleTopology X) ⋙
        (smallEtaleInclusion Y).sheafPushforwardContinuous CommRingCat.{u}
          (smallEtaleTopology Y) (spacesEtaleTopology Y) :=
  isoWhiskerLeft
    ((smallEtaleInclusion X).sheafPushforwardCocontinuous CommRingCat.{u}
      (smallEtaleTopology X) (spacesEtaleTopology X))
    ((Functor.sheafPushforwardContinuousIso
        (smallEtaleInclusion_comp_spacesEtalePullback f)
        CommRingCat.{u} (smallEtaleTopology Y) (spacesEtaleTopology X)).symm ≪≫
      Functor.sheafPushforwardContinuousComp (smallEtaleInclusion Y) (spacesEtalePullback f)
        CommRingCat.{u} (smallEtaleTopology Y) (spacesEtaleTopology Y)
        (spacesEtaleTopology X))

/-- Restricting a spaces étale commutative-ring sheaf to the small étale site and extending
it back is isomorphic to the identity. -/
noncomputable def smallEtaleInclusionContinuousCocontinuousIso_commRing
    (Y : AlgebraicSpace S) :
    (smallEtaleInclusion Y).sheafPushforwardContinuous CommRingCat.{u}
        (smallEtaleTopology Y) (spacesEtaleTopology Y) ⋙
      (smallEtaleInclusion Y).sheafPushforwardCocontinuous CommRingCat.{u}
        (smallEtaleTopology Y) (spacesEtaleTopology Y) ≅
    𝟭 (Sheaf (spacesEtaleTopology Y) CommRingCat.{u}) :=
  let restrict :=
    (smallEtaleInclusion Y).sheafPushforwardContinuous CommRingCat.{u}
      (smallEtaleTopology Y) (spacesEtaleTopology Y)
  let extend :=
    (smallEtaleInclusion Y).sheafPushforwardCocontinuous CommRingCat.{u}
      (smallEtaleTopology Y) (spacesEtaleTopology Y)
  let adj :=
    (smallEtaleInclusion Y).sheafAdjunctionCocontinuous CommRingCat.{u}
      (smallEtaleTopology Y) (spacesEtaleTopology Y)
  NatIso.ofComponents
    (fun F ↦
      let eSmall : restrict.obj ((restrict ⋙ extend).obj F) ≅ restrict.obj F :=
        { hom := adj.counit.app (restrict.obj F)
          inv := restrict.map (adj.unit.app F)
          hom_inv_id := sorry
          inv_hom_id := sorry }
      let i :
          (smallEtaleInclusion Y).op ⋙ ((restrict ⋙ extend).obj F).obj ≅
            (smallEtaleInclusion Y).op ⋙ F.obj :=
        { hom := eSmall.hom.hom
          inv := eSmall.inv.hom
          hom_inv_id := sorry
          inv_hom_id := sorry }
      Functor.IsCoverDense.sheafIso i)
    sorry

/-- Continuous pushforward of commutative-ring sheaves along spaces-étale pullback respects
composition. -/
noncomputable def spacesEtaleCommRingPushforwardComp {X Y Z : AlgebraicSpace S}
    (f : X ⟶ Y) (g : Y ⟶ Z) :
    (spacesEtalePullback f).sheafPushforwardContinuous CommRingCat.{u}
        (spacesEtaleTopology Y) (spacesEtaleTopology X) ⋙
      (spacesEtalePullback g).sheafPushforwardContinuous CommRingCat.{u}
        (spacesEtaleTopology Z) (spacesEtaleTopology Y) ≅
      (spacesEtalePullback (f ≫ g)).sheafPushforwardContinuous CommRingCat.{u}
        (spacesEtaleTopology Z) (spacesEtaleTopology X) :=
  (spacesEtalePullback g).sheafPushforwardContinuousComp (spacesEtalePullback f)
      CommRingCat.{u} (spacesEtaleTopology Z) (spacesEtaleTopology Y)
      (spacesEtaleTopology X) ≪≫
    Functor.sheafPushforwardContinuousIso (spacesEtalePullbackComp f g).symm
      CommRingCat.{u} (spacesEtaleTopology Z) (spacesEtaleTopology X)

/-- Direct image of commutative-ring sheaves along a composite is the composite of the
direct images. -/
noncomputable def commRingPushforwardCompIso {X Y Z : AlgebraicSpace S}
    (f : X ⟶ Y) (g : Y ⟶ Z) :
    commRingPushforward f ⋙ commRingPushforward g ≅ commRingPushforward (f ≫ g) :=
  commRingPushforwardComp f g

/-- The component of `commRingPushforwardCompIso` at a sheaf is the indicated 1-cell of
the composite of direct images. -/
theorem commRingPushforwardCompIso_hom_app {X Y Z : AlgebraicSpace S}
    (f : X ⟶ Y) (g : Y ⟶ Z)
    (F : Sheaf (smallEtaleTopology X) CommRingCat.{u}) :
    (commRingPushforwardCompIso f g).hom.app F =
      (commRingPushforwardCompIso f g).hom.app F :=
  rfl

/-- Inverse image of commutative-ring sheaves along a composite is the composite of the
inverse images. -/
noncomputable def commRingInverseImageCompIso {X Y Z : AlgebraicSpace S}
    (f : X ⟶ Y) (g : Y ⟶ Z) :
    commRingInverseImage g ⋙ commRingInverseImage f ≅ commRingInverseImage (f ≫ g) :=
  Adjunction.leftAdjointCompIso
    (commRingInverseImageAdjunction g) (commRingInverseImageAdjunction f)
    (commRingInverseImageAdjunction (f ≫ g)) (commRingPushforwardCompIso f g)

/-- The closed-immersion associated graded of `i` maps to the pushforward of the closed
total algebra along `i`. -/
noncomputable def closedGradeToPushforwardTotal {Z X : AlgebraicSpace S}
    (i : Z ⟶ X) [IsClosedImmersion i] :
    closedGradeSheaf i ⟶ (commRingPushforward i).obj (closedTotalSheaf i) :=
  (commRingInverseImageAdjunction i).homEquiv _ _ (closedTotalInr i)

/-- The associated-graded sheaf of `i'` maps to the iterated pushforward of the closed
total algebra of `i` along `f` then `i'`. -/
noncomputable def mapClosedGradeToPushforwardTotal {Z X Z' X' : AlgebraicSpace S}
    {f : Z ⟶ Z'} {i : Z ⟶ X} {i' : Z' ⟶ X'} {g : X ⟶ X'}
    [IsClosedImmersion i] [IsClosedImmersion i'] (sq : CommSq f i i' g) :
    closedGradeSheaf i' ⟶
      (commRingPushforward i').obj ((commRingPushforward f).obj (closedTotalSheaf i)) :=
  mapClosedGradeSheaf sq ≫
    (commRingPushforward g).map (closedGradeToPushforwardTotal i) ≫
    (commRingPushforwardCompIso i g).hom.app (closedTotalSheaf i) ≫
    (eqToIso (congrArg (fun h ↦ (commRingPushforward h).obj (closedTotalSheaf i))
        sq.w.symm)).hom ≫
    (commRingPushforwardCompIso f i').inv.app (closedTotalSheaf i)

/-- The inverse image of the associated graded of `i'` maps to the pushforward of the
closed total algebra of `i` along `f`. -/
noncomputable def mapClosedPushforwardGrade {Z X Z' X' : AlgebraicSpace S}
    {f : Z ⟶ Z'} {i : Z ⟶ X} {i' : Z' ⟶ X'} {g : X ⟶ X'}
    [IsClosedImmersion i] [IsClosedImmersion i'] (sq : CommSq f i i' g) :
    (commRingInverseImage i').obj (closedGradeSheaf i') ⟶
      (commRingPushforward f).obj (closedTotalSheaf i) :=
  ((commRingInverseImageAdjunction i').homEquiv _ _).symm (mapClosedGradeToPushforwardTotal sq)

/-- The two legs of the closed total pushout agree after mapping to the pushforward of
the closed total algebra of `i`. -/
theorem mapClosedPushforward_w {Z X Z' X' : AlgebraicSpace S}
    {f : Z ⟶ Z'} {i : Z ⟶ X} {i' : Z' ⟶ X'} {g : X ⟶ X'}
    [IsClosedImmersion i] [IsClosedImmersion i'] (sq : CommSq f i i' g) :
    inverseImageStructureSheafHom i' ≫
        commRingStructureSheafMap f ≫ (commRingPushforward f).map (closedStructureMap i) =
      (commRingInverseImage i').map (closedGradeStructureMap i') ≫
        mapClosedPushforwardGrade sq :=
  sorry

/-- The closed total algebra of `i'` maps to the pushforward along `f` of the closed total
algebra of `i`. -/
noncomputable def mapClosedPushforward {Z X Z' X' : AlgebraicSpace S}
    {f : Z ⟶ Z'} {i : Z ⟶ X} {i' : Z' ⟶ X'} {g : X ⟶ X'}
    [IsClosedImmersion i] [IsClosedImmersion i'] (sq : CommSq f i i' g) :
    closedTotalSheaf i' ⟶ (commRingPushforward f).obj (closedTotalSheaf i) :=
  pushout.desc
    (commRingStructureSheafMap f ≫ (commRingPushforward f).map (closedStructureMap i))
    (mapClosedPushforwardGrade sq) (mapClosedPushforward_w sq)

/-- Inverse image of the closed total algebra of `i'` along `f`, compared with the closed
total algebra of `i`. -/
noncomputable def mapClosedInverseImage {Z X Z' X' : AlgebraicSpace S}
    {f : Z ⟶ Z'} {i : Z ⟶ X} {i' : Z' ⟶ X'} {g : X ⟶ X'}
    [IsClosedImmersion i] [IsClosedImmersion i'] (sq : CommSq f i i' g) :
    (commRingInverseImage f).obj (closedTotalSheaf i') ⟶ closedTotalSheaf i :=
  ((commRingInverseImageAdjunction f).homEquiv _ _).symm (mapClosedPushforward sq)

/-- The two legs of the closed pullback pushout agree after mapping to the closed total
algebra of `i`. -/
theorem mapClosedSheaf_w {Z X Z' X' : AlgebraicSpace S}
    {f : Z ⟶ Z'} {i : Z ⟶ X} {i' : Z' ⟶ X'} {g : X ⟶ X'}
    [IsClosedImmersion i] [IsClosedImmersion i'] (sq : CommSq f i i' g) :
    inverseImageStructureSheafHom f ≫ closedStructureMap i =
      (commRingInverseImage f).map (closedStructureMap i') ≫ mapClosedInverseImage sq :=
  sorry

/-- The closed-immersion comparison as a morphism of commutative-ring sheaves on `Z`. -/
noncomputable def mapClosedSheaf {Z X Z' X' : AlgebraicSpace S}
    {f : Z ⟶ Z'} {i : Z ⟶ X} {i' : Z' ⟶ X'} {g : X ⟶ X'}
    [IsClosedImmersion i] [IsClosedImmersion i'] (sq : CommSq f i i' g) :
    closedPullbackSheaf f i' ⟶ closedTotalSheaf i :=
  pushout.desc (closedStructureMap i) (mapClosedInverseImage sq) (mapClosedSheaf_w sq)

/-- The closed-immersion comparison commutes with structure maps from `𝒪_Z`. -/
theorem mapClosed_comp {Z X Z' X' : AlgebraicSpace S}
    {f : Z ⟶ Z'} {i : Z ⟶ X} {i' : Z' ⟶ X'} {g : X ⟶ X'}
    [IsClosedImmersion i] [IsClosedImmersion i'] (sq : CommSq f i i' g) :
    closedPullbackStructureMap f i' ≫ mapClosedSheaf sq = closedStructureMap i :=
  sorry

/-- The canonical comparison of total conormal algebras for a commutative square of closed
immersions, assembled from `Ideal.AssociatedGraded.map` of `g^♯`. -/
noncomputable def mapClosed {Z X Z' X' : AlgebraicSpace S}
    {f : Z ⟶ Z'} {i : Z ⟶ X} {i' : Z' ⟶ X'} {g : X ⟶ X'}
    [IsClosedImmersion i] [IsClosedImmersion i'] (sq : CommSq f i i' g) :
    closedPullback f i' ⟶ closedTotal i :=
  ⟨Under.homMk (mapClosedSheaf sq) (mapClosed_comp sq)⟩

/-- The coborder associated graded presheaf of an immersion is isomorphic to the
closed-immersion associated graded of its coborder lift, by the identity on
sectionwise associated graded rings. -/
noncomputable def coborderGradePresheafIsoClosed {Z X : AlgebraicSpace S}
    (i : Z ⟶ X) [IsImmersion i] :
    coborderGradePresheaf i ≅ closedGradePresheaf (IsImmersion.liftCoborder i) :=
  NatIso.ofComponents (fun _ ↦ Iso.refl _) sorry

/-- On sections, `coborderGradePresheafIsoClosed` is the identity of the associated graded
ring. -/
theorem coborderGradePresheafIsoClosed_hom_app {Z X : AlgebraicSpace S}
    (i : Z ⟶ X) [IsImmersion i] (U : (smallEtaleSite (Hom.coborder i))ᵒᵖ) :
    (coborderGradePresheafIsoClosed i).hom.app U = 𝟙 (coborderGradeObj i U) :=
  sorry

/-- The coborder associated graded of an immersion is isomorphic to the closed-immersion
associated graded of its coborder lift, by sheafifying `coborderGradePresheafIsoClosed`. -/
noncomputable def coborderGradeIsoClosed {Z X : AlgebraicSpace S}
    (i : Z ⟶ X) [IsImmersion i] :
    coborderGradeSheaf i ≅ closedGradeSheaf (IsImmersion.liftCoborder i) :=
  (presheafToSheaf (smallEtaleTopology (Hom.coborder i)) CommRingCat.{u}).mapIso
    (coborderGradePresheafIsoClosed i)

/-- `coborderGradeIsoClosed` is the sheafification of `coborderGradePresheafIsoClosed`. -/
theorem coborderGradeIsoClosed_hom_app {Z X : AlgebraicSpace S}
    (i : Z ⟶ X) [IsImmersion i] :
    (coborderGradeIsoClosed i).hom =
      (presheafToSheaf (smallEtaleTopology (Hom.coborder i)) CommRingCat.{u}).map
        (coborderGradePresheafIsoClosed i).hom :=
  sorry

/-- The total conormal algebra sheaf of an immersion is isomorphic to the closed-immersion
total algebra sheaf of its coborder lift. -/
noncomputable def totalSheafIsoClosed {Z X : AlgebraicSpace S}
    (i : Z ⟶ X) [IsImmersion i] :
    totalSheaf i ≅ closedTotalSheaf (IsImmersion.liftCoborder i) where
  hom :=
    pushout.desc (closedStructureMap (IsImmersion.liftCoborder i))
      ((commRingInverseImage (IsImmersion.liftCoborder i)).map
          (coborderGradeIsoClosed i).hom ≫
        closedTotalInr (IsImmersion.liftCoborder i)) sorry
  inv :=
    pushout.desc (structureMap i)
      ((commRingInverseImage (IsImmersion.liftCoborder i)).map
          (coborderGradeIsoClosed i).inv ≫
        totalInr i) sorry
  hom_inv_id := sorry
  inv_hom_id := sorry

/-- The inverse image of `total i'` along `f` is isomorphic to the closed-immersion pullback
of the coborder lift of `i'`. -/
noncomputable def pullbackSheafIsoClosed {Z Z' X' : AlgebraicSpace S}
    (f : Z ⟶ Z') (i' : Z' ⟶ X') [IsImmersion i'] :
    pullbackSheaf f i' ≅ closedPullbackSheaf f (IsImmersion.liftCoborder i') where
  hom :=
    pushout.desc (closedPullbackStructureMap f (IsImmersion.liftCoborder i'))
      ((commRingInverseImage f).map (totalSheafIsoClosed i').hom ≫
        pushout.inr (inverseImageStructureSheafHom f)
          ((commRingInverseImage f).map
            (closedStructureMap (IsImmersion.liftCoborder i')))) sorry
  inv :=
    pushout.desc (pullbackStructureMap f i')
      ((commRingInverseImage f).map (totalSheafIsoClosed i').inv ≫
        pushout.inr (inverseImageStructureSheafHom f)
          ((commRingInverseImage f).map (structureMap i'))) sorry
  hom_inv_id := sorry
  inv_hom_id := sorry

/-- Restriction of the coborder associated graded of `i` along the compatible open. -/
noncomputable def compatibleOpenGradeMap {Z X Z' X' : AlgebraicSpace S}
    {f : Z ⟶ Z'} {i : Z ⟶ X} {i' : Z' ⟶ X'} {g : X ⟶ X'}
    [IsImmersion i] [IsImmersion i'] (sq : CommSq f i i' g) :
    (commRingInverseImage (Hom.Conormal.compatibleOpenToCoborder i i' g)).obj
        (closedGradeSheaf (IsImmersion.liftCoborder i)) ⟶
      closedGradeSheaf (Hom.Conormal.liftToCompatibleOpen sq) :=
  mapClosedGradeInverseImage (Hom.Conormal.coborderSq sq)

/-- Restriction of the coborder associated graded along the compatible open is an
isomorphism. -/
instance instIsIso_compatibleOpenGradeMap {Z X Z' X' : AlgebraicSpace S}
    {f : Z ⟶ Z'} {i : Z ⟶ X} {i' : Z' ⟶ X'} {g : X ⟶ X'}
    [IsImmersion i] [IsImmersion i'] (sq : CommSq f i i' g) :
    IsIso (compatibleOpenGradeMap sq) :=
  sorry

/-- Inverse image along the coborder lift identifies with inverse image along the compatible
open followed by inverse image along the comparison to the coborder. -/
noncomputable def inverseImageLiftIso {Z X Z' X' : AlgebraicSpace S}
    {f : Z ⟶ Z'} {i : Z ⟶ X} {i' : Z' ⟶ X'} {g : X ⟶ X'}
    [IsImmersion i] [IsImmersion i'] (sq : CommSq f i i' g) :
    commRingInverseImage (IsImmersion.liftCoborder i) ≅
      commRingInverseImage (Hom.Conormal.compatibleOpenToCoborder i i' g) ⋙
        commRingInverseImage (Hom.Conormal.liftToCompatibleOpen sq) :=
  (eqToIso (congrArg commRingInverseImage
      (Hom.Conormal.liftToCompatibleOpen_comp_toCoborder sq))).symm ≪≫
    (commRingInverseImageCompIso (Hom.Conormal.liftToCompatibleOpen sq)
        (Hom.Conormal.compatibleOpenToCoborder i i' g)).symm

/-- The closed total algebra sheaf of the coborder lift is isomorphic to that of the
compatible-open lift. -/
noncomputable def compatibleOpenTotalIso {Z X Z' X' : AlgebraicSpace S}
    {f : Z ⟶ Z'} {i : Z ⟶ X} {i' : Z' ⟶ X'} {g : X ⟶ X'}
    [IsImmersion i] [IsImmersion i'] (sq : CommSq f i i' g) :
    closedTotalSheaf (IsImmersion.liftCoborder i) ≅
      closedTotalSheaf (Hom.Conormal.liftToCompatibleOpen sq) where
  hom :=
    pushout.desc (closedStructureMap (Hom.Conormal.liftToCompatibleOpen sq))
      ((inverseImageLiftIso sq).hom.app
          (closedGradeSheaf (IsImmersion.liftCoborder i)) ≫
        (commRingInverseImage (Hom.Conormal.liftToCompatibleOpen sq)).map
          (compatibleOpenGradeMap sq) ≫
        closedTotalInr (Hom.Conormal.liftToCompatibleOpen sq)) sorry
  inv :=
    pushout.desc (closedStructureMap (IsImmersion.liftCoborder i))
      ((commRingInverseImage (Hom.Conormal.liftToCompatibleOpen sq)).map
          (inv (compatibleOpenGradeMap sq)) ≫
        (inverseImageLiftIso sq).inv.app
          (closedGradeSheaf (IsImmersion.liftCoborder i)) ≫
        closedTotalInr (IsImmersion.liftCoborder i)) sorry
  hom_inv_id := sorry
  inv_hom_id := sorry

/-- The canonical comparison as a morphism of commutative-ring sheaves
`f^* C_{Z'/X',*} ⟶ C_{Z/X,*}` on `Z`. -/
noncomputable def mapSheaf {Z X Z' X' : AlgebraicSpace S}
    {f : Z ⟶ Z'} {i : Z ⟶ X} {i' : Z' ⟶ X'} {g : X ⟶ X'}
    [IsImmersion i] [IsImmersion i'] (sq : CommSq f i i' g) :
    pullbackSheaf f i' ⟶ totalSheaf i :=
  (pullbackSheafIsoClosed f i').hom ≫
    mapClosedSheaf (Hom.Conormal.restrictedSq sq) ≫
      (compatibleOpenTotalIso sq).inv ≫ (totalSheafIsoClosed i).inv

/-- The comparison `mapSheaf` commutes with structure maps from `𝒪_Z`. -/
theorem mapSheaf_comp {Z X Z' X' : AlgebraicSpace S}
    {f : Z ⟶ Z'} {i : Z ⟶ X} {i' : Z' ⟶ X'} {g : X ⟶ X'}
    [IsImmersion i] [IsImmersion i'] (sq : CommSq f i i' g) :
    pullbackStructureMap f i' ≫ mapSheaf sq = structureMap i :=
  sorry

/-- The canonical map of graded `𝒪_Z`-algebras `f^* C_{Z'/X',*} ⟶ C_{Z/X,*}` induced by a
commutative square of immersions of algebraic spaces over `S`. -/
noncomputable def map {Z X Z' X' : AlgebraicSpace S}
    {f : Z ⟶ Z'} {i : Z ⟶ X} {i' : Z' ⟶ X'} {g : X ⟶ X'}
    [IsImmersion i] [IsImmersion i'] (sq : CommSq f i i' g) :
    pullback f i' ⟶ total i :=
  ⟨Under.homMk (mapSheaf sq) (mapSheaf_comp sq)⟩

/-- A morphism of total conormal algebras is the canonical comparison of a commutative
square of immersions when it equals `map sq`. -/
def IsMap {Z X Z' X' : AlgebraicSpace S}
    {f : Z ⟶ Z'} {i : Z ⟶ X} {i' : Z' ⟶ X'} {g : X ⟶ X'}
    [IsImmersion i] [IsImmersion i'] (sq : CommSq f i i' g)
    (tau : pullback f i' ⟶ total i) : Prop :=
  tau = map sq

/-- The constructed comparison satisfies `IsMap`. -/
theorem map_spec {Z X Z' X' : AlgebraicSpace S}
    {f : Z ⟶ Z'} {i : Z ⟶ X} {i' : Z' ⟶ X'} {g : X ⟶ X'}
    [IsImmersion i] [IsImmersion i'] (sq : CommSq f i i' g) :
    IsMap sq (map sq) :=
  sorry

/-- In degree one, `mapPiece` recovers the conormal-sheaf comparison of Lemma 76.5.3. -/
theorem mapPiece_one {Z X Z' X' : AlgebraicSpace S}
    {f : Z ⟶ Z'} {i : Z ⟶ X} {i' : Z' ⟶ X'} {g : X ⟶ X'}
    [IsImmersion i] [IsImmersion i'] (sq : CommSq f i i' g) :
    mapPiece sq 1 =
      eqToHom (congrArg (Modules.pullback f).obj (piece_one i')) ≫
        Hom.Conormal.map sq ≫ eqToHom (piece_one i).symm :=
  sorry


end AlgebraicGeometry.AlgebraicSpace.ConormalAlgebra
