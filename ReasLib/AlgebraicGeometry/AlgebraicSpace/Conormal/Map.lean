module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Conormal.CommRingAdjunction

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Conormal.Algebra
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Conormal.Piece
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Conormal.Functorial
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Algebra.Underlying
public import ReasLib.RingTheory.Ideal.AssociatedGraded.StageClass

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
    commStructureSheaf Z ⟶ pullbackSheaf f i' :=
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

/-- The section image of the new ideal power lies in the old one on the same chart. -/
theorem compatiblePowerSection_mem {Z X Z' X' : AlgebraicSpace S}
    {f : Z ⟶ Z'} {i : Z ⟶ X} {i' : Z' ⟶ X'} {g : X ⟶ X'}
    [IsImmersion i] [IsImmersion i'] (sq : CommSq f i i' g) (n : ℕ)
    (U : smallEtaleSite (Hom.Conormal.compatibleOpen i i' g).X)
    (s : (closedIdealPower (Hom.Conormal.liftToCompatibleOpen sq) n).toModule.val.obj (op U)) :
    ((Hom.Conormal.subobjectSectionsIso
        (closedIdealPower (Hom.Conormal.liftToCompatibleOpen sq) n) (op U)).hom s).val ∈
      LinearMap.range
        ((SheafOfModules.evaluation (structureSheaf (Hom.coborder i))
          (op ((etaleRestriction (Hom.Conormal.compatibleOpenToCoborder i i' g)).obj U))).map
          (coborderIdealPower i n).arrow).hom := sorry

/-- Retain the same scalar and its old ideal-power membership on the postcomposed chart. -/
def compatiblePowerSection {Z X Z' X' : AlgebraicSpace S}
    {f : Z ⟶ Z'} {i : Z ⟶ X} {i' : Z' ⟶ X'} {g : X ⟶ X'}
    [IsImmersion i] [IsImmersion i'] (sq : CommSq f i i' g) (n : ℕ)
    (U : smallEtaleSite (Hom.Conormal.compatibleOpen i i' g).X)
    (s : (closedIdealPower (Hom.Conormal.liftToCompatibleOpen sq) n).toModule.val.obj (op U)) :
    (coborderIdealPower i n).toModule.val.obj
      (op ((etaleRestriction (Hom.Conormal.compatibleOpenToCoborder i i' g)).obj U)) :=
  (Hom.Conormal.subobjectSectionsIso (coborderIdealPower i n)
      (op ((etaleRestriction (Hom.Conormal.compatibleOpenToCoborder i i' g)).obj U))).inv
    ⟨((Hom.Conormal.subobjectSectionsIso
        (closedIdealPower (Hom.Conormal.liftToCompatibleOpen sq) n) (op U)).hom s).val,
      compatiblePowerSection_mem sq n U s⟩

/-- The explicit map from a new ideal-power module to the geometric pullback of the old one. -/
def compatiblePowerToPullback {Z X Z' X' : AlgebraicSpace S}
    {f : Z ⟶ Z'} {i : Z ⟶ X} {i' : Z' ⟶ X'} {g : X ⟶ X'}
    [IsImmersion i] [IsImmersion i'] (sq : CommSq f i i' g) (n : ℕ) :
    (closedIdealPower (Hom.Conormal.liftToCompatibleOpen sq) n).toModule ⟶
      (Modules.pullback (Hom.Conormal.compatibleOpenToCoborder i i' g)).obj
        (coborderIdealPower i n).toModule where
  val :=
    { app := fun U ↦ ModuleCat.ofHom
        { toFun := fun s ↦ Hom.Conormal.pullbackSection
            (Hom.Conormal.compatibleOpenToCoborder i i' g) (coborderIdealPower i n).toModule
            U.unop (compatiblePowerSection sq n U.unop s)
          map_add' := sorry
          map_smul' := sorry }
      naturality := sorry }

/-- The new power module maps into the pulled old successive quotient. -/
def compatibleQuotientPowerMap {Z X Z' X' : AlgebraicSpace S}
    {f : Z ⟶ Z'} {i : Z ⟶ X} {i' : Z' ⟶ X'} {g : X ⟶ X'}
    [IsImmersion i] [IsImmersion i'] (sq : CommSq f i i' g) (n : ℕ) :
    (closedIdealPower (Hom.Conormal.liftToCompatibleOpen sq) n).toModule ⟶
      (Modules.pullback (Hom.Conormal.compatibleOpenToCoborder i i' g)).obj
        (coborderQuotient i n) :=
  compatiblePowerToPullback sq n ≫
    (Modules.pullback (Hom.Conormal.compatibleOpenToCoborder i i' g)).map
      (Modules.quotientByIdeal.π (Hom.idealSheafSubobject (IsImmersion.liftCoborder i))
        (coborderIdealPower i n).toModule)

/-- The new ideal action is annihilated by the specified old quotient map. -/
theorem compatibleQuotientPowerMap_w {Z X Z' X' : AlgebraicSpace S}
    {f : Z ⟶ Z'} {i : Z ⟶ X} {i' : Z' ⟶ X'} {g : X ⟶ X'}
    [IsImmersion i] [IsImmersion i'] (sq : CommSq f i i' g) (n : ℕ) :
    Modules.idealAction (Hom.idealSheafSubobject (Hom.Conormal.liftToCompatibleOpen sq))
        (closedIdealPower (Hom.Conormal.liftToCompatibleOpen sq) n).toModule ≫
      compatibleQuotientPowerMap sq n = 0 := sorry

/-- The reverse quotient restriction map is actual cokernel descent. -/
def compatibleOpenQuotientMapInv {Z X Z' X' : AlgebraicSpace S}
    {f : Z ⟶ Z'} {i : Z ⟶ X} {i' : Z' ⟶ X'} {g : X ⟶ X'}
    [IsImmersion i] [IsImmersion i'] (sq : CommSq f i i' g) (n : ℕ) :
    closedQuotient (Hom.Conormal.liftToCompatibleOpen sq) n ⟶
      (Modules.pullback (Hom.Conormal.compatibleOpenToCoborder i i' g)).obj
        (coborderQuotient i n) :=
  cokernel.desc _ (compatibleQuotientPowerMap sq n) (compatibleQuotientPowerMap_w sq n)

/-- The quotient restriction comparison with both maps fixed. -/
def compatibleOpenQuotientIso {Z X Z' X' : AlgebraicSpace S}
    {f : Z ⟶ Z'} {i : Z ⟶ X} {i' : Z' ⟶ X'} {g : X ⟶ X'}
    [IsImmersion i] [IsImmersion i'] (sq : CommSq f i i' g) (n : ℕ) :
    (Modules.pullback (Hom.Conormal.compatibleOpenToCoborder i i' g)).obj
        (coborderQuotient i n) ≅ closedQuotient (Hom.Conormal.liftToCompatibleOpen sq) n where
  hom := compatibleOpenQuotientMap sq n
  inv := compatibleOpenQuotientMapInv sq n
  hom_inv_id := sorry
  inv_hom_id := sorry

/-- The specified quotient restriction map is an isomorphism. -/
instance instIsIso_compatibleOpenQuotientMap {Z X Z' X' : AlgebraicSpace S}
    {f : Z ⟶ Z'} {i : Z ⟶ X} {i' : Z' ⟶ X'} {g : X ⟶ X'}
    [IsImmersion i] [IsImmersion i'] (sq : CommSq f i i' g) (n : ℕ) :
    IsIso (compatibleOpenQuotientMap sq n) := (compatibleOpenQuotientIso sq n).isIso_hom

/-- The degree-`n` comparison `f^{-1} C_{Z'/X',n} ⟶ C_{Z/X,n}` induced by a commutative
square of immersions. -/
noncomputable def mapPiece {Z X Z' X' : AlgebraicSpace S}
    {f : Z ⟶ Z'} {i : Z ⟶ X} {i' : Z' ⟶ X'} {g : X ⟶ X'}
    [IsImmersion i] [IsImmersion i'] (sq : CommSq f i i' g) (n : ℕ) :
    (Modules.pullback f).obj (piece i' n) ⟶ piece i n :=
  (Modules.pullbackCompIso f (IsImmersion.liftCoborder i')).hom.app (coborderQuotient i' n) ≫
    (eqToIso (congrArg Modules.pullback (Hom.Conormal.restrictedSq sq).w)).hom.app
      (coborderQuotient i' n) ≫
    (Modules.pullbackCompIso (Hom.Conormal.liftToCompatibleOpen sq)
        (Hom.Conormal.restrictToCompatibleOpen i i' g)).inv.app
      (coborderQuotient i' n) ≫
    (Modules.pullback (Hom.Conormal.liftToCompatibleOpen sq)).map
      (closedQuotientMap (Hom.Conormal.restrictedSq sq) n) ≫
    (Modules.pullback (Hom.Conormal.liftToCompatibleOpen sq)).map
      (compatibleOpenQuotientMapInv sq n) ≫
    (Modules.pullbackCompIso (Hom.Conormal.liftToCompatibleOpen sq)
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
    KernelIdeal.sectionIdeal (commStructureSheafMap i) U ≤
      Ideal.comap (((commStructureSheaf X).obj.map h).hom)
        (KernelIdeal.sectionIdeal (commStructureSheafMap i) V) :=
  sorry

/-- The sectionwise associated graded ring of the kernel ideal of a closed immersion. -/
noncomputable def closedGradeObj {Z X : AlgebraicSpace S}
    (i : Z ⟶ X) [IsClosedImmersion i] (U : (smallEtaleSite X)ᵒᵖ) : CommRingCat.{u} :=
  CommRingCat.of
    (Ideal.AssociatedGraded.ring (KernelIdeal.sectionIdeal (commStructureSheafMap i) U))

/-- Restriction of the sectionwise closed-immersion associated graded rings. -/
noncomputable def closedGradeMap {Z X : AlgebraicSpace S}
    (i : Z ⟶ X) [IsClosedImmersion i] {U V : (smallEtaleSite X)ᵒᵖ} (h : U ⟶ V) :
    closedGradeObj i U ⟶ closedGradeObj i V :=
  CommRingCat.ofHom
    (Ideal.AssociatedGraded.map (((commStructureSheaf X).obj.map h).hom)
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
    (commStructureSheaf X).obj.obj U ⟶ closedGradeObj i U :=
  CommRingCat.ofHom
    (algebraMap ((commStructureSheaf X).obj.obj U)
      (Ideal.AssociatedGraded.ring (KernelIdeal.sectionIdeal (commStructureSheafMap i) U)))

/-- The structure map from `𝒪_X` to the closed-immersion associated graded, as a morphism
of presheaves. -/
noncomputable def closedGradeStructureMapPresheaf {Z X : AlgebraicSpace S}
    (i : Z ⟶ X) [IsClosedImmersion i] :
    (commStructureSheaf X).obj ⟶ closedGradePresheaf i where
  app U := closedGradeStructureMap_app i U
  naturality := fun _ _ _ ↦ sorry

/-- The structure map from `𝒪_X` to the sheafified closed-immersion associated graded. -/
noncomputable def closedGradeStructureMap {Z X : AlgebraicSpace S}
    (i : Z ⟶ X) [IsClosedImmersion i] :
    commStructureSheaf X ⟶ closedGradeSheaf i :=
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
    commStructureSheaf Z ⟶ closedTotalSheaf i :=
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
    commStructureSheaf Z ⟶ closedPullbackSheaf f i' :=
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
    (a : StructuredArrow (op ((etaleBaseChange g).obj V)) (smallEtaleToSpaces X).op) :
    KernelIdeal.sectionIdeal (commStructureSheafMap i') (op V) ≤
      Ideal.comap (etaleSquareOfArrow g V a).map.left.appTop.hom
        (KernelIdeal.sectionIdeal (commStructureSheafMap i)
          (op (etaleSquareOfArrow g V a).left)) :=
  sorry

/-- The associated-graded component of an étale square, before sheafification on `X`. -/
noncomputable def mapClosedGradeToObj {Z X Z' X' : AlgebraicSpace S}
    {f : Z ⟶ Z'} {i : Z ⟶ X} {i' : Z' ⟶ X'} {g : X ⟶ X'}
    [IsClosedImmersion i] [IsClosedImmersion i'] (sq : CommSq f i i' g)
    {V : smallEtaleSite X'}
    (a : StructuredArrow (op ((etaleBaseChange g).obj V)) (smallEtaleToSpaces X).op) :
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
      (StructuredArrow.proj (op ((etaleBaseChange g).obj V)) (smallEtaleToSpaces X).op ⋙
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
    (AlgebraicSpace.commRingPushforwardComp i g).hom.app (closedTotalSheaf i) ≫
    (eqToIso (congrArg (fun h ↦ (commRingPushforward h).obj (closedTotalSheaf i))
        sq.w.symm)).hom ≫
    (AlgebraicSpace.commRingPushforwardComp f i').inv.app (closedTotalSheaf i)

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
        commStructureSheafMap f ≫ (commRingPushforward f).map (closedStructureMap i) =
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
    (commStructureSheafMap f ≫ (commRingPushforward f).map (closedStructureMap i))
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

/-- On a compatible-open chart, the new kernel ideal is contained in the old one
in the same section ring. -/
theorem compatibleGradeKernel_le {Z X Z' X' : AlgebraicSpace S}
    {f : Z ⟶ Z'} {i : Z ⟶ X} {i' : Z' ⟶ X'} {g : X ⟶ X'}
    [IsImmersion i] [IsImmersion i'] (sq : CommSq f i i' g)
    (U : smallEtaleSite (Hom.Conormal.compatibleOpen i i' g).X) :
    KernelIdeal.sectionIdeal (commStructureSheafMap (Hom.Conormal.liftToCompatibleOpen sq))
        (op U) ≤
      Ideal.comap (RingHom.id ((commStructureSheaf (Hom.Conormal.compatibleOpen i i' g).X).obj.obj (op U)))
        (KernelIdeal.sectionIdeal (commStructureSheafMap (IsImmersion.liftCoborder i))
          (op ((etaleRestriction (Hom.Conormal.compatibleOpenToCoborder i i' g)).obj U))) := sorry

/-- A new associated-graded section maps to the old graded section by the identity
map on the common scheme's ring. -/
def compatibleGradeSection {Z X Z' X' : AlgebraicSpace S}
    {f : Z ⟶ Z'} {i : Z ⟶ X} {i' : Z' ⟶ X'} {g : X ⟶ X'}
    [IsImmersion i] [IsImmersion i'] (sq : CommSq f i i' g)
    (U : smallEtaleSite (Hom.Conormal.compatibleOpen i i' g).X) :
    closedGradeObj (Hom.Conormal.liftToCompatibleOpen sq) (op U) ⟶
      closedGradeObj (IsImmersion.liftCoborder i)
        (op ((etaleRestriction (Hom.Conormal.compatibleOpenToCoborder i i' g)).obj U)) :=
  CommRingCat.ofHom
    (Ideal.AssociatedGraded.map (RingHom.id _) (compatibleGradeKernel_le sq U))

/-- Include the literal old graded section in its sheaf, then generate its actual
inverse-image section by the commutative-ring adjunction unit and chart evaluation. -/
def compatibleGradeInverseApp {Z X Z' X' : AlgebraicSpace S}
    {f : Z ⟶ Z'} {i : Z ⟶ X} {i' : Z' ⟶ X'} {g : X ⟶ X'}
    [IsImmersion i] [IsImmersion i'] (sq : CommSq f i i' g)
    (U : smallEtaleSite (Hom.Conormal.compatibleOpen i i' g).X) :
    closedGradeObj (Hom.Conormal.liftToCompatibleOpen sq) (op U) ⟶
      ((commRingInverseImage (Hom.Conormal.compatibleOpenToCoborder i i' g)).obj
        (closedGradeSheaf (IsImmersion.liftCoborder i))).obj.obj (op U) :=
  let e := Hom.Conormal.compatibleOpenToCoborder i i' g
  let G := closedGradeSheaf (IsImmersion.liftCoborder i)
  compatibleGradeSection sq U ≫
    (toSheafify (smallEtaleTopology (Hom.coborder i))
      (closedGradePresheaf (IsImmersion.liftCoborder i))).app
      (op ((etaleRestriction e).obj U)) ≫
    ((commRingInverseImageAdjunction e).unit.app G).hom.app
      (op ((etaleRestriction e).obj U)) ≫
    commRingPushforwardEvaluation e ((commRingInverseImage e).obj G)
      (Hom.Conormal.restrictionGraph e U)

/-- The reverse comparison on the actual associated-graded presheaf. -/
def compatibleGradeInversePresheaf {Z X Z' X' : AlgebraicSpace S}
    {f : Z ⟶ Z'} {i : Z ⟶ X} {i' : Z' ⟶ X'} {g : X ⟶ X'}
    [IsImmersion i] [IsImmersion i'] (sq : CommSq f i i' g) :
    closedGradePresheaf (Hom.Conormal.liftToCompatibleOpen sq) ⟶
      ((commRingInverseImage (Hom.Conormal.compatibleOpenToCoborder i i' g)).obj
        (closedGradeSheaf (IsImmersion.liftCoborder i))).obj where
  app U := compatibleGradeInverseApp sq U.unop
  naturality := sorry

/-- The actual reverse graded restriction map is the sheafification lift of the
specified identity-ring associated-graded maps. -/
def compatibleOpenGradeMapInv {Z X Z' X' : AlgebraicSpace S}
    {f : Z ⟶ Z'} {i : Z ⟶ X} {i' : Z' ⟶ X'} {g : X ⟶ X'}
    [IsImmersion i] [IsImmersion i'] (sq : CommSq f i i' g) :
    closedGradeSheaf (Hom.Conormal.liftToCompatibleOpen sq) ⟶
      (commRingInverseImage (Hom.Conormal.compatibleOpenToCoborder i i' g)).obj
        (closedGradeSheaf (IsImmersion.liftCoborder i)) :=
  ⟨sheafifyLift _ (compatibleGradeInversePresheaf sq)
    (((commRingInverseImage (Hom.Conormal.compatibleOpenToCoborder i i' g)).obj
      (closedGradeSheaf (IsImmersion.liftCoborder i))).property)⟩

/-- Graded restriction has two actual maps and their inverse laws. -/
def compatibleOpenGradeIso {Z X Z' X' : AlgebraicSpace S}
    {f : Z ⟶ Z'} {i : Z ⟶ X} {i' : Z' ⟶ X'} {g : X ⟶ X'}
    [IsImmersion i] [IsImmersion i'] (sq : CommSq f i i' g) :
    (commRingInverseImage (Hom.Conormal.compatibleOpenToCoborder i i' g)).obj
        (closedGradeSheaf (IsImmersion.liftCoborder i)) ≅
      closedGradeSheaf (Hom.Conormal.liftToCompatibleOpen sq) where
  hom := compatibleOpenGradeMap sq
  inv := compatibleOpenGradeMapInv sq
  hom_inv_id := sorry
  inv_hom_id := sorry

/-- The specified forward graded restriction map is invertible. -/
instance instIsIso_compatibleOpenGradeMap {Z X Z' X' : AlgebraicSpace S}
    {f : Z ⟶ Z'} {i : Z ⟶ X} {i' : Z' ⟶ X'} {g : X ⟶ X'}
    [IsImmersion i] [IsImmersion i'] (sq : CommSq f i i' g) :
    IsIso (compatibleOpenGradeMap sq) := (compatibleOpenGradeIso sq).isIso_hom

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
          (compatibleOpenGradeMapInv sq) ≫
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

/-- The canonical underlying comparison of `𝒪_Z`-algebras `f^* C_{Z'/X',*} ⟶ C_{Z/X,*}` induced by a
commutative square of immersions of algebraic spaces over `S`. -/
noncomputable def map {Z X Z' X' : AlgebraicSpace S}
    {f : Z ⟶ Z'} {i : Z ⟶ X} {i' : Z' ⟶ X'} {g : X ⟶ X'}
    [IsImmersion i] [IsImmersion i'] (sq : CommSq f i i' g) :
    pullback f i' ⟶ total i :=
  ⟨Under.homMk (mapSheaf sq) (mapSheaf_comp sq)⟩

/-- In degree one, `mapPiece` recovers the conormal-sheaf comparison induced by the same commutative square. -/
theorem mapPiece_one {Z X Z' X' : AlgebraicSpace S}
    {f : Z ⟶ Z'} {i : Z ⟶ X} {i' : Z' ⟶ X'} {g : X ⟶ X'}
    [IsImmersion i] [IsImmersion i'] (sq : CommSq f i i' g) :
    mapPiece sq 1 =
      eqToHom (congrArg (Modules.pullback f).obj (piece_one i')) ≫
        Hom.Conormal.map sq ≫ eqToHom (piece_one i).symm :=
  sorry


set_option maxRecDepth 2048 in
/-- The homogeneous inclusion of the successive quotient in degree `n` into the
module underlying the total conormal algebra. -/
noncomputable def degreeToTotal {Z X : AlgebraicSpace S}
    (i : Z ⟶ X) [IsImmersion i] (n : ℕ) :
    piece i n ⟶ QcAlgebraUnder.underlyingModule (total i) := by
  let j := IsImmersion.liftCoborder i
  let N := QcAlgebraUnder.underlyingModule (total i)
  let e : (commRingUnderlying Z).obj (totalSheaf i) ⟶
      (Sheaf.InternalModule.ToInternal.underlying (structureSheaf Z)).obj N :=
    ⟨{ app := fun U ↦ TypeCat.ofHom (fun x ↦ x)
       naturality := sorry }⟩
  let a : coborderGradeSheaf i ⟶ (commRingPushforward j).obj (totalSheaf i) :=
    (commRingInverseImageAdjunction j).homEquiv _ _ (totalInr i)
  let b := (commRingUnderlying (Hom.coborder i)).map a ≫
    (commRingPushforwardUnderlyingIso j).hom.app (totalSheaf i) ≫
    (typePushforward j).map e ≫
    (RingedSite.ToposHom.ModulePushforward.forgetIso (ringedToposHom j)).inv.app N
  let P : (smallEtaleSite (Hom.coborder i))ᵒᵖ ⥤ AddCommGrpCat.{u} :=
    { obj := fun U ↦ AddCommGrpCat.of
        (Ideal.AssociatedGraded.stage (KernelIdeal.sectionIdeal (coborderKernelMap i) U)
          ((commStructureSheaf (Hom.coborder i)).obj.obj U) n)
      map := fun h ↦ AddCommGrpCat.ofHom
        { toFun := fun x ↦ ⟨((commStructureSheaf (Hom.coborder i)).obj.map h).hom x.val,
            by sorry⟩
          map_zero' := by ext; exact map_zero _
          map_add' := by intros; ext; exact map_add _ _ _ }
      map_id := sorry
      map_comp := sorry }
  let power := (coborderIdealPower i n).toModule
  let target := (Modules.pushforward j).obj N
  let toPower : P ⟶ ((SheafOfModules.toSheaf (structureSheaf (Hom.coborder i))).obj power).obj :=
    { app := fun U ↦ AddCommGrpCat.ofHom
        { toFun := fun x ↦ (Hom.Conormal.subobjectSectionsIso
            (coborderIdealPower i n) U).inv ⟨x.val, by sorry⟩
          map_zero' := sorry
          map_add' := sorry }
      naturality := sorry }
  let toTarget : P ⟶ ((SheafOfModules.toSheaf (structureSheaf (Hom.coborder i))).obj target).obj :=
    { app := fun U ↦ AddCommGrpCat.ofHom
        { toFun := fun x ↦
            let I := KernelIdeal.sectionIdeal (coborderKernelMap i) U
            let q : Ideal.AssociatedGraded.piece I
                ((commStructureSheaf (Hom.coborder i)).obj.obj U) n :=
              Submodule.Quotient.mk x
            let h := (Ideal.AssociatedGraded.gradeEquivPiece I n).symm q
            b.hom.app U
              (((toSheafify (smallEtaleTopology (Hom.coborder i))
                (coborderGradePresheaf i)).app U).hom h.val)
          map_zero' := sorry
          map_add' := sorry }
      naturality := sorry }
  have hdesc : (smallEtaleTopology (Hom.coborder i)).W toPower := by sorry
  let c := (hdesc.homEquiv _
    ((SheafOfModules.toSheaf (structureSheaf (Hom.coborder i))).obj target).property).symm
      toTarget
  let powerToTotal : power ⟶ target :=
    { val :=
        { app := fun U ↦ @ModuleCat.ofHom
            ((structureSheaf (Hom.coborder i)).obj.obj U) _
            (power.val.obj U) (target.val.obj U)
            (power.val.obj U).isAddCommGroup (power.val.obj U).isModule
            (target.val.obj U).isAddCommGroup (target.val.obj U).isModule
            { toFun := (c.app U).hom
              map_add' := map_add _
              map_smul' := sorry }
          naturality := sorry } }
  exact Modules.adjointToPushforward j
    (cokernel.desc _ powerToTotal (by sorry))

/-- Scalar extension of the underlying module maps canonically to the module
underlying the pulled-back total algebra, through its pushout inclusion. -/
noncomputable def pullbackTotalModuleComparison {Z Z' X' : AlgebraicSpace S}
    (f : Z ⟶ Z') (i' : Z' ⟶ X') [IsImmersion i'] :
    (Modules.pullback f).obj (QcAlgebraUnder.underlyingModule (total i')) ⟶
      QcAlgebraUnder.underlyingModule (pullback f i') := by
  let M := QcAlgebraUnder.underlyingModule (total i')
  let N := QcAlgebraUnder.underlyingModule (pullback f i')
  let eM : (Sheaf.InternalModule.ToInternal.underlying (structureSheaf Z')).obj M ⟶
      (commRingUnderlying Z').obj (totalSheaf i') :=
    ⟨{ app := fun U ↦ TypeCat.ofHom (fun x ↦ x)
       naturality := sorry }⟩
  let eN : (commRingUnderlying Z).obj (pullbackSheaf f i') ⟶
      (Sheaf.InternalModule.ToInternal.underlying (structureSheaf Z)).obj N :=
    ⟨{ app := fun U ↦ TypeCat.ofHom (fun x ↦ x)
       naturality := sorry }⟩
  let a : totalSheaf i' ⟶ (commRingPushforward f).obj (pullbackSheaf f i') :=
    (commRingInverseImageAdjunction f).homEquiv _ _
      (pushout.inr (inverseImageStructureSheafHom f)
        ((commRingInverseImage f).map (structureMap i')))
  let b := eM ≫ (commRingUnderlying Z').map a ≫
    (commRingPushforwardUnderlyingIso f).hom.app (pullbackSheaf f i') ≫
    (typePushforward f).map eN ≫
    (RingedSite.ToposHom.ModulePushforward.forgetIso (ringedToposHom f)).inv.app N
  exact Modules.adjointToPushforward f
    (Sheaf.InternalModule.homOfUnderlying (structureSheaf Z') b (by sorry) (by sorry))

/-- The homogeneous inclusion of a pulled-back conormal piece into the module
underlying the pulled-back total conormal algebra. -/
noncomputable def pullbackDegreeToTotal {Z Z' X' : AlgebraicSpace S}
    (f : Z ⟶ Z') (i' : Z' ⟶ X') [IsImmersion i'] (n : ℕ) :
    (Modules.pullback f).obj (piece i' n) ⟶
      QcAlgebraUnder.underlyingModule (pullback f i') :=
  (Modules.pullback f).map (degreeToTotal i' n) ≫
    pullbackTotalModuleComparison f i'

/-- The canonical conormal algebra comparison preserves every homogeneous piece. -/
theorem map_graded {Z X Z' X' : AlgebraicSpace S}
    {f : Z ⟶ Z'} {i : Z ⟶ X} {i' : Z' ⟶ X'} {g : X ⟶ X'}
    [IsImmersion i] [IsImmersion i'] (sq : CommSq f i i' g) :
    ∀ n : ℕ, pullbackDegreeToTotal f i' n ≫ QcAlgebraUnder.underlyingModuleMap (map sq) =
      mapPiece sq n ≫ degreeToTotal i n :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.ConormalAlgebra
