/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Immersion
public import Mathlib.CategoryTheory.Abelian.Basic
public import Mathlib.CategoryTheory.CommSq
public import ReasLib.AlgebraicGeometry.Scheme.Module.Conormal
public import ReasLib.AlgebraicGeometry.Scheme.Module.Conormal.ClosedImmersion
public import Mathlib.CategoryTheory.Adjunction.Mates
public import ReasLib.AlgebraicGeometry.RingedSite.Module.Adjunction
public import ReasLib.AlgebraicGeometry.RingedSite.Module.BaseChange
public import ReasLib.AlgebraicGeometry.RingedSite.Module.Pushforward.Composition
public import ReasLib.CategoryTheory.Sites.Topos.ModuleAdjunction
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Ringed
public import Mathlib.AlgebraicGeometry.Restrict
public import stacks_project.Chap66.Definition_66_4_1_Points
public import stacks_project.Chap66.Lemma_66_18_13_Glueing
public import stacks_project.Chap66.Lemma_66_26_3_Glueing
public import stacks_project.Chap66.Proposition_66_32_1_Comparison
public import stacks_project.Chap67.Lemma_67_14_1_Quotient
public import stacks_project.Chap67.Lemma_67_28_12_IdealSheaf
public import stacks_project.Chap67.Remark_67_12_4_Coborder
public import stacks_project.Chap70.Lemma_70_5_6_GlobalSections
public import stacks_project.Chap76.Definition_76_6_5_Conormal
public import stacks_project.Chap76.Lemma_76_5_3_Map

/-!
# Scheme comparison and composition for conormal sheaves of immersions

For an immersion of schemes over `S`, restriction of the algebraic-space conormal sheaf
along `Modules.restrictToScheme` is canonically isomorphic to `Scheme.Hom.conormalSheaf`.
On a commutative square of schemes, `Hom.Conormal.map` recovers `Scheme.Hom.Conormal.map`,
and stacked squares compose via `CommSq.horiz_comp` and `Modules.pullbackComp`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry (Scheme)
open CategoryTheory.Sheaf.InternalModule
open TopologicalSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

variable {S : Scheme.{u}}

/-- An immersion of schemes over `S` remains an immersion of algebraic spaces after
`ofOverMap`. -/
instance instIsImmersion_ofOverMap {Z X : Over S} (i : Z ⟶ X)
    [AlgebraicGeometry.IsImmersion i.left] : IsImmersion (ofOverMap i) :=
  sorry

/-- A commutative square in `Over S` remains commutative after applying `ofOverMap`. -/
theorem ofOverCommSq {Z X Z' X' : Over S} {f : Z ⟶ Z'} {i : Z ⟶ X} {i' : Z' ⟶ X'}
    {g : X ⟶ X'} (sq : CommSq f i i' g) :
    CommSq (ofOverMap f) (ofOverMap i) (ofOverMap i') (ofOverMap g) :=
  sorry

/-- The commutative square of underlying scheme morphisms of a commutative square in
`Over S`. -/
theorem ofOverSqLeft {Z X Z' X' : Over S} {f : Z ⟶ Z'} {i : Z ⟶ X} {i' : Z' ⟶ X'}
    {g : X ⟶ X'} (sq : CommSq f i i' g) :
    CommSq f.left i.left i'.left g.left :=
  sorry

namespace Hom.Conormal

/-- The coborder open of an immersion of schemes over `S`, as an object of `Over S`. -/
def schemeCoborder {Z X : Over S} (i : Z ⟶ X)
    [AlgebraicGeometry.IsImmersion i.left] : Over S :=
  Over.mk (i.left.coborderRange.ι ≫ X.hom)

/-- Compatibility of the scheme coborder closed immersion with the structure morphisms
over `S`. -/
theorem schemeLiftCoborderOver_w {Z X : Over S} (i : Z ⟶ X)
    [AlgebraicGeometry.IsImmersion i.left] :
    i.left.liftCoborder ≫ (schemeCoborder i).hom = Z.hom :=
  sorry

/-- The coborder closed immersion of an immersion of schemes over `S`, as a morphism
in `Over S`. -/
def schemeLiftCoborderOver {Z X : Over S} (i : Z ⟶ X)
    [AlgebraicGeometry.IsImmersion i.left] :
    Z ⟶ schemeCoborder i :=
  Over.homMk i.left.liftCoborder (schemeLiftCoborderOver_w i)

/-- The underlying scheme morphism of `schemeLiftCoborderOver i` is the coborder closed
immersion. -/
instance instIsImmersion_schemeLiftCoborderOver_left {Z X : Over S} (i : Z ⟶ X)
    [AlgebraicGeometry.IsImmersion i.left] :
    AlgebraicGeometry.IsImmersion (schemeLiftCoborderOver i).left :=
  inferInstanceAs (AlgebraicGeometry.IsImmersion i.left.liftCoborder)

/-- An immersion of schemes over `S` remains an immersion after passing to the coborder
closed immersion as an algebraic-space morphism. -/
instance instIsImmersion_ofOverMap_schemeLiftCoborderOver {Z X : Over S} (i : Z ⟶ X)
    [AlgebraicGeometry.IsImmersion i.left] :
    IsImmersion (ofOverMap (schemeLiftCoborderOver i)) :=
  instIsImmersion_ofOverMap (schemeLiftCoborderOver i)

/-- Compatibility of the coborder open immersion with the structure morphisms over `S`. -/
theorem schemeCoborderι_w {Z X : Over S} (i : Z ⟶ X)
    [AlgebraicGeometry.IsImmersion i.left] :
    i.left.coborderRange.ι ≫ X.hom = (schemeCoborder i).hom :=
  rfl

/-- The coborder open immersion of an immersion of schemes over `S`, as a morphism
in `Over S`. -/
def schemeCoborderι {Z X : Over S} (i : Z ⟶ X)
    [AlgebraicGeometry.IsImmersion i.left] :
    schemeCoborder i ⟶ X :=
  Over.homMk i.left.coborderRange.ι (schemeCoborderι_w i)

/-- Factoring an immersion of schemes over `S` through its coborder closed immersion. -/
theorem schemeFactorizationSq {Z X : Over S} (i : Z ⟶ X)
    [AlgebraicGeometry.IsImmersion i.left] :
    CommSq (𝟙 Z) (schemeLiftCoborderOver i) i (schemeCoborderι i) :=
  sorry

/-- Equal morphisms of algebraic spaces induce isomorphic module pullbacks. -/
def modulesPullbackCongr {Y W : AlgebraicSpace S} {f g : Y ⟶ W} (h : f = g) :
    Modules.pullback f ≅ Modules.pullback g :=
  eqToIso (congrArg Modules.pullback h)

/-- Forward space-level comparison of conormal sheaves along the coborder factorization of an
immersion of schemes over `S`. -/
noncomputable def factorizationMap {Z X : Over S} (i : Z ⟶ X)
    [AlgebraicGeometry.IsImmersion i.left] :
    Hom.conormalSheaf (ofOverMap i) ⟶
      Hom.conormalSheaf (ofOverMap (schemeLiftCoborderOver i)) :=
  (SmallEtaleModuleGlueing.modulesPullbackId (ofOver Z)).inv.app
      (Hom.conormalSheaf (ofOverMap i)) ≫
    (modulesPullbackCongr (SmallEtaleGlueing.ofOverMap_id Z).symm).hom.app
      (Hom.conormalSheaf (ofOverMap i)) ≫
    Hom.Conormal.map (ofOverCommSq (schemeFactorizationSq i))

/-- Changing only the ambient coborder open preserves the ideal quotient.
This invertibility is specific to the factorization square, not an arbitrary square. -/
instance instIsIso_idealQuotientMap_restrictedFactorizationSq {Z X : Over S} (i : Z ⟶ X)
    [AlgebraicGeometry.IsImmersion i.left] :
    IsIso (idealQuotientMap (restrictedSq (ofOverCommSq (schemeFactorizationSq i)))) :=
  sorry

/-- Reverse of `Hom.Conormal.map`, obtained by reversing each comparison in the coborder
compatible-open composite. -/
noncomputable def mapInv {Z X Z' X' : AlgebraicSpace S} {f : Z ⟶ Z'} {i : Z ⟶ X}
    {i' : Z' ⟶ X'} {g : X ⟶ X'} [IsImmersion i] [IsImmersion i'] (sq : CommSq f i i' g)
    [IsIso (idealQuotientMap (restrictedSq sq))] :
    Hom.conormalSheaf i ⟶ (Modules.pullback f).obj (Hom.conormalSheaf i') :=
  (eqToIso (congrArg Modules.pullback (liftToCompatibleOpen_comp_toCoborder sq))).inv.app
      (Modules.quotientByIdeal (Hom.idealSheafSubobject (IsImmersion.liftCoborder i))
        (Hom.idealSheaf (IsImmersion.liftCoborder i))) ≫
    (Modules.pullbackComp (liftToCompatibleOpen sq)
        (compatibleOpenToCoborder i i' g)).inv.app
      (Modules.quotientByIdeal (Hom.idealSheafSubobject (IsImmersion.liftCoborder i))
        (Hom.idealSheaf (IsImmersion.liftCoborder i))) ≫
    (Modules.pullback (liftToCompatibleOpen sq)).map (compatibleOpenQuotientMap sq) ≫
    (Modules.pullback (liftToCompatibleOpen sq)).map
      (inv (idealQuotientMap (restrictedSq sq))) ≫
    (Modules.pullbackComp (liftToCompatibleOpen sq)
        (restrictToCompatibleOpen i i' g)).hom.app
      (Modules.quotientByIdeal (Hom.idealSheafSubobject (IsImmersion.liftCoborder i'))
        (Hom.idealSheaf (IsImmersion.liftCoborder i'))) ≫
    (eqToIso (congrArg Modules.pullback (restrictedSq sq).w)).inv.app
      (Modules.quotientByIdeal (Hom.idealSheafSubobject (IsImmersion.liftCoborder i'))
        (Hom.idealSheaf (IsImmersion.liftCoborder i'))) ≫
    (Modules.pullbackComp f (IsImmersion.liftCoborder i')).inv.app
      (Modules.quotientByIdeal (Hom.idealSheafSubobject (IsImmersion.liftCoborder i'))
        (Hom.idealSheaf (IsImmersion.liftCoborder i')))

/-- Reverse space-level comparison of conormal sheaves along the coborder factorization. -/
noncomputable def factorizationMapInv {Z X : Over S} (i : Z ⟶ X)
    [AlgebraicGeometry.IsImmersion i.left] :
    Hom.conormalSheaf (ofOverMap (schemeLiftCoborderOver i)) ⟶
      Hom.conormalSheaf (ofOverMap i) :=
  mapInv (ofOverCommSq (schemeFactorizationSq i)) ≫
    (modulesPullbackCongr (SmallEtaleGlueing.ofOverMap_id Z).symm).inv.app
      (Hom.conormalSheaf (ofOverMap i)) ≫
    (SmallEtaleModuleGlueing.modulesPullbackId (ofOver Z)).hom.app
      (Hom.conormalSheaf (ofOverMap i))

/-- The coborder ideal quotient of the closed immersion `ofOverMap (schemeLiftCoborderOver i)`. -/
noncomputable def closedIdealQuotient {Z X : Over S} (i : Z ⟶ X)
    [AlgebraicGeometry.IsImmersion i.left] :
    (ofOver (schemeCoborder i)).Modules :=
  Modules.quotientByIdeal
    (Hom.idealSheafSubobject (ofOverMap (schemeLiftCoborderOver i)))
    (Hom.idealSheaf (ofOverMap (schemeLiftCoborderOver i)))

/-- The ideal quotient of the coborder closed immersion is quasi-coherent. -/
instance closedIdealQuotient_isQuasicoherent {Z X : Over S} (i : Z ⟶ X)
    [AlgebraicGeometry.IsImmersion i.left] :
    (closedIdealQuotient i).IsQuasicoherent := sorry

/-- The closed-immersion formula `j^* (I / I²)` for the coborder closed immersion of `i`. -/
noncomputable def closedConormalPullback {Z X : Over S} (i : Z ⟶ X)
    [AlgebraicGeometry.IsImmersion i.left] :
    (ofOver Z).Modules :=
  (Modules.pullback (ofOverMap (schemeLiftCoborderOver i))).obj (closedIdealQuotient i)

/-- The pulled coborder kernel of `ofOverMap j` vanishes after mapping to `j_* 𝒪_Z`. -/
theorem closedPulledIdeal_vanishes {Z X : Over S} (i : Z ⟶ X)
    [AlgebraicGeometry.IsImmersion i.left] :
    IdealSubobject.pullbackMap
          (Hom.idealSheafSubobject (ofOverMap (schemeLiftCoborderOver i)))
          (IsImmersion.coborderRange (ofOverMap (schemeLiftCoborderOver i))).ι ≫
        Hom.idealSheafMap (IsImmersion.liftCoborder (ofOverMap (schemeLiftCoborderOver i))) =
      0 :=
  sorry

/-- Comparison of kernel ideals along the coborder open of the closed immersion
`ofOverMap (schemeLiftCoborderOver i)`. -/
noncomputable def closedPulledIdealToIdeal {Z X : Over S} (i : Z ⟶ X)
    [AlgebraicGeometry.IsImmersion i.left] :
    (Modules.pullback
          (IsImmersion.coborderRange (ofOverMap (schemeLiftCoborderOver i))).ι).obj
        (Hom.idealSheaf (ofOverMap (schemeLiftCoborderOver i))) ⟶
      Hom.idealSheaf (IsImmersion.liftCoborder (ofOverMap (schemeLiftCoborderOver i))) :=
  kernel.lift
      (Hom.idealSheafMap (IsImmersion.liftCoborder (ofOverMap (schemeLiftCoborderOver i))))
      (IdealSubobject.pullbackMap
        (Hom.idealSheafSubobject (ofOverMap (schemeLiftCoborderOver i)))
        (IsImmersion.coborderRange (ofOverMap (schemeLiftCoborderOver i))).ι)
      (closedPulledIdeal_vanishes i) ≫
    (Hom.idealSheaf_spec (IsImmersion.liftCoborder (ofOverMap (schemeLiftCoborderOver i)))).inv

/-- The pulled ideal-sheaf action followed by `closedPulledIdealToIdeal ≫ π` is zero. -/
theorem closedPulledIdealAction_comp_π {Z X : Over S} (i : Z ⟶ X)
    [AlgebraicGeometry.IsImmersion i.left] :
    (Modules.pullback
            (IsImmersion.coborderRange (ofOverMap (schemeLiftCoborderOver i))).ι).map
          (Modules.idealAction
            (Hom.idealSheafSubobject (ofOverMap (schemeLiftCoborderOver i)))
            (Hom.idealSheaf (ofOverMap (schemeLiftCoborderOver i)))) ≫
        closedPulledIdealToIdeal i ≫
          Modules.quotientByIdeal.π
            (Hom.idealSheafSubobject
              (IsImmersion.liftCoborder (ofOverMap (schemeLiftCoborderOver i))))
            (Hom.idealSheaf
              (IsImmersion.liftCoborder (ofOverMap (schemeLiftCoborderOver i)))) =
      0 :=
  sorry

/-- Restriction of `I / I²` along the coborder open of the closed immersion
`ofOverMap (schemeLiftCoborderOver i)`. -/
noncomputable def closedRestrictQuotient {Z X : Over S} (i : Z ⟶ X)
    [AlgebraicGeometry.IsImmersion i.left] :
    (Modules.pullback
          (IsImmersion.coborderRange (ofOverMap (schemeLiftCoborderOver i))).ι).obj
        (closedIdealQuotient i) ⟶
      Modules.quotientByIdeal
        (Hom.idealSheafSubobject
          (IsImmersion.liftCoborder (ofOverMap (schemeLiftCoborderOver i))))
        (Hom.idealSheaf
          (IsImmersion.liftCoborder (ofOverMap (schemeLiftCoborderOver i)))) :=
  (PreservesCokernel.iso
        (Modules.pullback
          (IsImmersion.coborderRange (ofOverMap (schemeLiftCoborderOver i))).ι)
        (Modules.idealAction
          (Hom.idealSheafSubobject (ofOverMap (schemeLiftCoborderOver i)))
          (Hom.idealSheaf (ofOverMap (schemeLiftCoborderOver i))))).hom ≫
    cokernel.desc
      ((Modules.pullback
            (IsImmersion.coborderRange (ofOverMap (schemeLiftCoborderOver i))).ι).map
        (Modules.idealAction
          (Hom.idealSheafSubobject (ofOverMap (schemeLiftCoborderOver i)))
          (Hom.idealSheaf (ofOverMap (schemeLiftCoborderOver i)))))
      (closedPulledIdealToIdeal i ≫
        Modules.quotientByIdeal.π
          (Hom.idealSheafSubobject
            (IsImmersion.liftCoborder (ofOverMap (schemeLiftCoborderOver i))))
          (Hom.idealSheaf
            (IsImmersion.liftCoborder (ofOverMap (schemeLiftCoborderOver i)))))
      (closedPulledIdealAction_comp_π i)

/-- The pulled inclusion of the closed-immersion kernel along the coborder open is a
monomorphism. -/
instance instMono_closedPulledIdealι {Z X : Over S} (i : Z ⟶ X)
    [AlgebraicGeometry.IsImmersion i.left] :
    Mono
      ((Modules.pullback
            (IsImmersion.coborderRange (ofOverMap (schemeLiftCoborderOver i))).ι).map
        (Hom.idealSheafι (ofOverMap (schemeLiftCoborderOver i)))) :=
  sorry

/-- The coborder kernel inclusion vanishes on the cokernel of the pulled closed-immersion
kernel inclusion. -/
theorem closedIdealToPulledIdeal_comp_π {Z X : Over S} (i : Z ⟶ X)
    [AlgebraicGeometry.IsImmersion i.left] :
    (Hom.idealSheafι (IsImmersion.liftCoborder (ofOverMap (schemeLiftCoborderOver i))) ≫
          Modules.structureModulePullbackInv
            (IsImmersion.coborderRange (ofOverMap (schemeLiftCoborderOver i))).ι) ≫
        cokernel.π
          ((Modules.pullback
                (IsImmersion.coborderRange (ofOverMap (schemeLiftCoborderOver i))).ι).map
            (Hom.idealSheafι (ofOverMap (schemeLiftCoborderOver i)))) =
      0 :=
  sorry

/-- Reverse comparison of kernel ideals along the coborder open. -/
noncomputable def closedIdealToPulledIdeal {Z X : Over S} (i : Z ⟶ X)
    [AlgebraicGeometry.IsImmersion i.left] :
    Hom.idealSheaf (IsImmersion.liftCoborder (ofOverMap (schemeLiftCoborderOver i))) ⟶
      (Modules.pullback
          (IsImmersion.coborderRange (ofOverMap (schemeLiftCoborderOver i))).ι).obj
        (Hom.idealSheaf (ofOverMap (schemeLiftCoborderOver i))) :=
  CategoryTheory.Abelian.monoLift
    ((Modules.pullback
          (IsImmersion.coborderRange (ofOverMap (schemeLiftCoborderOver i))).ι).map
      (Hom.idealSheafι (ofOverMap (schemeLiftCoborderOver i))))
    (Hom.idealSheafι (IsImmersion.liftCoborder (ofOverMap (schemeLiftCoborderOver i))) ≫
      Modules.structureModulePullbackInv
        (IsImmersion.coborderRange (ofOverMap (schemeLiftCoborderOver i))).ι)
    (closedIdealToPulledIdeal_comp_π i)

/-- The coborder ideal-sheaf action followed by the reverse kernel comparison and the
pulled quotient projection is zero. -/
theorem closedRestrictQuotientInv_comp_π {Z X : Over S} (i : Z ⟶ X)
    [AlgebraicGeometry.IsImmersion i.left] :
    Modules.idealAction
          (Hom.idealSheafSubobject
            (IsImmersion.liftCoborder (ofOverMap (schemeLiftCoborderOver i))))
          (Hom.idealSheaf
            (IsImmersion.liftCoborder (ofOverMap (schemeLiftCoborderOver i)))) ≫
        closedIdealToPulledIdeal i ≫
          (Modules.pullback
              (IsImmersion.coborderRange (ofOverMap (schemeLiftCoborderOver i))).ι).map
            (Modules.quotientByIdeal.π
              (Hom.idealSheafSubobject (ofOverMap (schemeLiftCoborderOver i)))
              (Hom.idealSheaf (ofOverMap (schemeLiftCoborderOver i)))) =
      0 :=
  sorry

/-- Inverse restriction of `I / I²` along the coborder open. -/
noncomputable def closedRestrictQuotientInv {Z X : Over S} (i : Z ⟶ X)
    [AlgebraicGeometry.IsImmersion i.left] :
    Modules.quotientByIdeal
        (Hom.idealSheafSubobject
          (IsImmersion.liftCoborder (ofOverMap (schemeLiftCoborderOver i))))
        (Hom.idealSheaf
          (IsImmersion.liftCoborder (ofOverMap (schemeLiftCoborderOver i)))) ⟶
      (Modules.pullback
          (IsImmersion.coborderRange (ofOverMap (schemeLiftCoborderOver i))).ι).obj
        (closedIdealQuotient i) :=
  cokernel.desc
      (Modules.idealAction
        (Hom.idealSheafSubobject
          (IsImmersion.liftCoborder (ofOverMap (schemeLiftCoborderOver i))))
        (Hom.idealSheaf
          (IsImmersion.liftCoborder (ofOverMap (schemeLiftCoborderOver i)))))
      (closedIdealToPulledIdeal i ≫
        (Modules.pullback
            (IsImmersion.coborderRange (ofOverMap (schemeLiftCoborderOver i))).ι).map
          (Modules.quotientByIdeal.π
            (Hom.idealSheafSubobject (ofOverMap (schemeLiftCoborderOver i)))
            (Hom.idealSheaf (ofOverMap (schemeLiftCoborderOver i)))))
      (closedRestrictQuotientInv_comp_π i)

/-- Forward unfolding of the space conormal of the coborder closed immersion to
`j^* (I / I²)`. -/
noncomputable def closedUnfold {Z X : Over S} (i : Z ⟶ X)
    [AlgebraicGeometry.IsImmersion i.left] :
    Hom.conormalSheaf (ofOverMap (schemeLiftCoborderOver i)) ⟶ closedConormalPullback i :=
  (Modules.pullback
        (IsImmersion.liftCoborder (ofOverMap (schemeLiftCoborderOver i)))).map
      (closedRestrictQuotientInv i) ≫
    (Modules.pullbackComp
        (IsImmersion.liftCoborder (ofOverMap (schemeLiftCoborderOver i)))
        (IsImmersion.coborderRange (ofOverMap (schemeLiftCoborderOver i))).ι).hom.app
      (closedIdealQuotient i) ≫
    (modulesPullbackCongr
        (IsImmersion.liftCoborder_comp (ofOverMap (schemeLiftCoborderOver i)))).hom.app
      (closedIdealQuotient i)

/-- Reverse unfolding from `j^* (I / I²)` to the space conormal of the coborder closed
immersion. -/
noncomputable def closedUnfoldInv {Z X : Over S} (i : Z ⟶ X)
    [AlgebraicGeometry.IsImmersion i.left] :
    closedConormalPullback i ⟶
      Hom.conormalSheaf (ofOverMap (schemeLiftCoborderOver i)) :=
  (modulesPullbackCongr
        (IsImmersion.liftCoborder_comp (ofOverMap (schemeLiftCoborderOver i)))).inv.app
      (closedIdealQuotient i) ≫
    (Modules.pullbackComp
        (IsImmersion.liftCoborder (ofOverMap (schemeLiftCoborderOver i)))
        (IsImmersion.coborderRange (ofOverMap (schemeLiftCoborderOver i))).ι).inv.app
      (closedIdealQuotient i) ≫
    (Modules.pullback
        (IsImmersion.liftCoborder (ofOverMap (schemeLiftCoborderOver i)))).map
      (closedRestrictQuotient i)

/-- Reverse of `idealCotangentPullbackComparison`, obtained from the named closed-immersion
isomorphism rather than identity transport of sections. -/
noncomputable def idealCotangentPullbackComparisonInv {Z U : AlgebraicGeometry.Scheme.{u}}
    (j : Z ⟶ U) [AlgebraicGeometry.IsClosedImmersion j] :
    AlgebraicGeometry.Scheme.Hom.conormalSheaf j ⟶
      (AlgebraicGeometry.Scheme.Modules.pullback j).obj
        (AlgebraicGeometry.Scheme.Hom.Conormal.idealCotangentSheaf j) :=
  (@asIso _ _ _ _
      (AlgebraicGeometry.Scheme.Hom.Conormal.idealCotangentPullbackComparison j)
      (AlgebraicGeometry.Scheme.Hom.Conormal.idealCotangentPullbackComparison_isIso j)).inv

/-- The ringed-site composite from the small étale site of `ofOver U` to the open-subscheme
ringed site of `U.left`. -/
noncomputable def restrictToOpensHom (U : Over S) :
    RingedSite.Hom (ringedSite (ofOver U))
      (RingedSite.ofRingSheaf (Opens.grothendieckTopology (U.left : TopCat))
        ⟨Scheme.Site.structurePresheaf (U.left.restrictFunctor ⋙ Over.forget U.left),
          opensStructurePresheaf_isSheaf U.left⟩) :=
  RingedSite.Hom.comp (schemeEtaleRingedHom U) (smallEtaleToOpensRingedHom U.left)

/-- Continuity of the named restriction functor, projected from its ringed-site morphism. -/
instance restrictToOpensHom_isContinuous (U : Over S) :
    (restrictToOpensHom U).base.IsContinuous
      (Opens.grothendieckTopology (U.left : TopCat)) (smallEtaleTopology (ofOver U)) :=
  RingedSite.Hom.base_isContinuous (restrictToOpensHom U)

/-- Identification of the two-stage module pushforward in `restrictToScheme` with pushforward
along `restrictToOpensHom`. -/
noncomputable def restrictToOpensPushforwardIso (U : Over S) :
    (schemeEtaleRingedHom U).modulePushforward.{u} ⋙
        (smallEtaleToOpensRingedHom U.left).modulePushforward.{u} ≅
      (restrictToOpensHom U).modulePushforward.{u} :=
  RingedSite.Hom.modulePushforwardCompIso.{u}
    (schemeEtaleRingedHom U) (smallEtaleToOpensRingedHom U.left)

/-- Transport of `restrictToScheme` along the module-pushforward composite of
`restrictToOpensHom`. -/
noncomputable def restrictToSchemeOpensIso {U : Over S} (F : (ofOver U).Modules) :
    (Modules.restrictToScheme U).obj F ≅
      (opensToSchemeModules U.left).obj
        ((restrictToOpensHom U).modulePushforward.{u}.obj
          ((Modules.restrictFunctor (𝟙 (ofOver U))).obj F)) :=
  (opensToSchemeModules U.left).mapIso
    ((restrictToOpensPushforwardIso U).app ((Modules.restrictFunctor (𝟙 (ofOver U))).obj F))

/-- The `Over S` morphism recovered from a morphism of algebraic spaces between schemes
over `S`. -/
noncomputable def overHomOf {U V : Over S} (φ : ofOver U ⟶ ofOver V) : U ⟶ V :=
  Yoneda.fullyFaithful.preimage (φ : yoneda.obj U ⟶ yoneda.obj V)

/-- The scheme over `S` obtained by pulling `V` back along `f.left`. -/
noncomputable def ofOverSmallEtalePullbackOver {Z Z' : Over S} (f : Z ⟶ Z')
    (V : smallEtaleSite (ofOver Z')) : Over S :=
  Over.mk (pullback.fst f.left (overHomOf V.hom).left ≫ Z.hom)

/-- Compatibility of the fibre-product projection with the structure morphisms over `S`. -/
theorem ofOverSmallEtalePullbackHom_w {Z Z' : Over S} (f : Z ⟶ Z')
    (V : smallEtaleSite (ofOver Z')) :
    pullback.fst f.left (overHomOf V.hom).left ≫ Z.hom =
      (ofOverSmallEtalePullbackOver f V).hom :=
  rfl

/-- The morphism over `S` given by the first projection of the scheme fibre product. -/
noncomputable def ofOverSmallEtalePullbackHom {Z Z' : Over S} (f : Z ⟶ Z')
    (V : smallEtaleSite (ofOver Z')) :
    ofOverSmallEtalePullbackOver f V ⟶ Z :=
  Over.homMk (pullback.fst f.left (overHomOf V.hom).left)
    (ofOverSmallEtalePullbackHom_w f V)

/-- Pullback of an étale morphism of schemes over `S` remains étale. -/
instance instEtale_ofOverSmallEtalePullback {Z Z' : Over S} (f : Z ⟶ Z')
    (V : smallEtaleSite (ofOver Z')) :
    Etale (ofOverMap (ofOverSmallEtalePullbackHom f V)) :=
  sorry

/-- The object of the small étale site of `ofOver Z` obtained by pulling `V` back along `f`. -/
noncomputable def ofOverSmallEtalePullbackObj {Z Z' : Over S} (f : Z ⟶ Z')
    (V : smallEtaleSite (ofOver Z')) : smallEtaleSite (ofOver Z) :=
  smallEtaleSite.mk (ofOverMap (ofOverSmallEtalePullbackHom f V))

/-- The morphism of fibre products induced by a morphism in the small étale site. -/
noncomputable def ofOverSmallEtalePullbackMap {Z Z' : Over S} (f : Z ⟶ Z')
    {V V' : smallEtaleSite (ofOver Z')} (h : V' ⟶ V) :
    ofOverSmallEtalePullbackObj f V' ⟶ ofOverSmallEtalePullbackObj f V :=
  MorphismProperty.CostructuredArrow.homMk
    (Over.homMk
      (pullback.lift (pullback.fst f.left (overHomOf V'.hom).left)
        (pullback.snd f.left (overHomOf V'.hom).left ≫ h.left.left) sorry)
      sorry)
    trivial sorry

/-- Small étale pullback along a morphism of schemes over `S`. -/
noncomputable def ofOverSmallEtalePullback {Z Z' : Over S} (f : Z ⟶ Z') :
    smallEtaleSite (ofOver Z') ⥤ smallEtaleSite (ofOver Z) where
  obj := ofOverSmallEtalePullbackObj f
  map h := ofOverSmallEtalePullbackMap f h
  map_id := sorry
  map_comp := sorry

/-- Realization projection for `ofOverSmallEtalePullback f`, given by the second projection
of the scheme fibre product. -/
noncomputable def ofOverEtaleProjection {Z Z' : Over S} (f : Z ⟶ Z') :
    ofOverSmallEtalePullback f ⋙ smallEtaleToScheme (ofOver Z) ⟶
      smallEtaleToScheme (ofOver Z') where
  app V := pullback.snd f.left (overHomOf V.hom).left
  naturality _ _ _ := sorry

/-- Small étale pullback along a morphism of schemes over `S` is a morphism of sites. -/
instance instIsMorphismOfSites_ofOverSmallEtalePullback {Z Z' : Over S} (f : Z ⟶ Z') :
    IsMorphismOfSites (smallEtaleTopology (ofOver Z')) (smallEtaleTopology (ofOver Z))
      (ofOverSmallEtalePullback f) :=
  sorry

/-- The morphism of small étale ringed sites induced by a morphism of schemes over `S`. -/
noncomputable def ofOverRingedHom {Z Z' : Over S} (f : Z ⟶ Z') :
    RingedSite.Hom (ringedSite (ofOver Z)) (ringedSite (ofOver Z')) :=
  Scheme.Site.ringedHom (smallEtaleTopology (ofOver Z')) (smallEtaleTopology (ofOver Z))
    (smallEtaleToScheme (ofOver Z')) (smallEtaleToScheme (ofOver Z))
    (ofOverSmallEtalePullback f) (ofOverEtaleProjection f)
    (structurePresheaf_isSheaf (ofOver Z')) (structurePresheaf_isSheaf (ofOver Z))

/-- Module pushforward along `ofOverRingedHom` admits its canonical inverse-image left adjoint. -/
noncomputable instance instIsRightAdjoint_ofOverRingedHom_modulePushforward
    {Z Z' : Over S} (f : Z ⟶ Z') :
    ((ofOverRingedHom f).modulePushforward.{u}).IsRightAdjoint :=
  sorry

/-- Open restriction along a scheme morphism is a morphism of open-cover sites. -/
instance instIsMorphismOfSites_opensMap {X Y : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ Y) :
    IsMorphismOfSites (Opens.grothendieckTopology (Y : TopCat))
      (Opens.grothendieckTopology (X : TopCat)) (Opens.map f.base) :=
  inferInstance

/-- Realization projection for `Opens.map f.base`, given by restriction of `f` to an open. -/
noncomputable def schemeOpensProjection {X Y : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ Y) :
    Opens.map f.base ⋙ (X.restrictFunctor ⋙ Over.forget X) ⟶
      Y.restrictFunctor ⋙ Over.forget Y where
  app U := f ∣_ U
  naturality _ _ _ := sorry

/-- The morphism of open-subscheme ringed sites induced by a scheme morphism. -/
noncomputable def schemeOpensRingedHom {X Y : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ Y) :
    RingedSite.Hom
      (RingedSite.ofRingSheaf (Opens.grothendieckTopology (X : TopCat))
        ⟨Scheme.Site.structurePresheaf (X.restrictFunctor ⋙ Over.forget X),
          opensStructurePresheaf_isSheaf X⟩)
      (RingedSite.ofRingSheaf (Opens.grothendieckTopology (Y : TopCat))
        ⟨Scheme.Site.structurePresheaf (Y.restrictFunctor ⋙ Over.forget Y),
          opensStructurePresheaf_isSheaf Y⟩) :=
  Scheme.Site.ringedHom (Opens.grothendieckTopology (Y : TopCat))
    (Opens.grothendieckTopology (X : TopCat))
    (Y.restrictFunctor ⋙ Over.forget Y) (X.restrictFunctor ⋙ Over.forget X)
    (Opens.map f.base) (schemeOpensProjection f)
    (opensStructurePresheaf_isSheaf Y) (opensStructurePresheaf_isSheaf X)

/-- The two base functors in the restriction square are related by the actual
scheme pullback/open-restriction isomorphism, not equality of chosen objects. -/
noncomputable def restrictPullbackBaseIso {Z Z' : Over S} (f : Z ⟶ Z') :
    (RingedSite.Hom.comp (ofOverRingedHom f) (restrictToOpensHom Z')).base ≅
      (RingedSite.Hom.comp (restrictToOpensHom Z) (schemeOpensRingedHom f.left)).base :=
  NatIso.ofComponents
    (fun W ↦
      { hom := MorphismProperty.CostructuredArrow.homMk
          (Over.homMk (AlgebraicGeometry.pullbackRestrictIsoRestrict f.left W).hom sorry)
          trivial sorry
        inv := MorphismProperty.CostructuredArrow.homMk
          (Over.homMk (AlgebraicGeometry.pullbackRestrictIsoRestrict f.left W).inv sorry)
          trivial sorry
        hom_inv_id := sorry
        inv_hom_id := sorry }) sorry

/-- Continuity of the pullback-then-restriction presentation. -/
instance restrictPullbackLeft_isContinuous {Z Z' : Over S} (f : Z ⟶ Z') :
    (RingedSite.Hom.comp (ofOverRingedHom f) (restrictToOpensHom Z')).base.IsContinuous
      (Opens.grothendieckTopology (Z'.left : TopCat)) (smallEtaleTopology (ofOver Z)) :=
  RingedSite.Hom.base_isContinuous _

/-- Continuity of the restriction-then-pullback presentation. -/
instance restrictPullbackRight_isContinuous {Z Z' : Over S} (f : Z ⟶ Z') :
    (RingedSite.Hom.comp (restrictToOpensHom Z) (schemeOpensRingedHom f.left)).base.IsContinuous
      (Opens.grothendieckTopology (Z'.left : TopCat)) (smallEtaleTopology (ofOver Z)) :=
  RingedSite.Hom.base_isContinuous _

/-- The pullback/open-restriction isomorphism respects restriction of regular functions. -/
theorem restrictPullbackBaseIso_structure {Z Z' : Over S} (f : Z ⟶ Z') :
    (RingedSite.Hom.comp (restrictToOpensHom Z) (schemeOpensRingedHom f.left)).structureSheafMap ≫
        (Functor.sheafPushforwardContinuousNatTrans (restrictPullbackBaseIso f).hom
          RingCat.{u} _ _).app (ringedSite (ofOver Z)).structureSheaf =
      (RingedSite.Hom.comp (ofOverRingedHom f) (restrictToOpensHom Z')).structureSheafMap := sorry

/-- Direct-image coherence for the actual isomorphism of the restriction square. -/
noncomputable def restrictPullbackPushforwardIso {Z Z' : Over S} (f : Z ⟶ Z') :
    (ofOverRingedHom f).modulePushforward.{u} ⋙ (restrictToOpensHom Z').modulePushforward.{u} ≅
      (restrictToOpensHom Z).modulePushforward.{u} ⋙ (schemeOpensRingedHom f.left).modulePushforward.{u} :=
  RingedSite.Hom.modulePushforwardCompIso (ofOverRingedHom f) (restrictToOpensHom Z') ≪≫
    (SheafOfModules.pushforwardCongr₂
      (RingedSite.Hom.comp (restrictToOpensHom Z) (schemeOpensRingedHom f.left)).structureSheafMap
      (restrictPullbackBaseIso f) (restrictPullbackBaseIso_structure f)).symm ≪≫
    (RingedSite.Hom.modulePushforwardCompIso (restrictToOpensHom Z) (schemeOpensRingedHom f.left)).symm

/-- Module pushforward along `restrictToOpensHom` admits its canonical inverse-image left adjoint. -/
noncomputable instance instIsRightAdjoint_restrictToOpensHom_modulePushforward
    (U : Over S) :
    ((restrictToOpensHom U).modulePushforward.{u}).IsRightAdjoint :=
  sorry

/-- Module pushforward along `schemeOpensRingedHom` admits its canonical inverse-image left adjoint. -/
noncomputable instance instIsRightAdjoint_schemeOpensRingedHom_modulePushforward
    {X Y : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ Y) :
    ((schemeOpensRingedHom f).modulePushforward.{u}).IsRightAdjoint :=
  sorry

/-- Inverse-image comparison for the restriction square, as the mate of
`CommSq.pushforwardIso`. -/
noncomputable def restrictPullbackOpensComparison {Z Z' : Over S} (f : Z ⟶ Z') :
    (restrictToOpensHom Z').modulePushforward.{u} ⋙
        (schemeOpensRingedHom f.left).modulePullback.{u} ⟶
      (ofOverRingedHom f).modulePullback.{u} ⋙
        (restrictToOpensHom Z).modulePushforward.{u} :=
  RingedSite.Hom.BaseChange.comparison
    (ofOverRingedHom f) (restrictToOpensHom Z) (restrictToOpensHom Z')
    (schemeOpensRingedHom f.left)
    (((conjugateIsoEquiv
      ((RingedSite.Hom.modulePullbackPushforwardAdjunction (restrictToOpensHom Z')).comp
        (RingedSite.Hom.modulePullbackPushforwardAdjunction (ofOverRingedHom f)))
      ((RingedSite.Hom.modulePullbackPushforwardAdjunction (schemeOpensRingedHom f.left)).comp
        (RingedSite.Hom.modulePullbackPushforwardAdjunction (restrictToOpensHom Z)))).symm
      (restrictPullbackPushforwardIso f)).hom)

/-- The second projection of the scheme fibre product, as an arrow over the base. -/
noncomputable def smallPullbackSndOver {Z Z' : Over S} (f : Z ⟶ Z')
    (V : smallEtaleSite (ofOver Z')) : ofOverSmallEtalePullbackOver f V ⟶ V.left :=
  Over.homMk (pullback.snd f.left (overHomOf V.hom).left) sorry

/-- The Yoneda map from the scheme pullback to the functor-of-points pullback. -/
noncomputable def smallPullbackToSpace {Z Z' : Over S} (f : Z ⟶ Z')
    (V : smallEtaleSite (ofOver Z')) :
    ofOver (ofOverSmallEtalePullbackOver f V) ⟶ etaleBaseChangeSpace (ofOverMap f) V :=
  pullback.lift (f := homFunctor (ofOverMap f)) (g := homFunctor V.hom)
    (homFunctor (ofOverMap (ofOverSmallEtalePullbackHom f V)))
    (homFunctor (ofOverMap (smallPullbackSndOver f V))) sorry

/-- The inverse Yoneda comparison sends a compatible pair of points to its scheme pullback lift. -/
noncomputable def spacePullbackToSmall {Z Z' : Over S} (f : Z ⟶ Z')
    (V : smallEtaleSite (ofOver Z')) :
    etaleBaseChangeSpace (ofOverMap f) V ⟶ ofOver (ofOverSmallEtalePullbackOver f V) where
  app T := TypeCat.ofHom (fun x ↦
    (Over.homMk
      (pullback.lift (f := f.left) (g := (overHomOf V.hom).left)
        (((etaleBaseChangeFst (ofOverMap f) V).app T) x).left
        (((etaleBaseChangeSndNat (ofOverMap f) V).app T) x).left sorry) sorry :
      T.unop ⟶ ofOverSmallEtalePullbackOver f V))
  naturality := sorry

/-- The two actual fibre-product constructions agree over the source algebraic space. -/
noncomputable def smallPullbackSpaceIso {Z Z' : Over S} (f : Z ⟶ Z')
    (V : smallEtaleSite (ofOver Z')) :
    (smallEtaleInclusion (ofOver Z)).obj (ofOverSmallEtalePullbackObj f V) ≅
      (etaleBaseChange (ofOverMap f)).obj V :=
  MorphismProperty.Over.isoMk
    { hom := smallPullbackToSpace f V
      inv := spacePullbackToSmall f V
      hom_inv_id := sorry
      inv_hom_id := sorry } sorry

/-- Evaluate the right Kan extension on the represented fibre product, then apply its counit. -/
noncomputable def ofOverTypePushforwardComparison {Z Z' : Over S} (f : Z ⟶ Z')
    (G : Sheaf (smallEtaleTopology (ofOver Z)) (Type u)) :
    (typePushforward (ofOverMap f)).obj G ⟶
      ((ofOverSmallEtalePullback f).sheafPushforwardContinuous (Type u)
        (smallEtaleTopology (ofOver Z')) (smallEtaleTopology (ofOver Z))).obj G :=
  InducedCategory.homMk
    { app := fun V ↦
        EtaleTopos.extensionEvaluation (ofOver Z) G (smallPullbackSpaceIso f V.unop).hom
      naturality := sorry }

/-- Direct-image comparison of modules induced by the pullback projection and Kan counit. -/
noncomputable def ofOverPushforwardHom {Z Z' : Over S} (f : Z ⟶ Z')
    (G : (ofOver Z).Modules) :
    (Modules.pushforward (ofOverMap f)).obj G ⟶
      (ofOverRingedHom f).modulePushforward.{u}.obj G :=
  homOfUnderlying (structureSheaf (ofOver Z'))
    ((RingedSite.ToposHom.ModulePushforward.forgetIso (ringedToposHom (ofOverMap f))).hom.app G ≫
      ofOverTypePushforwardComparison f ((ToInternal.underlying (structureSheaf (ofOver Z))).obj G))
    sorry sorry

/-- Evaluation on a representable object of the fully faithful small étale inclusion is invertible. -/
theorem ofOverPushforwardHom_isIso {Z Z' : Over S} (f : Z ⟶ Z')
    (G : (ofOver Z).Modules) : IsIso (ofOverPushforwardHom f G) := sorry

/-- Inverse of the concrete direct-image comparison. -/
noncomputable def ofOverPushforwardInv {Z Z' : Over S} (f : Z ⟶ Z')
    (G : (ofOver Z).Modules) :
    (ofOverRingedHom f).modulePushforward.{u}.obj G ⟶
      (Modules.pushforward (ofOverMap f)).obj G :=
  (@asIso _ _ _ _ (ofOverPushforwardHom f G) (ofOverPushforwardHom_isIso f G)).inv

/-- Identification of `ofOverRingedHom` pullback with algebraic-space module pullback. -/
noncomputable def ofOverModulePullbackHom {Z Z' : Over S} (f : Z ⟶ Z')
    (F : (ofOver Z').Modules) :
    (ofOverRingedHom f).modulePullback.{u}.obj F ⟶
      (Modules.pullback (ofOverMap f)).obj F :=
  ((ofOverRingedHom f).modulePullbackHomEquiv.{u} F
      ((Modules.pullback (ofOverMap f)).obj F)).symm
    ((Modules.pullbackPushforwardAdjunction (ofOverMap f)).unit.app F ≫
      ofOverPushforwardHom f ((Modules.pullback (ofOverMap f)).obj F))

/-- Reverse identification of algebraic-space module pullback with `ofOverRingedHom`
pullback. -/
noncomputable def ofOverModulePullbackInv {Z Z' : Over S} (f : Z ⟶ Z')
    (F : (ofOver Z').Modules) :
    (Modules.pullback (ofOverMap f)).obj F ⟶
      (ofOverRingedHom f).modulePullback.{u}.obj F :=
  ((Modules.pullbackPushforwardAdjunction (ofOverMap f)).homEquiv F
      ((ofOverRingedHom f).modulePullback.{u}.obj F)).symm
    ((RingedSite.Hom.modulePullbackPushforwardAdjunction (ofOverRingedHom f)).unit.app F ≫
      ofOverPushforwardInv f ((ofOverRingedHom f).modulePullback.{u}.obj F))

/-- `restrictFunctor` of space-level pullback maps to `ofOverRingedHom` pullback of the
restricted module. -/
noncomputable def restrictFunctorPullbackHom {Z Z' : Over S} (f : Z ⟶ Z')
    (F : (ofOver Z').Modules) :
    (Modules.restrictFunctor (𝟙 (ofOver Z))).obj
        ((Modules.pullback (ofOverMap f)).obj F) ⟶
      (ofOverRingedHom f).modulePullback.{u}.obj
        ((Modules.restrictFunctor (𝟙 (ofOver Z'))).obj F) :=
  (SmallEtaleModuleGlueing.restrictFunctorId (ofOver Z)).hom.app
      ((Modules.pullback (ofOverMap f)).obj F) ≫
    ofOverModulePullbackInv f F ≫
      (ofOverRingedHom f).modulePullback.{u}.map
        ((SmallEtaleModuleGlueing.restrictFunctorId (ofOver Z')).inv.app F)

/-- Reverse of `restrictFunctorPullbackHom`. -/
noncomputable def restrictFunctorPullbackInv {Z Z' : Over S} (f : Z ⟶ Z')
    (F : (ofOver Z').Modules) :
    (ofOverRingedHom f).modulePullback.{u}.obj
        ((Modules.restrictFunctor (𝟙 (ofOver Z'))).obj F) ⟶
      (Modules.restrictFunctor (𝟙 (ofOver Z))).obj
        ((Modules.pullback (ofOverMap f)).obj F) :=
  (ofOverRingedHom f).modulePullback.{u}.map
      ((SmallEtaleModuleGlueing.restrictFunctorId (ofOver Z')).hom.app F) ≫
    ofOverModulePullbackHom f F ≫
      (SmallEtaleModuleGlueing.restrictFunctorId (ofOver Z)).inv.app
        ((Modules.pullback (ofOverMap f)).obj F)

/-- Both direct images evaluate the same module on the inverse-image open.
The underlying maps are literal identities; only scalar compatibility uses naturality
of the genuine restriction-of-sections ring isomorphism. -/
noncomputable def schemeOpensPushforwardIso {Z Z' : Over S} (f : Z ⟶ Z') :
    (schemeOpensRingedHom f.left).modulePushforward.{u} ⋙ opensToSchemeModules Z'.left ≅
      opensToSchemeModules Z.left ⋙ Scheme.Modules.pushforward f.left :=
  NatIso.ofComponents
    (fun M ↦
      { hom := homOfUnderlying Z'.left.ringCatSheaf
          (InducedCategory.homMk
            { app := fun W ↦ 𝟙 _
              naturality := sorry }) sorry sorry
        inv := homOfUnderlying Z'.left.ringCatSheaf
          (InducedCategory.homMk
            { app := fun W ↦ 𝟙 _
              naturality := sorry }) sorry sorry
        hom_inv_id := sorry
        inv_hom_id := sorry }) sorry

/-- The inverse-image comparison is the adjunction mate of direct-image coherence. -/
noncomputable def schemeOpensPullbackComparison {Z Z' : Over S} (f : Z ⟶ Z') :
    opensToSchemeModules Z'.left ⋙ Scheme.Modules.pullback f.left ⟶
      (schemeOpensRingedHom f.left).modulePullback.{u} ⋙ opensToSchemeModules Z.left :=
  ((mateEquiv
    (RingedSite.Hom.modulePullbackPushforwardAdjunction (schemeOpensRingedHom f.left))
    (Scheme.Modules.pullbackPushforwardAdjunction f.left)).symm
      (schemeOpensPushforwardIso f).hom).natTrans

/-- Scalar transport by the restriction-of-sections ring isomorphism preserves this mate. -/
theorem schemeOpensPullbackComparison_isIso {Z Z' : Over S} (f : Z ⟶ Z')
    (M : RingedSite.ModuleCat.{u}
      (RingedSite.ofRingSheaf (Opens.grothendieckTopology (Z'.left : TopCat))
        ⟨Scheme.Site.structurePresheaf (Z'.left.restrictFunctor ⋙ Over.forget Z'.left),
          opensStructurePresheaf_isSheaf Z'.left⟩)) :
    IsIso ((schemeOpensPullbackComparison f).app M) := sorry

/-- Interchange of open-site pullback and scalar transport, inverse to the actual mate. -/
noncomputable def schemeOpensModulesPullbackHom {Z Z' : Over S} (f : Z ⟶ Z')
    (M : RingedSite.ModuleCat.{u}
      (RingedSite.ofRingSheaf (Opens.grothendieckTopology (Z'.left : TopCat))
        ⟨Scheme.Site.structurePresheaf (Z'.left.restrictFunctor ⋙ Over.forget Z'.left),
          opensStructurePresheaf_isSheaf Z'.left⟩)) :
    (opensToSchemeModules Z.left).obj ((schemeOpensRingedHom f.left).modulePullback.{u}.obj M) ⟶
      (Scheme.Modules.pullback f.left).obj ((opensToSchemeModules Z'.left).obj M) :=
  (@asIso _ _ _ _ ((schemeOpensPullbackComparison f).app M)
    (schemeOpensPullbackComparison_isIso f M)).inv

/-- The reverse interchange is the actual adjunction mate itself. -/
noncomputable def schemeOpensModulesPullbackInv {Z Z' : Over S} (f : Z ⟶ Z')
    (M : RingedSite.ModuleCat.{u}
      (RingedSite.ofRingSheaf (Opens.grothendieckTopology (Z'.left : TopCat))
        ⟨Scheme.Site.structurePresheaf (Z'.left.restrictFunctor ⋙ Over.forget Z'.left),
          opensStructurePresheaf_isSheaf Z'.left⟩)) :
    (Scheme.Modules.pullback f.left).obj ((opensToSchemeModules Z'.left).obj M) ⟶
      (opensToSchemeModules Z.left).obj ((schemeOpensRingedHom f.left).modulePullback.{u}.obj M) :=
  (schemeOpensPullbackComparison f).app M

/-- For a quasi-coherent source module, the actual restriction-square mate is invertible. -/
theorem restrictPullbackOpensComparison_isIso {Z Z' : Over S} (f : Z ⟶ Z')
    (F : (ofOver Z').Modules) [F.IsQuasicoherent] :
    IsIso
      ((restrictPullbackOpensComparison f).app
        ((Modules.restrictFunctor (𝟙 (ofOver Z'))).obj F)) :=
  sorry

/-- Interchange of `restrictToOpensHom` pushforward with scheme-level pullback, assembled from
the ringed-site mate and the algebraic-space/scheme pullback identifications. -/
noncomputable def restrictPullbackOpensHom {Z Z' : Over S} (f : Z ⟶ Z')
    (F : (ofOver Z').Modules) [F.IsQuasicoherent] :
    (opensToSchemeModules Z.left).obj
        ((restrictToOpensHom Z).modulePushforward.{u}.obj
          ((Modules.restrictFunctor (𝟙 (ofOver Z))).obj
            ((Modules.pullback (ofOverMap f)).obj F))) ⟶
      (Scheme.Modules.pullback f.left).obj
        ((opensToSchemeModules Z'.left).obj
          ((restrictToOpensHom Z').modulePushforward.{u}.obj
            ((Modules.restrictFunctor (𝟙 (ofOver Z'))).obj F))) :=
  (opensToSchemeModules Z.left).map
      ((restrictToOpensHom Z).modulePushforward.{u}.map (restrictFunctorPullbackHom f F)) ≫
    (opensToSchemeModules Z.left).map
      (@asIso _ _ _ _
        ((restrictPullbackOpensComparison f).app
          ((Modules.restrictFunctor (𝟙 (ofOver Z'))).obj F))
        (restrictPullbackOpensComparison_isIso f F)).inv ≫
    schemeOpensModulesPullbackHom f
      ((restrictToOpensHom Z').modulePushforward.{u}.obj
        ((Modules.restrictFunctor (𝟙 (ofOver Z'))).obj F))

/-- Reverse interchange of `restrictToOpensHom` pushforward with scheme-level pullback. -/
noncomputable def restrictPullbackOpensInv {Z Z' : Over S} (f : Z ⟶ Z')
    (F : (ofOver Z').Modules) [F.IsQuasicoherent] :
    (Scheme.Modules.pullback f.left).obj
        ((opensToSchemeModules Z'.left).obj
          ((restrictToOpensHom Z').modulePushforward.{u}.obj
            ((Modules.restrictFunctor (𝟙 (ofOver Z'))).obj F))) ⟶
      (opensToSchemeModules Z.left).obj
        ((restrictToOpensHom Z).modulePushforward.{u}.obj
          ((Modules.restrictFunctor (𝟙 (ofOver Z))).obj
            ((Modules.pullback (ofOverMap f)).obj F))) :=
  schemeOpensModulesPullbackInv f
      ((restrictToOpensHom Z').modulePushforward.{u}.obj
        ((Modules.restrictFunctor (𝟙 (ofOver Z'))).obj F)) ≫
    (opensToSchemeModules Z.left).map
      ((restrictPullbackOpensComparison f).app
        ((Modules.restrictFunctor (𝟙 (ofOver Z'))).obj F)) ≫
    (opensToSchemeModules Z.left).map
      ((restrictToOpensHom Z).modulePushforward.{u}.map (restrictFunctorPullbackInv f F))

/-- Restriction of modules to the underlying scheme, after pullback along `ofOverMap f`,
identifies with restriction followed by scheme-level module pullback. -/
noncomputable def restrictPullbackIso {Z Z' : Over S} (f : Z ⟶ Z')
    (F : (ofOver Z').Modules) [F.IsQuasicoherent] :
    (Modules.restrictToScheme Z).obj ((Modules.pullback (ofOverMap f)).obj F) ≅
      (Scheme.Modules.pullback f.left).obj ((Modules.restrictToScheme Z').obj F) where
  hom :=
    (restrictToSchemeOpensIso ((Modules.pullback (ofOverMap f)).obj F)).hom ≫
      restrictPullbackOpensHom f F ≫
        (Scheme.Modules.pullback f.left).map (restrictToSchemeOpensIso F).inv
  inv :=
    (Scheme.Modules.pullback f.left).map (restrictToSchemeOpensIso F).hom ≫
      restrictPullbackOpensInv f F ≫
        (restrictToSchemeOpensIso ((Modules.pullback (ofOverMap f)).obj F)).inv
  hom_inv_id := sorry
  inv_hom_id := sorry

/-- Scheme-level coborder comparison from the kernel-cotangent pullback to the conormal
sheaf of the original immersion. -/
noncomputable def schemeCoborderConormalHom {Z X : Over S} (i : Z ⟶ X)
    [AlgebraicGeometry.IsImmersion i.left] :
    (Scheme.Modules.pullback i.left.liftCoborder).obj
        (Scheme.Hom.Conormal.idealCotangentSheaf i.left.liftCoborder) ⟶
      Scheme.Hom.conormalSheaf i.left :=
  Scheme.Hom.Conormal.idealCotangentPullbackComparison i.left.liftCoborder ≫
    Scheme.Hom.Conormal.factorizationConormalComparisonInv i.left i.left.liftCoborder
      i.left.coborderRange.ι i.left.liftCoborder_ι

/-- Reverse scheme-level coborder comparison. -/
noncomputable def schemeCoborderConormalInv {Z X : Over S} (i : Z ⟶ X)
    [AlgebraicGeometry.IsImmersion i.left] :
    Scheme.Hom.conormalSheaf i.left ⟶
      (Scheme.Modules.pullback i.left.liftCoborder).obj
        (Scheme.Hom.Conormal.idealCotangentSheaf i.left.liftCoborder) :=
  Scheme.Hom.Conormal.factorizationConormalComparison i.left i.left.liftCoborder
      i.left.coborderRange.ι i.left.liftCoborder_ι ≫
    idealCotangentPullbackComparisonInv i.left.liftCoborder

/-- Cokernel comparison after `restrictToScheme`, obtained by descending the image of the
cokernel projection. -/
noncomputable def restrictToSchemeCokernelInv {U : Over S} {A B : (ofOver U).Modules}
    (g : A ⟶ B) :
    cokernel ((Modules.restrictToScheme U).map g) ⟶
      (Modules.restrictToScheme U).obj (cokernel g) :=
  cokernel.desc ((Modules.restrictToScheme U).map g)
    ((Modules.restrictToScheme U).map (cokernel.π g)) sorry

/-- Restriction preserves the ideal-action cokernel of a closed immersion: both
the ideal and its square are quasi-coherent. No assertion is made for arbitrary module cokernels. -/
instance restrictToSchemeIdealCokernelInv_isIso {Z X : Over S} (i : Z ⟶ X)
    [AlgebraicGeometry.IsImmersion i.left] :
    IsIso (restrictToSchemeCokernelInv
      (Modules.idealAction (Hom.idealSheafSubobject (ofOverMap (schemeLiftCoborderOver i)))
        (Hom.idealSheaf (ofOverMap (schemeLiftCoborderOver i))))) := sorry

/-- Forward cokernel comparison when the actual comparison morphism is invertible. -/
noncomputable def restrictToSchemeCokernelHom {U : Over S} {A B : (ofOver U).Modules}
    (g : A ⟶ B) [IsIso (restrictToSchemeCokernelInv g)] :
    (Modules.restrictToScheme U).obj (cokernel g) ⟶
      cokernel ((Modules.restrictToScheme U).map g) :=
  inv (restrictToSchemeCokernelInv g)

/-- The canonical structure-algebra map presenting the scheme coborder kernel ideal. -/
noncomputable abbrev schemeCoborderUnitToPushforward {Z X : Over S} (i : Z ⟶ X)
    [AlgebraicGeometry.IsImmersion i.left] :=
  SheafOfModules.RingedSite.KernelIdeal.map
    (RingedSpace.Hom.commRingSheafPushforwardMap i.left.liftCoborder.toShHom)

/-- The scheme unit maps to the restricted space unit through the actual coefficient maps. -/
noncomputable def schemeUnitToRestrictedUnit (U : Over S) :
    SheafOfModules.unit U.left.ringCatSheaf ⟶
      (Modules.restrictToScheme U).obj (SheafOfModules.unit (structureSheaf (ofOver U))) :=
  SheafOfModules.unitToPushforwardObjUnit
      (SheafOfModules.ChangeOfRings.homOverId (opensStructureToRingCatSheaf U.left)) ≫
    (SheafOfModules.ChangeOfRings.pushforwardIso
      (opensStructureToRingCatSheaf U.left)).hom.app _ ≫
    (opensToSchemeModules U.left).map
      (SheafOfModules.unitToPushforwardObjUnit (restrictToOpensHom U).structureSheafMap) ≫
    (opensToSchemeModules U.left).map
      ((restrictToOpensHom U).modulePushforward.map
        ((SmallEtaleModuleGlueing.restrictFunctorId (ofOver U)).inv.app
          (SheafOfModules.unit (structureSheaf (ofOver U))))) ≫
    (restrictToSchemeOpensIso (SheafOfModules.unit (structureSheaf (ofOver U)))).inv

/-- On a scheme the coefficient comparison identifies the two structure modules. -/
theorem schemeUnitToRestrictedUnit_isIso (U : Over S) :
    IsIso (schemeUnitToRestrictedUnit U) := sorry

/-- Restriction of the space unit to the coborder scheme, inverse to its coefficient map. -/
noncomputable def restrictToSchemeUnitHom {Z X : Over S} (i : Z ⟶ X)
    [AlgebraicGeometry.IsImmersion i.left] :
    (Modules.restrictToScheme (schemeCoborder i)).obj
        (SheafOfModules.unit (structureSheaf (ofOver (schemeCoborder i)))) ⟶
      SheafOfModules.unit (schemeCoborder i).left.ringCatSheaf :=
  (@asIso _ _ _ _ (schemeUnitToRestrictedUnit (schemeCoborder i))
    (schemeUnitToRestrictedUnit_isIso (schemeCoborder i))).inv

/-- The categorical kernel and its chosen kernel-subobject representative agree canonically. -/
noncomputable def schemeCoborderKernelIso {Z X : Over S} (i : Z ⟶ X)
    [AlgebraicGeometry.IsImmersion i.left] :
    kernel (schemeCoborderUnitToPushforward i) ≅
      RingedSpace.Hom.kernelIdealSheaf i.left.liftCoborder.toShHom :=
  (kernelSubobjectIso (schemeCoborderUnitToPushforward i)).symm

/-- The restricted coborder kernel action followed by the scheme structure map vanishes. -/
theorem restrictedClosedIdeal_comp_unit {Z X : Over S} (i : Z ⟶ X)
    [AlgebraicGeometry.IsImmersion i.left] :
    (Modules.restrictToScheme (schemeCoborder i)).map
          (Hom.idealSheafι (ofOverMap (schemeLiftCoborderOver i))) ≫
        restrictToSchemeUnitHom i ≫ schemeCoborderUnitToPushforward i =
      0 :=
  sorry

/-- Comparison of the restricted coborder kernel ideal with the scheme kernel ideal. -/
noncomputable def restrictedClosedIdealHom {Z X : Over S} (i : Z ⟶ X)
    [AlgebraicGeometry.IsImmersion i.left] :
    (Modules.restrictToScheme (schemeCoborder i)).obj
        (Hom.idealSheaf (ofOverMap (schemeLiftCoborderOver i))) ⟶
      kernel (schemeCoborderUnitToPushforward i) :=
  kernel.lift (schemeCoborderUnitToPushforward i)
    ((Modules.restrictToScheme (schemeCoborder i)).map
        (Hom.idealSheafι (ofOverMap (schemeLiftCoborderOver i))) ≫
      restrictToSchemeUnitHom i)
    (restrictedClosedIdeal_comp_unit i)

/-- The restricted coborder ideal action followed by the kernel-cotangent map vanishes. -/
theorem restrictedClosedIdealAction_comp_cotangent {Z X : Over S} (i : Z ⟶ X)
    [AlgebraicGeometry.IsImmersion i.left] :
    (Modules.restrictToScheme (schemeCoborder i)).map
          (Modules.idealAction
            (Hom.idealSheafSubobject (ofOverMap (schemeLiftCoborderOver i)))
            (Hom.idealSheaf (ofOverMap (schemeLiftCoborderOver i)))) ≫
        restrictedClosedIdealHom i ≫
          (schemeCoborderKernelIso i).hom ≫
            Scheme.Hom.Conormal.idealToCotangent i.left.liftCoborder =
      0 :=
  sorry

/-- Comparison of the restricted coborder `I / I²` with the scheme kernel-cotangent sheaf,
using the `restrictToScheme` module-pushforward composite. -/
noncomputable def restrictedClosedIdealQuotientHom {Z X : Over S} (i : Z ⟶ X)
    [AlgebraicGeometry.IsImmersion i.left] :
    (Modules.restrictToScheme (schemeCoborder i)).obj (closedIdealQuotient i) ⟶
      Scheme.Hom.Conormal.idealCotangentSheaf i.left.liftCoborder :=
  restrictToSchemeCokernelHom
      (Modules.idealAction
        (Hom.idealSheafSubobject (ofOverMap (schemeLiftCoborderOver i)))
        (Hom.idealSheaf (ofOverMap (schemeLiftCoborderOver i)))) ≫
    cokernel.desc
      ((Modules.restrictToScheme (schemeCoborder i)).map
        (Modules.idealAction
          (Hom.idealSheafSubobject (ofOverMap (schemeLiftCoborderOver i)))
          (Hom.idealSheaf (ofOverMap (schemeLiftCoborderOver i)))))
      (restrictedClosedIdealHom i ≫
        (schemeCoborderKernelIso i).hom ≫
          Scheme.Hom.Conormal.idealToCotangent i.left.liftCoborder)
      (restrictedClosedIdealAction_comp_cotangent i)

/-- The restricted coborder `I / I²` comparison is an isomorphism. -/
theorem restrictedClosedIdealQuotientHom_isIso {Z X : Over S} (i : Z ⟶ X)
    [AlgebraicGeometry.IsImmersion i.left] :
    IsIso (restrictedClosedIdealQuotientHom i) :=
  sorry

/-- Reverse comparison of the scheme kernel-cotangent sheaf with the restricted coborder
`I / I²`. -/
noncomputable def restrictedClosedIdealQuotientInv {Z X : Over S} (i : Z ⟶ X)
    [AlgebraicGeometry.IsImmersion i.left] :
    Scheme.Hom.Conormal.idealCotangentSheaf i.left.liftCoborder ⟶
      (Modules.restrictToScheme (schemeCoborder i)).obj (closedIdealQuotient i) :=
  (@asIso _ _ _ _
      (restrictedClosedIdealQuotientHom i)
      (restrictedClosedIdealQuotientHom_isIso i)).inv

/-- Forward comparison from the restricted `j^* (I / I²)` to the scheme kernel-cotangent
pullback. -/
noncomputable def restrictedClosedConormalHom {Z X : Over S} (i : Z ⟶ X)
    [AlgebraicGeometry.IsImmersion i.left] :
    (Modules.restrictToScheme Z).obj (closedConormalPullback i) ⟶
      (Scheme.Modules.pullback i.left.liftCoborder).obj
        (Scheme.Hom.Conormal.idealCotangentSheaf i.left.liftCoborder) :=
  (restrictPullbackIso (schemeLiftCoborderOver i) (closedIdealQuotient i)).hom ≫
    (Scheme.Modules.pullback i.left.liftCoborder).map (restrictedClosedIdealQuotientHom i)

/-- Reverse comparison from the scheme kernel-cotangent pullback to the restricted
`j^* (I / I²)`. -/
noncomputable def restrictedClosedConormalInv {Z X : Over S} (i : Z ⟶ X)
    [AlgebraicGeometry.IsImmersion i.left] :
    (Scheme.Modules.pullback i.left.liftCoborder).obj
        (Scheme.Hom.Conormal.idealCotangentSheaf i.left.liftCoborder) ⟶
      (Modules.restrictToScheme Z).obj (closedConormalPullback i) :=
  (Scheme.Modules.pullback i.left.liftCoborder).map (restrictedClosedIdealQuotientInv i) ≫
    (restrictPullbackIso (schemeLiftCoborderOver i) (closedIdealQuotient i)).inv

/-- Forward comparison from the restricted algebraic-space conormal sheaf to
`Scheme.Hom.conormalSheaf`, as the coborder `I / I²` composite of `factorizationMap`,
`closedUnfold`, the restrict/pullback identification, and
`factorizationConormalComparisonInv`. -/
noncomputable def restrictToSchemeIsoHom {Z X : Over S} (i : Z ⟶ X)
    [AlgebraicGeometry.IsImmersion i.left] :
    (Modules.restrictToScheme Z).obj (Hom.conormalSheaf (ofOverMap i)) ⟶
      Scheme.Hom.conormalSheaf i.left :=
  (Modules.restrictToScheme Z).map (factorizationMap i) ≫
    (Modules.restrictToScheme Z).map (closedUnfold i) ≫
    restrictedClosedConormalHom i ≫
    schemeCoborderConormalHom i

/-- Reverse comparison from `Scheme.Hom.conormalSheaf` to the restricted algebraic-space
conormal sheaf. -/
noncomputable def restrictToSchemeIsoInv {Z X : Over S} (i : Z ⟶ X)
    [AlgebraicGeometry.IsImmersion i.left] :
    Scheme.Hom.conormalSheaf i.left ⟶
      (Modules.restrictToScheme Z).obj (Hom.conormalSheaf (ofOverMap i)) :=
  schemeCoborderConormalInv i ≫
    restrictedClosedConormalInv i ≫
    (Modules.restrictToScheme Z).map (closedUnfoldInv i) ≫
    (Modules.restrictToScheme Z).map (factorizationMapInv i)

/-- Restriction of the algebraic-space conormal sheaf of an immersion of schemes over `S`
identifies with `Scheme.Hom.conormalSheaf`. -/
noncomputable def restrictToSchemeIso {Z X : Over S} (i : Z ⟶ X)
    [AlgebraicGeometry.IsImmersion i.left] :
    (Modules.restrictToScheme Z).obj (Hom.conormalSheaf (ofOverMap i)) ≅
      Scheme.Hom.conormalSheaf i.left where
  hom := restrictToSchemeIsoHom i
  inv := restrictToSchemeIsoInv i
  hom_inv_id := sorry
  inv_hom_id := sorry

/-- The forward component of `restrictToSchemeIso` is the constructed coborder comparison. -/
theorem restrictToSchemeIso_hom {Z X : Over S} (i : Z ⟶ X)
    [AlgebraicGeometry.IsImmersion i.left] :
    (restrictToSchemeIso i).hom = restrictToSchemeIsoHom i :=
  rfl

/-- The inverse component of `restrictToSchemeIso` is the constructed reverse coborder
comparison. -/
theorem restrictToSchemeIso_inv {Z X : Over S} (i : Z ⟶ X)
    [AlgebraicGeometry.IsImmersion i.left] :
    (restrictToSchemeIso i).inv = restrictToSchemeIsoInv i :=
  rfl

/-- The restriction identification is the constructed coborder composite in both directions. -/
theorem restrictToSchemeIso_spec {Z X : Over S} (i : Z ⟶ X)
    [AlgebraicGeometry.IsImmersion i.left] :
    (restrictToSchemeIso i).hom = restrictToSchemeIsoHom i ∧
      (restrictToSchemeIso i).inv = restrictToSchemeIsoInv i :=
  ⟨rfl, rfl⟩

/-- Pullback of an algebraic-space conormal sheaf, then restriction to the underlying
scheme, identifies with restriction followed by scheme-level module pullback. -/
noncomputable def pullbackRestrictIso {Z Z' X' : Over S} (f : Z ⟶ Z') (i' : Z' ⟶ X')
    [AlgebraicGeometry.IsImmersion i'.left] :
    (Modules.restrictToScheme Z).obj
        ((Modules.pullback (ofOverMap f)).obj (Hom.conormalSheaf (ofOverMap i'))) ≅
      (Scheme.Modules.pullback f.left).obj (Scheme.Hom.conormalSheaf i'.left) :=
  restrictPullbackIso f (Hom.conormalSheaf (ofOverMap i')) ≪≫
    (Scheme.Modules.pullback f.left).mapIso (restrictToSchemeIso i')

/-- The pullback-restriction comparison is the restrict/pullback interchange followed by
`restrictToSchemeIso`. -/
theorem pullbackRestrictIso_spec {Z Z' X' : Over S} (f : Z ⟶ Z') (i' : Z' ⟶ X')
    [AlgebraicGeometry.IsImmersion i'.left] :
    pullbackRestrictIso f i' =
      restrictPullbackIso f (Hom.conormalSheaf (ofOverMap i')) ≪≫
        (Scheme.Modules.pullback f.left).mapIso (restrictToSchemeIso i') :=
  rfl

/-- On a commutative square of immersions of schemes over `S`, `Hom.Conormal.map` agrees
with `Scheme.Hom.Conormal.map` after the restriction and pullback-restriction
comparisons. -/
theorem map_restrictToScheme {Z X Z' X' : Over S} {f : Z ⟶ Z'} {i : Z ⟶ X} {i' : Z' ⟶ X'}
    {g : X ⟶ X'} [AlgebraicGeometry.IsImmersion i.left]
    [AlgebraicGeometry.IsImmersion i'.left] (sq : CommSq f i i' g) :
    (pullbackRestrictIso f i').hom ≫ Scheme.Hom.Conormal.map (ofOverSqLeft sq) =
      (Modules.restrictToScheme Z).map (Hom.Conormal.map (ofOverCommSq sq)) ≫
        (restrictToSchemeIso i).hom :=
  sorry

/-- For a vertically stacked pair of commutative squares of algebraic spaces whose
horizontal arrows are immersions, `Hom.Conormal.map` of the composite square is the
composite of `Hom.Conormal.map` of the lower square with the pullback of
`Hom.Conormal.map` of the upper square. -/
theorem map_comp {Z X Z' X' Z'' X'' : AlgebraicSpace S} {f : Z ⟶ Z'} {f' : Z' ⟶ Z''}
    {i : Z ⟶ X} {i' : Z' ⟶ X'} {i'' : Z'' ⟶ X''} {g : X ⟶ X'} {g' : X' ⟶ X''}
    [IsImmersion i] [IsImmersion i'] [IsImmersion i''] (sq : CommSq f i i' g)
    (sq' : CommSq f' i' i'' g') :
    Hom.Conormal.map (sq.horiz_comp sq') =
      (Modules.pullbackComp f f').inv.app (Hom.conormalSheaf i'') ≫
        (Modules.pullback f).map (Hom.Conormal.map sq') ≫ Hom.Conormal.map sq :=
  sorry

end Hom.Conormal

end AlgebraicGeometry.AlgebraicSpace
