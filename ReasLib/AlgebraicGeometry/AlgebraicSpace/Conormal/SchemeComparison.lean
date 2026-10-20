/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Immersion
public import Mathlib.CategoryTheory.Abelian.Basic
public import ReasLib.AlgebraicGeometry.Scheme.Module.Conormal
public import ReasLib.AlgebraicGeometry.Scheme.Module.Conormal.ClosedImmersion
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Conormal.Functorial
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Glueing
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Pullback.Sections
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.RestrictToScheme.Structure
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.RestrictToScheme.Pullback

/-! # Comparison of scheme and algebraic-space conormal sheaves

Restriction identifies the conormal sheaf of an immersion of schemes with the
scheme conormal sheaf and intertwines their canonical functorial maps.
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
abbrev schemeCoborder {Z X : Over S} (i : Z ⟶ X)
    [AlgebraicGeometry.IsImmersion i.left] : Over S :=
  { left := i.left.coborderRange.toScheme
    right := ⟨⟨⟩⟩
    hom := i.left.coborderRange.ι ≫ X.hom }

/-- Compatibility of the scheme coborder closed immersion with the structure morphisms
over `S`. -/
theorem schemeLiftCoborderOver_w {Z X : Over S} (i : Z ⟶ X)
    [AlgebraicGeometry.IsImmersion i.left] :
    i.left.liftCoborder ≫ (schemeCoborder i).hom = Z.hom :=
  sorry

/-- The coborder closed immersion of an immersion of schemes over `S`, as a morphism
in `Over S`. -/
abbrev schemeLiftCoborderOver {Z X : Over S} (i : Z ⟶ X)
    [AlgebraicGeometry.IsImmersion i.left] :
    Z ⟶ schemeCoborder i :=
  { left := i.left.liftCoborder
    right := 𝟙 _
    w := by
      change i.left.liftCoborder ≫ (schemeCoborder i).hom = Z.hom ≫ 𝟙 S
      exact (schemeLiftCoborderOver_w i).trans (Category.comp_id Z.hom).symm }

/-- The underlying scheme morphism of `schemeLiftCoborderOver i` is the coborder closed
immersion. -/
theorem instIsImmersion_schemeLiftCoborderOver_left {Z X : Over S} (i : Z ⟶ X)
    [AlgebraicGeometry.IsImmersion i.left] :
    AlgebraicGeometry.IsImmersion (schemeLiftCoborderOver i).left :=
  inferInstanceAs (AlgebraicGeometry.IsImmersion i.left.liftCoborder)

/-- An immersion of schemes over `S` remains an immersion after passing to the coborder
closed immersion as an algebraic-space morphism. -/
theorem instIsImmersion_ofOverMap_schemeLiftCoborderOver {Z X : Over S} (i : Z ⟶ X)
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
theorem instIsIso_idealQuotientMap_restrictedFactorizationSq {Z X : Over S} (i : Z ⟶ X)
    [AlgebraicGeometry.IsImmersion i.left] :
    IsIso (idealQuotientMap (restrictedSq (ofOverCommSq (schemeFactorizationSq i)))) :=
  sorry

/-- Reverse of `Hom.Conormal.map`, obtained by reversing each comparison in the coborder
compatible-open composite. -/
noncomputable def mapInv {Z X Z' X' : AlgebraicSpace S} {f : Z ⟶ Z'} {i : Z ⟶ X}
    {i' : Z' ⟶ X'} {g : X ⟶ X'} [IsImmersion i] [IsImmersion i'] (sq : CommSq f i i' g)
    [hIso : IsIso (idealQuotientMap (restrictedSq sq))] :
    Hom.conormalSheaf i ⟶ (Modules.pullback f).obj (Hom.conormalSheaf i') :=
  (eqToIso (congrArg Modules.pullback (liftToCompatibleOpen_comp_toCoborder sq))).inv.app
      (Modules.quotientByIdeal (Hom.idealSheafSubobject (IsImmersion.liftCoborder i))
        (Hom.idealSheaf (IsImmersion.liftCoborder i))) ≫
    (Modules.pullbackCompIso (liftToCompatibleOpen sq)
        (compatibleOpenToCoborder i i' g)).inv.app
      (Modules.quotientByIdeal (Hom.idealSheafSubobject (IsImmersion.liftCoborder i))
        (Hom.idealSheaf (IsImmersion.liftCoborder i))) ≫
    (Modules.pullback (liftToCompatibleOpen sq)).map (compatibleOpenQuotientMap sq) ≫
    (Modules.pullback (liftToCompatibleOpen sq)).map
      (inv (idealQuotientMap (restrictedSq sq))) ≫
    (Modules.pullbackCompIso (liftToCompatibleOpen sq)
        (restrictToCompatibleOpen i i' g)).hom.app
      (Modules.quotientByIdeal (Hom.idealSheafSubobject (IsImmersion.liftCoborder i'))
        (Hom.idealSheaf (IsImmersion.liftCoborder i'))) ≫
    (eqToIso (congrArg Modules.pullback (restrictedSq sq).w)).inv.app
      (Modules.quotientByIdeal (Hom.idealSheafSubobject (IsImmersion.liftCoborder i'))
        (Hom.idealSheaf (IsImmersion.liftCoborder i'))) ≫
    (Modules.pullbackCompIso f (IsImmersion.liftCoborder i')).inv.app
      (Modules.quotientByIdeal (Hom.idealSheafSubobject (IsImmersion.liftCoborder i'))
        (Hom.idealSheaf (IsImmersion.liftCoborder i')))

/-- Reverse space-level comparison of conormal sheaves along the coborder factorization. -/
noncomputable def factorizationMapInv {Z X : Over S} (i : Z ⟶ X)
    [AlgebraicGeometry.IsImmersion i.left] :
    Hom.conormalSheaf (ofOverMap (schemeLiftCoborderOver i)) ⟶
      Hom.conormalSheaf (ofOverMap i) :=
  mapInv (ofOverCommSq (schemeFactorizationSq i))
      (hIso := instIsIso_idealQuotientMap_restrictedFactorizationSq i) ≫
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
theorem closedIdealQuotient_isQuasicoherent {Z X : Over S} (i : Z ⟶ X)
    [AlgebraicGeometry.IsImmersion i.left] :
    (closedIdealQuotient i).IsQuasicoherent := sorry

/-- The closed-immersion formula `j^* (I / I²)` for the coborder closed immersion of `i`. -/
noncomputable def closedConormalPullback {Z X : Over S} (i : Z ⟶ X)
    [AlgebraicGeometry.IsImmersion i.left] :
    (ofOver Z).Modules :=
  (Modules.pullback (ofOverMap (schemeLiftCoborderOver i))).obj (closedIdealQuotient i)

/-- The pulled coborder kernel of `ofOverMap j` vanishes after mapping to `j_* 𝒪_Z`. -/
private theorem closedPulledIdeal_vanishes {Z X : Over S} (i : Z ⟶ X)
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
      (by exact closedPulledIdeal_vanishes i) ≫
    (Hom.idealSheaf_spec (IsImmersion.liftCoborder (ofOverMap (schemeLiftCoborderOver i)))).inv

/-- The pulled ideal-sheaf action followed by `closedPulledIdealToIdeal ≫ π` is zero. -/
private theorem closedPulledIdealAction_comp_π {Z X : Over S} (i : Z ⟶ X)
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
      (by exact closedPulledIdealAction_comp_π i)

/-- The pulled inclusion of the closed-immersion kernel along the coborder open is a
monomorphism. -/
theorem instMono_closedPulledIdealι {Z X : Over S} (i : Z ⟶ X)
    [AlgebraicGeometry.IsImmersion i.left] :
    Mono
      ((Modules.pullback
            (IsImmersion.coborderRange (ofOverMap (schemeLiftCoborderOver i))).ι).map
        (Hom.idealSheafι (ofOverMap (schemeLiftCoborderOver i)))) :=
  sorry

/-- The coborder kernel inclusion vanishes on the cokernel of the pulled closed-immersion
kernel inclusion. -/
private theorem closedIdealToPulledIdeal_comp_π {Z X : Over S} (i : Z ⟶ X)
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
  @CategoryTheory.Abelian.monoLift _ _ _ _ _
    ((Modules.pullback
          (IsImmersion.coborderRange (ofOverMap (schemeLiftCoborderOver i))).ι).map
      (Hom.idealSheafι (ofOverMap (schemeLiftCoborderOver i))))
    (instMono_closedPulledIdealι i) _
    (Hom.idealSheafι (IsImmersion.liftCoborder (ofOverMap (schemeLiftCoborderOver i))) ≫
      Modules.structureModulePullbackInv
        (IsImmersion.coborderRange (ofOverMap (schemeLiftCoborderOver i))).ι)
    (by exact closedIdealToPulledIdeal_comp_π i)

/-- The coborder ideal-sheaf action followed by the reverse kernel comparison and the
pulled quotient projection is zero. -/
private theorem closedRestrictQuotientInv_comp_π {Z X : Over S} (i : Z ⟶ X)
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
      (by exact closedRestrictQuotientInv_comp_π i)

/-- Forward unfolding of the space conormal of the coborder closed immersion to
`j^* (I / I²)`. -/
noncomputable def closedUnfold {Z X : Over S} (i : Z ⟶ X)
    [AlgebraicGeometry.IsImmersion i.left] :
    Hom.conormalSheaf (ofOverMap (schemeLiftCoborderOver i)) ⟶ closedConormalPullback i :=
  (Modules.pullback
        (IsImmersion.liftCoborder (ofOverMap (schemeLiftCoborderOver i)))).map
      (closedRestrictQuotientInv i) ≫
    (Modules.pullbackCompIso
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
    (Modules.pullbackCompIso
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

/-- Restriction preserves the ideal-action cokernel of a closed immersion: both
the ideal and its square are quasi-coherent. No assertion is made for arbitrary module cokernels. -/
theorem restrictToSchemeIdealCokernelComparison_isIso {Z X : Over S} (i : Z ⟶ X)
    [AlgebraicGeometry.IsImmersion i.left] :
    IsIso (@cokernelComparison _ _ _ _ _
      (Modules.idealAction (Hom.idealSheafSubobject (ofOverMap (schemeLiftCoborderOver i)))
        (Hom.idealSheaf (ofOverMap (schemeLiftCoborderOver i)))) _ _ _
      (Modules.restrictToScheme (schemeCoborder i))
      (Modules.RestrictToScheme.preservesZeroMorphisms (schemeCoborder i)) _ _) := sorry

/-- The canonical structure-algebra map presenting the scheme coborder kernel ideal. -/
noncomputable abbrev schemeCoborderUnitToPushforward {Z X : Over S} (i : Z ⟶ X)
    [AlgebraicGeometry.IsImmersion i.left] :=
  SheafOfModules.RingedSite.KernelIdeal.map
    (RingedSpace.Hom.commRingSheafPushforwardMap i.left.liftCoborder.toShHom)

/-- Restriction of the space unit to the coborder scheme, inverse to its coefficient map. -/
noncomputable def restrictToSchemeUnitHom {Z X : Over S} (i : Z ⟶ X)
    [AlgebraicGeometry.IsImmersion i.left] :
    (Modules.restrictToScheme (schemeCoborder i)).obj
        (SheafOfModules.unit (structureSheaf (ofOver (schemeCoborder i)))) ⟶
      SheafOfModules.unit (schemeCoborder i).left.ringCatSheaf :=
  (@asIso _ _ _ _ (Modules.RestrictToScheme.unitMap (schemeCoborder i))
    (by exact Modules.RestrictToScheme.unitMap_isIso (schemeCoborder i))).inv

/-- The categorical kernel and its chosen kernel-subobject representative agree canonically. -/
noncomputable def schemeCoborderKernelIso {Z X : Over S} (i : Z ⟶ X)
    [AlgebraicGeometry.IsImmersion i.left] :
    kernel (schemeCoborderUnitToPushforward i) ≅
      RingedSpace.Hom.kernelIdealSheaf i.left.liftCoborder.toShHom :=
  (kernelSubobjectIso (schemeCoborderUnitToPushforward i)).symm

/-- The restricted coborder kernel action followed by the scheme structure map vanishes. -/
private theorem restrictedClosedIdeal_comp_unit {Z X : Over S} (i : Z ⟶ X)
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
    (by exact restrictedClosedIdeal_comp_unit i)

/-- The restricted coborder ideal action followed by the kernel-cotangent map vanishes. -/
private theorem restrictedClosedIdealAction_comp_cotangent {Z X : Over S} (i : Z ⟶ X)
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
  (@asIso _ _ _ _ (@cokernelComparison _ _ _ _ _
      (Modules.idealAction
        (Hom.idealSheafSubobject (ofOverMap (schemeLiftCoborderOver i)))
        (Hom.idealSheaf (ofOverMap (schemeLiftCoborderOver i)))) _ _ _
      (Modules.restrictToScheme (schemeCoborder i))
      (Modules.RestrictToScheme.preservesZeroMorphisms (schemeCoborder i)) _ _)
      (by exact restrictToSchemeIdealCokernelComparison_isIso i)).inv ≫
    cokernel.desc
      ((Modules.restrictToScheme (schemeCoborder i)).map
        (Modules.idealAction
          (Hom.idealSheafSubobject (ofOverMap (schemeLiftCoborderOver i)))
          (Hom.idealSheaf (ofOverMap (schemeLiftCoborderOver i)))))
      (restrictedClosedIdealHom i ≫
        (schemeCoborderKernelIso i).hom ≫
          Scheme.Hom.Conormal.idealToCotangent i.left.liftCoborder)
      (by exact restrictedClosedIdealAction_comp_cotangent i)

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
  (@Modules.RestrictToScheme.restrictPullbackIso S Z (schemeCoborder i)
      (schemeLiftCoborderOver i) (closedIdealQuotient i) (closedIdealQuotient_isQuasicoherent i)).hom ≫
    (Scheme.Modules.pullback i.left.liftCoborder).map (restrictedClosedIdealQuotientHom i)

/-- Reverse comparison from the scheme kernel-cotangent pullback to the restricted
`j^* (I / I²)`. -/
noncomputable def restrictedClosedConormalInv {Z X : Over S} (i : Z ⟶ X)
    [AlgebraicGeometry.IsImmersion i.left] :
    (Scheme.Modules.pullback i.left.liftCoborder).obj
        (Scheme.Hom.Conormal.idealCotangentSheaf i.left.liftCoborder) ⟶
      (Modules.restrictToScheme Z).obj (closedConormalPullback i) :=
  (Scheme.Modules.pullback i.left.liftCoborder).map (restrictedClosedIdealQuotientInv i) ≫
    (@Modules.RestrictToScheme.restrictPullbackIso S Z (schemeCoborder i)
      (schemeLiftCoborderOver i) (closedIdealQuotient i) (closedIdealQuotient_isQuasicoherent i)).inv

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
      Scheme.Hom.conormalSheaf i.left :=
  let inverseLaws :
      restrictToSchemeIsoHom i ≫ restrictToSchemeIsoInv i = 𝟙 _ ∧
        restrictToSchemeIsoInv i ≫ restrictToSchemeIsoHom i = 𝟙 _ := sorry
  { hom := restrictToSchemeIsoHom i
    inv := restrictToSchemeIsoInv i
    hom_inv_id := inverseLaws.1
    inv_hom_id := inverseLaws.2 }

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
  (@Modules.RestrictToScheme.restrictPullbackIso S Z Z' f
      (Hom.conormalSheaf (ofOverMap i')) (Hom.conormalSheaf_isQuasicoherent (ofOverMap i'))) ≪≫
    (Scheme.Modules.pullback f.left).mapIso (restrictToSchemeIso i')

/-- The pullback-restriction comparison is the restrict/pullback interchange followed by
`restrictToSchemeIso`. -/
theorem pullbackRestrictIso_spec {Z Z' X' : Over S} (f : Z ⟶ Z') (i' : Z' ⟶ X')
    [AlgebraicGeometry.IsImmersion i'.left] :
    pullbackRestrictIso f i' =
      (@Modules.RestrictToScheme.restrictPullbackIso S Z Z' f
      (Hom.conormalSheaf (ofOverMap i')) (Hom.conormalSheaf_isQuasicoherent (ofOverMap i'))) ≪≫
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

end Hom.Conormal

end AlgebraicGeometry.AlgebraicSpace
