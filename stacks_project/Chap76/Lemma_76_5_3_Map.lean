module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Conormal.ClosedMap
public import Mathlib.CategoryTheory.CommSq
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Kernels
public import Mathlib.Topology.Defs.Basic
public import stacks_project.Chap66.«66_26_0_1_Pushforward»
public import stacks_project.Chap67.Lemma_67_14_1_Quotient
public import stacks_project.Chap67.Lemma_67_28_12_IdealSheaf
public import stacks_project.Chap67.Remark_67_12_4_Coborder
public import stacks_project.Chap67.Remark_67_12_5_Opens
public import stacks_project.Chap70.Lemma_70_5_6_GlobalSections
public import stacks_project.Chap69.Lemma_69_17_2_Pullback
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Conormal.Basic

/-!
# Functoriality of conormal sheaves of immersions of algebraic spaces

A commutative square of algebraic spaces whose horizontal arrows are immersions
induces a canonical morphism of conormal sheaves
`(Modules.pullback f).obj (conormalSheaf i') ⟶ conormalSheaf i`.
The construction reduces to closed immersions on the compatible open
`coborder(i) ∩ g⁻¹ coborder(i')`, compares coborder ideal quotients, and
transports along `Modules.pullbackComp`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
open AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

variable {S : Scheme.{u}}

namespace Hom.Conormal

/-- The coborder of the image of `i` intersected with the preimage of the coborder
of the image of `i'` is open in `Points X`. -/
theorem isOpen_compatibleOpenPoints {Z X Z' X' : AlgebraicSpace S}
    (i : Z ⟶ X) (i' : Z' ⟶ X') (g : X ⟶ X') [IsImmersion i] [IsImmersion i'] :
    IsOpen
      (_root_.coborder (Set.range (Points.map i)) ∩
        Points.map g ⁻¹' _root_.coborder (Set.range (Points.map i'))) :=
  sorry

/-- The open of `|X|` on which both immersions become closed and `g` restricts. -/
def compatibleOpenPoints {Z X Z' X' : AlgebraicSpace S}
    (i : Z ⟶ X) (i' : Z' ⟶ X') (g : X ⟶ X') [IsImmersion i] [IsImmersion i'] :
    Opens (Points X) :=
  Opens.mk
    (_root_.coborder (Set.range (Points.map i)) ∩
      Points.map g ⁻¹' _root_.coborder (Set.range (Points.map i')))
    (isOpen_compatibleOpenPoints i i' g)

/-- The compatible open subspace `U ⊂ X` with
`|U| = coborder(i) ∩ g⁻¹ coborder(i')`. -/
def compatibleOpen {Z X Z' X' : AlgebraicSpace S}
    (i : Z ⟶ X) (i' : Z' ⟶ X') (g : X ⟶ X') [IsImmersion i] [IsImmersion i'] :
    OpenSubspace X :=
  OpenSubspace.ofOpens (compatibleOpenPoints i i' g)

/-- The point-set of `compatibleOpen` is the coborder of `i` intersected with the
preimage of the coborder of `i'`. -/
theorem compatibleOpen_pointsSet {Z X Z' X' : AlgebraicSpace S}
    (i : Z ⟶ X) (i' : Z' ⟶ X') (g : X ⟶ X') [IsImmersion i] [IsImmersion i'] :
    (compatibleOpen i i' g).pointsSet =
      _root_.coborder (Set.range (Points.map i)) ∩
        Points.map g ⁻¹' _root_.coborder (Set.range (Points.map i')) :=
  sorry

/-- The image of `i` lands in the compatible open, using commutativity of the
square to place `g(i(Z))` in the coborder of `i'`. -/
theorem exists_liftToCompatibleOpen {Z X Z' X' : AlgebraicSpace S}
    {f : Z ⟶ Z'} {i : Z ⟶ X} {i' : Z' ⟶ X'} {g : X ⟶ X'}
    [IsImmersion i] [IsImmersion i'] (sq : CommSq f i i' g) :
    ∃ iU : Z ⟶ (compatibleOpen i i' g).X, iU ≫ (compatibleOpen i i' g).ι = i :=
  sorry

/-- The closed-immersion lift of `i` through the compatible open. -/
def liftToCompatibleOpen {Z X Z' X' : AlgebraicSpace S}
    {f : Z ⟶ Z'} {i : Z ⟶ X} {i' : Z' ⟶ X'} {g : X ⟶ X'}
    [IsImmersion i] [IsImmersion i'] (sq : CommSq f i i' g) :
    Z ⟶ (compatibleOpen i i' g).X :=
  Classical.choose (exists_liftToCompatibleOpen sq)

/-- The compatible-open lift composed with the open inclusion recovers `i`. -/
theorem liftToCompatibleOpen_comp {Z X Z' X' : AlgebraicSpace S}
    {f : Z ⟶ Z'} {i : Z ⟶ X} {i' : Z' ⟶ X'} {g : X ⟶ X'}
    [IsImmersion i] [IsImmersion i'] (sq : CommSq f i i' g) :
    liftToCompatibleOpen sq ≫ (compatibleOpen i i' g).ι = i :=
  sorry

/-- The compatible-open lift of an immersion is a closed immersion. -/
instance instIsClosedImmersion_liftToCompatibleOpen {Z X Z' X' : AlgebraicSpace S}
    {f : Z ⟶ Z'} {i : Z ⟶ X} {i' : Z' ⟶ X'} {g : X ⟶ X'}
    [IsImmersion i] [IsImmersion i'] (sq : CommSq f i i' g) :
    IsClosedImmersion (liftToCompatibleOpen sq) :=
  sorry

/-- The compatible open is contained in the coborder range of `i`. -/
theorem exists_compatibleOpenToCoborder {Z X Z' X' : AlgebraicSpace S}
    (i : Z ⟶ X) (i' : Z' ⟶ X') (g : X ⟶ X') [IsImmersion i] [IsImmersion i'] :
    ∃ φ : (compatibleOpen i i' g).X ⟶ (IsImmersion.coborderRange i).X,
      φ ≫ (IsImmersion.coborderRange i).ι = (compatibleOpen i i' g).ι :=
  sorry

/-- The open immersion from the compatible open into the coborder range of `i`. -/
def compatibleOpenToCoborder {Z X Z' X' : AlgebraicSpace S}
    (i : Z ⟶ X) (i' : Z' ⟶ X') (g : X ⟶ X') [IsImmersion i] [IsImmersion i'] :
    (compatibleOpen i i' g).X ⟶ (IsImmersion.coborderRange i).X :=
  Classical.choose (exists_compatibleOpenToCoborder i i' g)

/-- The comparison `compatibleOpenToCoborder` is an open immersion. -/
instance instIsOpenImmersion_compatibleOpenToCoborder {Z X Z' X' : AlgebraicSpace S}
    (i : Z ⟶ X) (i' : Z' ⟶ X') (g : X ⟶ X') [IsImmersion i] [IsImmersion i'] :
    IsOpenImmersion (compatibleOpenToCoborder i i' g) :=
  sorry

/-- The compatible-open lift of `i` composed with `compatibleOpenToCoborder` is the
coborder closed immersion of `i`. -/
theorem liftToCompatibleOpen_comp_toCoborder {Z X Z' X' : AlgebraicSpace S}
    {f : Z ⟶ Z'} {i : Z ⟶ X} {i' : Z' ⟶ X'} {g : X ⟶ X'}
    [IsImmersion i] [IsImmersion i'] (sq : CommSq f i i' g) :
    liftToCompatibleOpen sq ≫ compatibleOpenToCoborder i i' g =
      IsImmersion.liftCoborder i :=
  sorry

/-- `g` sends the compatible open into the coborder range of `i'`. -/
theorem exists_restrictToCompatibleOpen {Z X Z' X' : AlgebraicSpace S}
    (i : Z ⟶ X) (i' : Z' ⟶ X') (g : X ⟶ X') [IsImmersion i] [IsImmersion i'] :
    ∃ gU : (compatibleOpen i i' g).X ⟶ (IsImmersion.coborderRange i').X,
      gU ≫ (IsImmersion.coborderRange i').ι = (compatibleOpen i i' g).ι ≫ g :=
  sorry

/-- The restriction of `g` from the compatible open to the coborder range of `i'`. -/
def restrictToCompatibleOpen {Z X Z' X' : AlgebraicSpace S}
    (i : Z ⟶ X) (i' : Z' ⟶ X') (g : X ⟶ X') [IsImmersion i] [IsImmersion i'] :
    (compatibleOpen i i' g).X ⟶ (IsImmersion.coborderRange i').X :=
  Classical.choose (exists_restrictToCompatibleOpen i i' g)

/-- The restricted morphism composed with the coborder inclusion of `i'` is
`compatibleOpen.ι ≫ g`. -/
theorem restrictToCompatibleOpen_comp {Z X Z' X' : AlgebraicSpace S}
    (i : Z ⟶ X) (i' : Z' ⟶ X') (g : X ⟶ X') [IsImmersion i] [IsImmersion i'] :
    restrictToCompatibleOpen i i' g ≫ (IsImmersion.coborderRange i').ι =
      (compatibleOpen i i' g).ι ≫ g :=
  sorry

/-- After restriction to the compatible open, the original square remains
commutative. -/
theorem restrictedSq {Z X Z' X' : AlgebraicSpace S}
    {f : Z ⟶ Z'} {i : Z ⟶ X} {i' : Z' ⟶ X'} {g : X ⟶ X'}
    [IsImmersion i] [IsImmersion i'] (sq : CommSq f i i' g) :
    CommSq f (liftToCompatibleOpen sq) (IsImmersion.liftCoborder i')
      (restrictToCompatibleOpen i i' g) :=
  sorry

/-- The identity square relating the compatible-open lift of `i` to its coborder
closed immersion. -/
theorem coborderSq {Z X Z' X' : AlgebraicSpace S}
    {f : Z ⟶ Z'} {i : Z ⟶ X} {i' : Z' ⟶ X'} {g : X ⟶ X'}
    [IsImmersion i] [IsImmersion i'] (sq : CommSq f i i' g) :
    CommSq (𝟙 Z) (liftToCompatibleOpen sq) (IsImmersion.liftCoborder i)
      (compatibleOpenToCoborder i i' g) :=
  sorry

/-- Restriction of the coborder ideal quotient of `i` to the compatible open. -/
noncomputable def compatibleOpenQuotientMap {Z X Z' X' : AlgebraicSpace S}
    {f : Z ⟶ Z'} {i : Z ⟶ X} {i' : Z' ⟶ X'} {g : X ⟶ X'}
    [IsImmersion i] [IsImmersion i'] (sq : CommSq f i i' g) :
    (Modules.pullback (compatibleOpenToCoborder i i' g)).obj
        (Modules.quotientByIdeal (idealSheafSubobject (IsImmersion.liftCoborder i))
          (idealSheaf (IsImmersion.liftCoborder i))) ⟶
      Modules.quotientByIdeal (idealSheafSubobject (liftToCompatibleOpen sq))
        (idealSheaf (liftToCompatibleOpen sq)) :=
  idealQuotientMap (coborderSq sq)

/-- Restriction of the coborder ideal quotient along the compatible open is an
isomorphism. -/
instance instIsIso_compatibleOpenQuotientMap {Z X Z' X' : AlgebraicSpace S}
    {f : Z ⟶ Z'} {i : Z ⟶ X} {i' : Z' ⟶ X'} {g : X ⟶ X'}
    [IsImmersion i] [IsImmersion i'] (sq : CommSq f i i' g) :
    IsIso (compatibleOpenQuotientMap sq) :=
  sorry

/-- The canonical pullback comparison between conormal sheaves of immersions in a
commutative square of algebraic spaces over `S`. -/
noncomputable def map {Z X Z' X' : AlgebraicSpace S}
    {f : Z ⟶ Z'} {i : Z ⟶ X} {i' : Z' ⟶ X'} {g : X ⟶ X'}
    [IsImmersion i] [IsImmersion i'] (sq : CommSq f i i' g) :
    (Modules.pullback f).obj (conormalSheaf i') ⟶ conormalSheaf i :=
  (Modules.pullbackComp f (IsImmersion.liftCoborder i')).hom.app
      (Modules.quotientByIdeal (idealSheafSubobject (IsImmersion.liftCoborder i'))
        (idealSheaf (IsImmersion.liftCoborder i'))) ≫
    (eqToIso (congrArg Modules.pullback (restrictedSq sq).w)).hom.app
      (Modules.quotientByIdeal (idealSheafSubobject (IsImmersion.liftCoborder i'))
        (idealSheaf (IsImmersion.liftCoborder i'))) ≫
    (Modules.pullbackComp (liftToCompatibleOpen sq)
        (restrictToCompatibleOpen i i' g)).inv.app
      (Modules.quotientByIdeal (idealSheafSubobject (IsImmersion.liftCoborder i'))
        (idealSheaf (IsImmersion.liftCoborder i'))) ≫
    (Modules.pullback (liftToCompatibleOpen sq)).map
      (idealQuotientMap (restrictedSq sq)) ≫
    (Modules.pullback (liftToCompatibleOpen sq)).map
      (inv (compatibleOpenQuotientMap sq)) ≫
    (Modules.pullbackComp (liftToCompatibleOpen sq)
        (compatibleOpenToCoborder i i' g)).hom.app
      (Modules.quotientByIdeal (idealSheafSubobject (IsImmersion.liftCoborder i))
        (idealSheaf (IsImmersion.liftCoborder i))) ≫
    (eqToIso (congrArg Modules.pullback
        (liftToCompatibleOpen_comp_toCoborder sq))).hom.app
      (Modules.quotientByIdeal (idealSheafSubobject (IsImmersion.liftCoborder i))
        (idealSheaf (IsImmersion.liftCoborder i)))

/-- A morphism of conormal sheaves is the canonical comparison of a commutative
square of immersions when it equals `map sq`. -/
def IsMap {Z X Z' X' : AlgebraicSpace S}
    {f : Z ⟶ Z'} {i : Z ⟶ X} {i' : Z' ⟶ X'} {g : X ⟶ X'}
    [IsImmersion i] [IsImmersion i'] (sq : CommSq f i i' g)
    (tau : (Modules.pullback f).obj (conormalSheaf i') ⟶ conormalSheaf i) : Prop :=
  tau = map sq

/-- The constructed comparison satisfies `IsMap`. -/
theorem map_spec {Z X Z' X' : AlgebraicSpace S}
    {f : Z ⟶ Z'} {i : Z ⟶ X} {i' : Z' ⟶ X'} {g : X ⟶ X'}
    [IsImmersion i] [IsImmersion i'] (sq : CommSq f i i' g) :
    IsMap sq (map sq) :=
  sorry

end Hom.Conormal

end AlgebraicGeometry.AlgebraicSpace
