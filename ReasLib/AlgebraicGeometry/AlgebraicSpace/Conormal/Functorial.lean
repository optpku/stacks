module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Conormal.ClosedMap
public import Mathlib.CategoryTheory.CommSq
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Kernels
public import Mathlib.Topology.Defs.Basic
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.DirectImage
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.IdealQuotient
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.IdealSheaf
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Immersion.Coborder
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.OpenSubspace.Construction
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Pullback
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.IdealSubobject.Pullback
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Conormal.Basic
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Conormal.Restriction

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

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite
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
  OpenSubspace.fromOpens (compatibleOpenPoints i i' g)

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

/-- Commutativity places the image of the first immersion in both compatible opens. -/
theorem range_subset_compatibleOpenPoints {Z X Z' X' : AlgebraicSpace S}
    {f : Z ⟶ Z'} {i : Z ⟶ X} {i' : Z' ⟶ X'} {g : X ⟶ X'}
    [IsImmersion i] [IsImmersion i'] (sq : CommSq f i i' g) :
    Set.range (Points.map i) ⊆ compatibleOpenPoints i i' g := sorry

/-- The closed-immersion lift of `i` through the compatible open. -/
def liftToCompatibleOpen {Z X Z' X' : AlgebraicSpace S}
    {f : Z ⟶ Z'} {i : Z ⟶ X} {i' : Z' ⟶ X'} {g : X ⟶ X'}
    [IsImmersion i] [IsImmersion i'] (sq : CommSq f i i' g) :
    Z ⟶ (compatibleOpen i i' g).X :=
  OpenSubspace.Construction.lift i (range_subset_compatibleOpenPoints sq)

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
  OpenSubspace.Construction.lift (compatibleOpen i i' g).ι (by
    change Set.range (Points.map (compatibleOpen i i' g).ι) ⊆
      _root_.coborder (Set.range (Points.map i))
    intro x hx
    have hx' : x ∈ (compatibleOpen i i' g).pointsSet := hx
    rw [compatibleOpen_pointsSet] at hx'
    exact hx'.1)

/-- The comparison `compatibleOpenToCoborder` is an open immersion. -/
instance instIsOpenImmersion_compatibleOpenToCoborder {Z X Z' X' : AlgebraicSpace S}
    (i : Z ⟶ X) (i' : Z' ⟶ X') (g : X ⟶ X') [IsImmersion i] [IsImmersion i'] :
    IsOpenImmersion (compatibleOpenToCoborder i i' g) :=
  sorry

/-- The specified comparison between open subspaces is étale. -/
instance compatibleOpenToCoborder_etale {Z X Z' X' : AlgebraicSpace S}
    (i : Z ⟶ X) (i' : Z' ⟶ X') (g : X ⟶ X') [IsImmersion i] [IsImmersion i'] :
    Etale (compatibleOpenToCoborder i i' g) := sorry

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
  OpenSubspace.Construction.lift ((compatibleOpen i i' g).ι ≫ g) (by
    change Set.range (Points.map ((compatibleOpen i i' g).ι ≫ g)) ⊆
      _root_.coborder (Set.range (Points.map i'))
    rintro x ⟨y, rfl⟩
    rw [Points.map_comp]
    have hy : Points.map (compatibleOpen i i' g).ι y ∈
        (compatibleOpen i i' g).pointsSet := ⟨y, rfl⟩
    rw [compatibleOpen_pointsSet] at hy
    exact hy.2)

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

/-- A kernel section on the compatible chart also vanishes in the old coborder kernel. -/
theorem compatibleKernelSection_mem {Z X Z' X' : AlgebraicSpace S}
    {f : Z ⟶ Z'} {i : Z ⟶ X} {i' : Z' ⟶ X'} {g : X ⟶ X'}
    [IsImmersion i] [IsImmersion i'] (sq : CommSq f i i' g)
    (U : smallEtaleSite (compatibleOpen i i' g).X)
    (s : (idealSheaf (liftToCompatibleOpen sq)).val.obj (op U)) :
    ((idealSectionsIso (liftToCompatibleOpen sq) (op U)).hom s).val ∈
      LinearMap.ker
        ((SheafOfModules.evaluation (structureSheaf (Hom.coborder i))
          (op ((etaleRestriction (compatibleOpenToCoborder i i' g)).obj U))).map
          (idealSheafMap (IsImmersion.liftCoborder i))).hom := sorry

/-- Repackage the same vanishing scalar as a section of the original coborder kernel. -/
def compatibleKernelSection {Z X Z' X' : AlgebraicSpace S}
    {f : Z ⟶ Z'} {i : Z ⟶ X} {i' : Z' ⟶ X'} {g : X ⟶ X'}
    [IsImmersion i] [IsImmersion i'] (sq : CommSq f i i' g)
    (U : smallEtaleSite (compatibleOpen i i' g).X)
    (s : (idealSheaf (liftToCompatibleOpen sq)).val.obj (op U)) :
    (idealSheaf (IsImmersion.liftCoborder i)).val.obj
      (op ((etaleRestriction (compatibleOpenToCoborder i i' g)).obj U)) :=
  (idealSectionsIso (IsImmersion.liftCoborder i)
      (op ((etaleRestriction (compatibleOpenToCoborder i i' g)).obj U))).inv
    ⟨((idealSectionsIso (liftToCompatibleOpen sq) (op U)).hom s).val,
      compatibleKernelSection_mem sq U s⟩

/-- The restricted kernel section functions are additive, linear, and natural. -/
private theorem compatibleKernelToPullback_laws {Z X Z' X' : AlgebraicSpace S}
    {f : Z ⟶ Z'} {i : Z ⟶ X} {i' : Z' ⟶ X'} {g : X ⟶ X'}
    [IsImmersion i] [IsImmersion i'] (sq : CommSq f i i' g) :
    let F := idealSheaf (liftToCompatibleOpen sq)
    let G := (Modules.pullback (compatibleOpenToCoborder i i' g)).obj
      (idealSheaf (IsImmersion.liftCoborder i))
    let φ : ∀ U : (smallEtaleSite (compatibleOpen i i' g).X)ᵒᵖ,
        F.val.obj U → G.val.obj U := fun U s ↦
      pullbackSection (compatibleOpenToCoborder i i' g)
        (idealSheaf (IsImmersion.liftCoborder i)) U.unop
        (compatibleKernelSection sq U.unop s)
    (∀ U x y, φ U (x + y) = φ U x + φ U y) ∧
    (∀ U (r : (structureSheaf (compatibleOpen i i' g).X).obj.obj U) x,
      φ U (r • x) = r • φ U x) ∧
    (∀ {U V : (smallEtaleSite (compatibleOpen i i' g).X)ᵒᵖ}
      (h : U ⟶ V) (x : F.val.obj U),
      φ V (F.val.map h x) = G.val.map h (φ U x)) := sorry

set_option maxRecDepth 4096 in
/-- Lift the literal restricted kernel section into the actual pullback of the old kernel. -/
def compatibleKernelToPullback {Z X Z' X' : AlgebraicSpace S}
    {f : Z ⟶ Z'} {i : Z ⟶ X} {i' : Z' ⟶ X'} {g : X ⟶ X'}
    [IsImmersion i] [IsImmersion i'] (sq : CommSq f i i' g) :
    idealSheaf (liftToCompatibleOpen sq) ⟶
      (Modules.pullback (compatibleOpenToCoborder i i' g)).obj
        (idealSheaf (IsImmersion.liftCoborder i)) where
  val :=
    { app := fun U ↦ ModuleCat.ofHom
        { toFun := fun s ↦ pullbackSection (compatibleOpenToCoborder i i' g)
            (idealSheaf (IsImmersion.liftCoborder i)) U.unop
            (compatibleKernelSection sq U.unop s)
          map_add' := by exact (compatibleKernelToPullback_laws sq).1 U
          map_smul' := by exact (compatibleKernelToPullback_laws sq).2.1 U }
      naturality := by
        intro U V h
        ext x
        exact (compatibleKernelToPullback_laws sq).2.2 h x }

/-- The actual kernel map followed by the pulled quotient projection. -/
def compatibleQuotientKernelMap {Z X Z' X' : AlgebraicSpace S}
    {f : Z ⟶ Z'} {i : Z ⟶ X} {i' : Z' ⟶ X'} {g : X ⟶ X'}
    [IsImmersion i] [IsImmersion i'] (sq : CommSq f i i' g) :
    idealSheaf (liftToCompatibleOpen sq) ⟶
      (Modules.pullback (compatibleOpenToCoborder i i' g)).obj
        (Modules.quotientByIdeal (idealSheafSubobject (IsImmersion.liftCoborder i))
          (idealSheaf (IsImmersion.liftCoborder i))) :=
  compatibleKernelToPullback sq ≫
    (Modules.pullback (compatibleOpenToCoborder i i' g)).map
      (Modules.quotientByIdeal.π (idealSheafSubobject (IsImmersion.liftCoborder i))
        (idealSheaf (IsImmersion.liftCoborder i)))

/-- The new ideal-square action vanishes after the explicit old quotient map. -/
theorem compatibleQuotientKernelMap_w {Z X Z' X' : AlgebraicSpace S}
    {f : Z ⟶ Z'} {i : Z ⟶ X} {i' : Z' ⟶ X'} {g : X ⟶ X'}
    [IsImmersion i] [IsImmersion i'] (sq : CommSq f i i' g) :
    Modules.idealAction (idealSheafSubobject (liftToCompatibleOpen sq))
        (idealSheaf (liftToCompatibleOpen sq)) ≫ compatibleQuotientKernelMap sq = 0 := sorry

/-- The inverse restriction map is actual cokernel descent, with the same kernel sections. -/
def compatibleOpenQuotientMapInv {Z X Z' X' : AlgebraicSpace S}
    {f : Z ⟶ Z'} {i : Z ⟶ X} {i' : Z' ⟶ X'} {g : X ⟶ X'}
    [IsImmersion i] [IsImmersion i'] (sq : CommSq f i i' g) :
    Modules.quotientByIdeal (idealSheafSubobject (liftToCompatibleOpen sq))
        (idealSheaf (liftToCompatibleOpen sq)) ⟶
      (Modules.pullback (compatibleOpenToCoborder i i' g)).obj
        (Modules.quotientByIdeal (idealSheafSubobject (IsImmersion.liftCoborder i))
          (idealSheaf (IsImmersion.liftCoborder i))) :=
  cokernel.desc _ (compatibleQuotientKernelMap sq) (compatibleQuotientKernelMap_w sq)

/-- The coborder quotient restriction map and its kernel descent are mutual inverses. -/
private theorem compatibleOpenQuotientIso_laws {Z X Z' X' : AlgebraicSpace S}
    {f : Z ⟶ Z'} {i : Z ⟶ X} {i' : Z' ⟶ X'} {g : X ⟶ X'}
    [IsImmersion i] [IsImmersion i'] (sq : CommSq f i i' g) :
    compatibleOpenQuotientMap sq ≫ compatibleOpenQuotientMapInv sq = 𝟙 _ ∧
      compatibleOpenQuotientMapInv sq ≫ compatibleOpenQuotientMap sq = 𝟙 _ := sorry

/-- Restriction of the actual coborder quotient, with both maps specified. -/
def compatibleOpenQuotientIso {Z X Z' X' : AlgebraicSpace S}
    {f : Z ⟶ Z'} {i : Z ⟶ X} {i' : Z' ⟶ X'} {g : X ⟶ X'}
    [IsImmersion i] [IsImmersion i'] (sq : CommSq f i i' g) :
    (Modules.pullback (compatibleOpenToCoborder i i' g)).obj
        (Modules.quotientByIdeal (idealSheafSubobject (IsImmersion.liftCoborder i))
          (idealSheaf (IsImmersion.liftCoborder i))) ≅
      Modules.quotientByIdeal (idealSheafSubobject (liftToCompatibleOpen sq))
        (idealSheaf (liftToCompatibleOpen sq)) where
  hom := compatibleOpenQuotientMap sq
  inv := compatibleOpenQuotientMapInv sq
  hom_inv_id := by exact (compatibleOpenQuotientIso_laws sq).1
  inv_hom_id := by exact (compatibleOpenQuotientIso_laws sq).2

/-- The specified forward restriction map is an isomorphism. -/
instance instIsIso_compatibleOpenQuotientMap {Z X Z' X' : AlgebraicSpace S}
    {f : Z ⟶ Z'} {i : Z ⟶ X} {i' : Z' ⟶ X'} {g : X ⟶ X'}
    [IsImmersion i] [IsImmersion i'] (sq : CommSq f i i' g) :
    IsIso (compatibleOpenQuotientMap sq) := (compatibleOpenQuotientIso sq).isIso_hom

/-- The canonical pullback comparison between conormal sheaves of immersions in a
commutative square of algebraic spaces over `S`. -/
noncomputable def map {Z X Z' X' : AlgebraicSpace S}
    {f : Z ⟶ Z'} {i : Z ⟶ X} {i' : Z' ⟶ X'} {g : X ⟶ X'}
    [IsImmersion i] [IsImmersion i'] (sq : CommSq f i i' g) :
    (Modules.pullback f).obj (conormalSheaf i') ⟶ conormalSheaf i :=
  (Modules.pullbackCompIso f (IsImmersion.liftCoborder i')).hom.app
      (Modules.quotientByIdeal (idealSheafSubobject (IsImmersion.liftCoborder i'))
        (idealSheaf (IsImmersion.liftCoborder i'))) ≫
    (eqToIso (congrArg Modules.pullback (restrictedSq sq).w)).hom.app
      (Modules.quotientByIdeal (idealSheafSubobject (IsImmersion.liftCoborder i'))
        (idealSheaf (IsImmersion.liftCoborder i'))) ≫
    (Modules.pullbackCompIso (liftToCompatibleOpen sq)
        (restrictToCompatibleOpen i i' g)).inv.app
      (Modules.quotientByIdeal (idealSheafSubobject (IsImmersion.liftCoborder i'))
        (idealSheaf (IsImmersion.liftCoborder i'))) ≫
    (Modules.pullback (liftToCompatibleOpen sq)).map
      (idealQuotientMap (restrictedSq sq)) ≫
    (Modules.pullback (liftToCompatibleOpen sq)).map
      (compatibleOpenQuotientMapInv sq) ≫
    (Modules.pullbackCompIso (liftToCompatibleOpen sq)
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
