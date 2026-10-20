module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Subspace.LocallyClosed
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Groupoid.Restriction
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Groupoid.Smooth
public import ReasLib.CategoryTheory.Subobject.Invariant

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits AlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidAlgebraicSpace

/-- For an open subspace, open invariance is equivalent to locally closed invariance of the
underlying locally closed subspace. -/
theorem isOpenInvariant_iff_isLocallyClosedInvariant {S : Scheme.{u}}
    {B : AlgebraicSpace S} (G : GroupoidAlgebraicSpace B)
    (W : OpenSubspace G.U.left) :
    CategoryTheory.Morphism.IsForwardInvariant G.s.left G.t.left W.ι ↔ CategoryTheory.Morphism.IsPullbackInvariant G.s.left G.t.left W.toLocallyClosed.ι :=
  sorry


/-- The locally closed subspace `Z ⊂ U` viewed as an object of `Over B` with structure map
`Z.ι ≫ G.U.hom`. -/
def overObj {S : Scheme.{u}} {B : AlgebraicSpace S} (G : GroupoidAlgebraicSpace B)
    (Z : LocallyClosedSubspace G.U.left) : Over B :=
  Over.mk (Z.ι ≫ G.U.hom)

/-- The structure morphism of `overObj G Z` is `Z.ι ≫ G.U.hom`. -/
theorem overObj_hom {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) (Z : LocallyClosedSubspace G.U.left) :
    (overObj G Z).hom = Z.ι ≫ G.U.hom :=
  rfl

/-- The underlying algebraic space of `overObj G Z` is `Z.X`. -/
theorem overObj_left {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) (Z : LocallyClosedSubspace G.U.left) :
    (overObj G Z).left = Z.X :=
  rfl

/-- The inclusion `Z ⊂ U` as a morphism of objects over `B`. -/
def overι {S : Scheme.{u}} {B : AlgebraicSpace S} (G : GroupoidAlgebraicSpace B)
    (Z : LocallyClosedSubspace G.U.left) : overObj G Z ⟶ G.U :=
  Over.homMk Z.ι rfl

/-- The underlying morphism of algebraic spaces of `overι G Z` is `Z.ι`. -/
theorem overι_left {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) (Z : LocallyClosedSubspace G.U.left) :
    (overι G Z).left = Z.ι :=
  rfl

/-- Restriction of a groupoid in algebraic spaces to a locally closed subspace of its object
space. -/
def restrict {S : Scheme.{u}} {B : AlgebraicSpace S} (G : GroupoidAlgebraicSpace B)
    (Z : LocallyClosedSubspace G.U.left) : GroupoidAlgebraicSpace B :=
  G.pullback (overι G Z)

/-- The restricted groupoid is the pullback of `G` along `overι G Z`. -/
theorem restrict_eq {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) (Z : LocallyClosedSubspace G.U.left) :
    restrict G Z = G.pullback (overι G Z) :=
  rfl

/-- The object space of the restriction is `overObj G Z`. -/
theorem restrict_U {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) (Z : LocallyClosedSubspace G.U.left) :
    (restrict G Z).U = overObj G Z :=
  rfl

/-- The arrow space of the restriction is the pullback of the underlying pre-relation along
`overι G Z`. -/
theorem restrict_R {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) (Z : LocallyClosedSubspace G.U.left) :
    (restrict G Z).R = (G.toPreRelation.pullback (overι G Z)).left :=
  rfl

/-- The canonical morphism of groupoids from the restriction to the original groupoid. -/
def restrictHom {S : Scheme.{u}} {B : AlgebraicSpace S} (G : GroupoidAlgebraicSpace B)
    (Z : LocallyClosedSubspace G.U.left) : Hom (restrict G Z) G :=
  pullbackHom G (overι G Z)

/-- The object component of `restrictHom G Z` is `overι G Z`. -/
theorem restrictHom_obj {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) (Z : LocallyClosedSubspace G.U.left) :
    (restrictHom G Z).obj = overι G Z :=
  rfl

/-- The arrow component of `restrictHom G Z` is the canonical pullback projection. -/
theorem restrictHom_arrow {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) (Z : LocallyClosedSubspace G.U.left) :
    (restrictHom G Z).arrow = pullbackArrow G (overι G Z) :=
  rfl

/-- Restriction of a smooth groupoid to an `R`-invariant locally closed subspace remains
smooth. Invariance is required: without it the restricted source need not be smooth. -/
theorem smooth_restrict {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) [Smooth G] (Z : LocallyClosedSubspace G.U.left)
    (hZ : CategoryTheory.Morphism.IsPullbackInvariant G.s.left G.t.left Z.ι) :
    Smooth (restrict G Z) :=
  sorry

/-- Restriction of a smooth groupoid to an `R`-invariant open subspace remains smooth. -/
theorem smooth_restrict_open {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) [Smooth G] (W : OpenSubspace G.U.left)
    (hW : CategoryTheory.Morphism.IsForwardInvariant G.s.left G.t.left W.ι) :
    Smooth (restrict G W.toLocallyClosed) :=
  smooth_restrict G W.toLocallyClosed
    ((isOpenInvariant_iff_isLocallyClosedInvariant G W).mp hW)

/-- The source square of `restrictHom G Z` is cartesian if and only if `Z` is locally closed
invariant. -/
theorem isPullback_restrictHom_source_iff {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) (Z : LocallyClosedSubspace G.U.left) :
    IsPullback (restrictHom G Z).arrow (restrict G Z).s G.s (restrictHom G Z).obj ↔
      CategoryTheory.Morphism.IsPullbackInvariant G.s.left G.t.left Z.ι :=
  sorry

/-- If `Z` is locally closed invariant, the source square of `restrictHom G Z` is cartesian. -/
theorem isPullback_restrictHom_source {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) (Z : LocallyClosedSubspace G.U.left)
    (hZ : CategoryTheory.Morphism.IsPullbackInvariant G.s.left G.t.left Z.ι) :
    IsPullback (restrictHom G Z).arrow (restrict G Z).s G.s (restrictHom G Z).obj :=
  (isPullback_restrictHom_source_iff G Z).mpr hZ

/-- If `Z` is locally closed invariant, the underlying algebraic-space source square of
`restrictHom G Z` is cartesian. -/
theorem isPullback_restrictHom_source_left {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) (Z : LocallyClosedSubspace G.U.left)
    (hZ : CategoryTheory.Morphism.IsPullbackInvariant G.s.left G.t.left Z.ι) :
    IsPullback (restrict G Z).s.left (restrictHom G Z).arrow.left Z.ι G.s.left :=
  sorry

/-- If `Z` is locally closed invariant, the underlying algebraic-space target square of
`restrictHom G Z` is cartesian. -/
theorem isPullback_restrictHom_target_left {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) (Z : LocallyClosedSubspace G.U.left)
    (hZ : CategoryTheory.Morphism.IsPullbackInvariant G.s.left G.t.left Z.ι) :
    IsPullback (restrict G Z).t.left (restrictHom G Z).arrow.left Z.ι G.t.left :=
  sorry

/-- If `Z` is locally closed invariant, the restricted arrow space identifies with the inverse
image of `Z` along the source map. -/
def restrict_arrowIso_sourceInverseImage {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) (Z : LocallyClosedSubspace G.U.left)
    (hZ : CategoryTheory.Morphism.IsPullbackInvariant G.s.left G.t.left Z.ι) :
    (restrict G Z).R.left ≅ Limits.pullback Z.ι G.s.left :=
  (isPullback_restrictHom_source_left G Z hZ).isoPullback

/-- The comparison isomorphism to `s⁻¹(Z)` commutes with the maps to `G.R`. -/
theorem restrict_arrowIso_sourceInverseImage_hom_comp_snd {S : Scheme.{u}}
    {B : AlgebraicSpace S} (G : GroupoidAlgebraicSpace B)
    (Z : LocallyClosedSubspace G.U.left) (hZ : CategoryTheory.Morphism.IsPullbackInvariant G.s.left G.t.left Z.ι) :
    (restrict_arrowIso_sourceInverseImage G Z hZ).hom ≫
      Limits.pullback.snd Z.ι G.s.left =
    (restrictHom G Z).arrow.left :=
  (isPullback_restrictHom_source_left G Z hZ).isoPullback_hom_snd

/-- The comparison isomorphism to `s⁻¹(Z)` recovers the restricted source map. -/
theorem restrict_arrowIso_sourceInverseImage_hom_comp_fst {S : Scheme.{u}}
    {B : AlgebraicSpace S} (G : GroupoidAlgebraicSpace B)
    (Z : LocallyClosedSubspace G.U.left) (hZ : CategoryTheory.Morphism.IsPullbackInvariant G.s.left G.t.left Z.ι) :
    (restrict_arrowIso_sourceInverseImage G Z hZ).hom ≫
      Limits.pullback.fst Z.ι G.s.left =
    (restrict G Z).s.left :=
  (isPullback_restrictHom_source_left G Z hZ).isoPullback_hom_fst

/-- If `Z` is locally closed invariant, the restricted arrow space identifies with the inverse
image of `Z` along the target map. -/
def restrict_arrowIso_targetInverseImage {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) (Z : LocallyClosedSubspace G.U.left)
    (hZ : CategoryTheory.Morphism.IsPullbackInvariant G.s.left G.t.left Z.ι) :
    (restrict G Z).R.left ≅ Limits.pullback Z.ι G.t.left :=
  (isPullback_restrictHom_target_left G Z hZ).isoPullback

/-- The comparison isomorphism to `t⁻¹(Z)` commutes with the maps to `G.R`. -/
theorem restrict_arrowIso_targetInverseImage_hom_comp_snd {S : Scheme.{u}}
    {B : AlgebraicSpace S} (G : GroupoidAlgebraicSpace B)
    (Z : LocallyClosedSubspace G.U.left) (hZ : CategoryTheory.Morphism.IsPullbackInvariant G.s.left G.t.left Z.ι) :
    (restrict_arrowIso_targetInverseImage G Z hZ).hom ≫
      Limits.pullback.snd Z.ι G.t.left =
    (restrictHom G Z).arrow.left :=
  (isPullback_restrictHom_target_left G Z hZ).isoPullback_hom_snd

/-- The comparison isomorphism to `t⁻¹(Z)` recovers the restricted target map. -/
theorem restrict_arrowIso_targetInverseImage_hom_comp_fst {S : Scheme.{u}}
    {B : AlgebraicSpace S} (G : GroupoidAlgebraicSpace B)
    (Z : LocallyClosedSubspace G.U.left) (hZ : CategoryTheory.Morphism.IsPullbackInvariant G.s.left G.t.left Z.ι) :
    (restrict_arrowIso_targetInverseImage G Z hZ).hom ≫
      Limits.pullback.fst Z.ι G.t.left =
    (restrict G Z).t.left :=
  (isPullback_restrictHom_target_left G Z hZ).isoPullback_hom_fst

end AlgebraicGeometry.GroupoidAlgebraicSpace
