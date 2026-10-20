/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import stacks_project.Chap65.Definition_65_12_1_Subspace
public import stacks_project.Chap78.Lemma_78_17_1_Restriction
public import stacks_project.Chap94.Definition_94_16_4_Smooth
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Groupoid.Restriction.LocallyClosed

/-!
# Restriction of a groupoid in algebraic spaces to a subspace

A locally closed subspace `Z ⊂ U` of the object space of a groupoid `G` in
algebraic spaces determines an object `overObj G Z` over the same base, an
inclusion `overι G Z`, and the restricted groupoid `restrict G Z` together with
its canonical morphism `restrictHom G Z`. Smoothness of the restriction requires
invariance of `Z`, so that `R_Z` identifies with the inverse images of `Z` along
`s` and `t`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits AlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.OpenSubspace

/- The locally closed subspace underlying an open subspace. -/
#check (AlgebraicGeometry.AlgebraicSpace.OpenSubspace.toLocallyClosed : ∀ {S : Scheme.{u}} {F : AlgebraicSpace S} (W : OpenSubspace F) ,
    LocallyClosedSubspace F)

/- The inclusion of `toLocallyClosed W` is the open inclusion of `W`. -/
#check (AlgebraicGeometry.AlgebraicSpace.OpenSubspace.toLocallyClosed_ι : ∀ {S : Scheme.{u}} {F : AlgebraicSpace S}
    (W : OpenSubspace F) ,
    W.toLocallyClosed.ι = W.ι)

/- The underlying algebraic space of `toLocallyClosed W` is that of `W`. -/
#check (AlgebraicGeometry.AlgebraicSpace.OpenSubspace.toLocallyClosed_X : ∀ {S : Scheme.{u}} {F : AlgebraicSpace S}
    (W : OpenSubspace F) ,
    W.toLocallyClosed.X = W.X)

end AlgebraicGeometry.AlgebraicSpace.OpenSubspace

namespace AlgebraicGeometry.AlgebraicSpace.ClosedSubspace

/- The locally closed subspace underlying a closed subspace. -/
#check (AlgebraicGeometry.AlgebraicSpace.ClosedSubspace.toLocallyClosed : ∀ {S : Scheme.{u}} {F : AlgebraicSpace S} (C : ClosedSubspace F) ,
    LocallyClosedSubspace F)

/- The inclusion of `toLocallyClosed C` is the closed inclusion of `C`. -/
#check (AlgebraicGeometry.AlgebraicSpace.ClosedSubspace.toLocallyClosed_ι : ∀ {S : Scheme.{u}} {F : AlgebraicSpace S}
    (C : ClosedSubspace F) ,
    C.toLocallyClosed.ι = C.ι)

/- The underlying algebraic space of `toLocallyClosed C` is that of `C`. -/
#check (AlgebraicGeometry.AlgebraicSpace.ClosedSubspace.toLocallyClosed_X : ∀ {S : Scheme.{u}} {F : AlgebraicSpace S}
    (C : ClosedSubspace F) ,
    C.toLocallyClosed.X = C.X)

end AlgebraicGeometry.AlgebraicSpace.ClosedSubspace

namespace AlgebraicGeometry.GroupoidAlgebraicSpace

/-- An open subspace `W ⊂ U` is invariant under a groupoid when the restriction of `t` to
the inverse image of `W` along `s` factors through `W.ι`. -/
abbrev IsOpenInvariant {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) (W : OpenSubspace G.U.left) : Prop :=
  CategoryTheory.Morphism.IsForwardInvariant G.s.left G.t.left W.ι

/-- Open invariance unfolds to a factoring of the restricted target map through `W`. -/
theorem isOpenInvariant_iff {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) (W : OpenSubspace G.U.left) :
    G.IsOpenInvariant W ↔
      ∃ h : Limits.pullback W.ι G.s.left ⟶ W.X,
        h ≫ W.ι = Limits.pullback.snd W.ι G.s.left ≫ G.t.left :=
  Iff.rfl

/-- A locally closed subspace `Z ⊂ U` is invariant under a groupoid when the inverse images
of `Z` along `t` and `s` agree as objects over the arrow space. -/
abbrev IsLocallyClosedInvariant {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) (Z : LocallyClosedSubspace G.U.left) : Prop :=
  CategoryTheory.Morphism.IsPullbackInvariant G.s.left G.t.left Z.ι

/-- Locally closed invariance unfolds to a commuting isomorphism of inverse images. -/
theorem isLocallyClosedInvariant_iff {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) (Z : LocallyClosedSubspace G.U.left) :
    G.IsLocallyClosedInvariant Z ↔
      ∃ e : Limits.pullback Z.ι G.t.left ≅ Limits.pullback Z.ι G.s.left,
        e.hom ≫ Limits.pullback.snd Z.ι G.s.left = Limits.pullback.snd Z.ι G.t.left :=
  Iff.rfl

/- For an open subspace, open invariance is equivalent to locally closed invariance of the
underlying locally closed subspace. -/
#check (AlgebraicGeometry.GroupoidAlgebraicSpace.isOpenInvariant_iff_isLocallyClosedInvariant : ∀ {S : Scheme.{u}}
    {B : AlgebraicSpace S} (G : GroupoidAlgebraicSpace B)
    (W : OpenSubspace G.U.left) ,
    G.IsOpenInvariant W ↔ G.IsLocallyClosedInvariant W.toLocallyClosed)

/- The locally closed subspace `Z ⊂ U` viewed as an object of `Over B` with structure map
`Z.ι ≫ G.U.hom`. -/
#check (AlgebraicGeometry.GroupoidAlgebraicSpace.overObj : ∀ {S : Scheme.{u}} {B : AlgebraicSpace S} (G : GroupoidAlgebraicSpace B)
    (Z : LocallyClosedSubspace G.U.left) ,
    Over B)

/- The structure morphism of `overObj G Z` is `Z.ι ≫ G.U.hom`. -/
#check (AlgebraicGeometry.GroupoidAlgebraicSpace.overObj_hom : ∀ {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) (Z : LocallyClosedSubspace G.U.left) ,
    (overObj G Z).hom = Z.ι ≫ G.U.hom)

/- The underlying algebraic space of `overObj G Z` is `Z.X`. -/
#check (AlgebraicGeometry.GroupoidAlgebraicSpace.overObj_left : ∀ {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) (Z : LocallyClosedSubspace G.U.left) ,
    (overObj G Z).left = Z.X)

/- The inclusion `Z ⊂ U` as a morphism of objects over `B`. -/
#check (AlgebraicGeometry.GroupoidAlgebraicSpace.overι : ∀ {S : Scheme.{u}} {B : AlgebraicSpace S} (G : GroupoidAlgebraicSpace B)
    (Z : LocallyClosedSubspace G.U.left) ,
    overObj G Z ⟶ G.U)

/- The underlying morphism of algebraic spaces of `overι G Z` is `Z.ι`. -/
#check (AlgebraicGeometry.GroupoidAlgebraicSpace.overι_left : ∀ {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) (Z : LocallyClosedSubspace G.U.left) ,
    (overι G Z).left = Z.ι)

/- Restriction of a groupoid in algebraic spaces to a locally closed subspace of its object
space. -/
#check (AlgebraicGeometry.GroupoidAlgebraicSpace.restrict : ∀ {S : Scheme.{u}} {B : AlgebraicSpace S} (G : GroupoidAlgebraicSpace B)
    (Z : LocallyClosedSubspace G.U.left) ,
    GroupoidAlgebraicSpace B)

/- The restricted groupoid is the pullback of `G` along `overι G Z`. -/
#check (AlgebraicGeometry.GroupoidAlgebraicSpace.restrict_eq : ∀ {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) (Z : LocallyClosedSubspace G.U.left) ,
    restrict G Z = G.pullback (overι G Z))

/- The object space of the restriction is `overObj G Z`. -/
#check (AlgebraicGeometry.GroupoidAlgebraicSpace.restrict_U : ∀ {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) (Z : LocallyClosedSubspace G.U.left) ,
    (restrict G Z).U = overObj G Z)

/- The arrow space of the restriction is the pullback of the underlying pre-relation along
`overι G Z`. -/
#check (AlgebraicGeometry.GroupoidAlgebraicSpace.restrict_R : ∀ {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) (Z : LocallyClosedSubspace G.U.left) ,
    (restrict G Z).R = (G.toPreRelation.pullback (overι G Z)).left)

/- The canonical morphism of groupoids from the restriction to the original groupoid. -/
#check (AlgebraicGeometry.GroupoidAlgebraicSpace.restrictHom : ∀ {S : Scheme.{u}} {B : AlgebraicSpace S} (G : GroupoidAlgebraicSpace B)
    (Z : LocallyClosedSubspace G.U.left) ,
    Hom (restrict G Z) G)

/- The object component of `restrictHom G Z` is `overι G Z`. -/
#check (AlgebraicGeometry.GroupoidAlgebraicSpace.restrictHom_obj : ∀ {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) (Z : LocallyClosedSubspace G.U.left) ,
    (restrictHom G Z).obj = overι G Z)

/- The arrow component of `restrictHom G Z` is the canonical pullback projection. -/
#check (AlgebraicGeometry.GroupoidAlgebraicSpace.restrictHom_arrow : ∀ {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) (Z : LocallyClosedSubspace G.U.left) ,
    (restrictHom G Z).arrow = pullbackArrow G (overι G Z))

/- Restriction of a smooth groupoid to an `R`-invariant locally closed subspace remains
smooth. Invariance is required: without it the restricted source need not be smooth. -/
#check (AlgebraicGeometry.GroupoidAlgebraicSpace.smooth_restrict : ∀ {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) [Smooth G] (Z : LocallyClosedSubspace G.U.left)
    (hZ : G.IsLocallyClosedInvariant Z) ,
    Smooth (restrict G Z))

/- Restriction of a smooth groupoid to an `R`-invariant open subspace remains smooth. -/
#check (AlgebraicGeometry.GroupoidAlgebraicSpace.smooth_restrict_open : ∀ {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) [Smooth G] (W : OpenSubspace G.U.left)
    (hW : G.IsOpenInvariant W) ,
    Smooth (restrict G W.toLocallyClosed))

/- The source square of `restrictHom G Z` is cartesian if and only if `Z` is locally closed
invariant. -/
#check (AlgebraicGeometry.GroupoidAlgebraicSpace.isPullback_restrictHom_source_iff : ∀ {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) (Z : LocallyClosedSubspace G.U.left) ,
    IsPullback (restrictHom G Z).arrow (restrict G Z).s G.s (restrictHom G Z).obj ↔
      G.IsLocallyClosedInvariant Z)

/- If `Z` is locally closed invariant, the source square of `restrictHom G Z` is cartesian. -/
#check (AlgebraicGeometry.GroupoidAlgebraicSpace.isPullback_restrictHom_source : ∀ {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) (Z : LocallyClosedSubspace G.U.left)
    (hZ : G.IsLocallyClosedInvariant Z) ,
    IsPullback (restrictHom G Z).arrow (restrict G Z).s G.s (restrictHom G Z).obj)

/- If `Z` is locally closed invariant, the underlying algebraic-space source square of
`restrictHom G Z` is cartesian. -/
#check (AlgebraicGeometry.GroupoidAlgebraicSpace.isPullback_restrictHom_source_left : ∀ {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) (Z : LocallyClosedSubspace G.U.left)
    (hZ : G.IsLocallyClosedInvariant Z) ,
    IsPullback (restrict G Z).s.left (restrictHom G Z).arrow.left Z.ι G.s.left)

/- If `Z` is locally closed invariant, the underlying algebraic-space target square of
`restrictHom G Z` is cartesian. -/
#check (AlgebraicGeometry.GroupoidAlgebraicSpace.isPullback_restrictHom_target_left : ∀ {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) (Z : LocallyClosedSubspace G.U.left)
    (hZ : G.IsLocallyClosedInvariant Z) ,
    IsPullback (restrict G Z).t.left (restrictHom G Z).arrow.left Z.ι G.t.left)

/- If `Z` is locally closed invariant, the restricted arrow space identifies with the inverse
image of `Z` along the source map. -/
#check (AlgebraicGeometry.GroupoidAlgebraicSpace.restrict_arrowIso_sourceInverseImage : ∀ {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) (Z : LocallyClosedSubspace G.U.left)
    (hZ : G.IsLocallyClosedInvariant Z) ,
    (restrict G Z).R.left ≅ Limits.pullback Z.ι G.s.left)

/- The comparison isomorphism to `s⁻¹(Z)` commutes with the maps to `G.R`. -/
#check (AlgebraicGeometry.GroupoidAlgebraicSpace.restrict_arrowIso_sourceInverseImage_hom_comp_snd : ∀ {S : Scheme.{u}}
    {B : AlgebraicSpace S} (G : GroupoidAlgebraicSpace B)
    (Z : LocallyClosedSubspace G.U.left) (hZ : G.IsLocallyClosedInvariant Z) ,
    (restrict_arrowIso_sourceInverseImage G Z hZ).hom ≫
      Limits.pullback.snd Z.ι G.s.left =
    (restrictHom G Z).arrow.left)

/- The comparison isomorphism to `s⁻¹(Z)` recovers the restricted source map. -/
#check (AlgebraicGeometry.GroupoidAlgebraicSpace.restrict_arrowIso_sourceInverseImage_hom_comp_fst : ∀ {S : Scheme.{u}}
    {B : AlgebraicSpace S} (G : GroupoidAlgebraicSpace B)
    (Z : LocallyClosedSubspace G.U.left) (hZ : G.IsLocallyClosedInvariant Z) ,
    (restrict_arrowIso_sourceInverseImage G Z hZ).hom ≫
      Limits.pullback.fst Z.ι G.s.left =
    (restrict G Z).s.left)

/- If `Z` is locally closed invariant, the restricted arrow space identifies with the inverse
image of `Z` along the target map. -/
#check (AlgebraicGeometry.GroupoidAlgebraicSpace.restrict_arrowIso_targetInverseImage : ∀ {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) (Z : LocallyClosedSubspace G.U.left)
    (hZ : G.IsLocallyClosedInvariant Z) ,
    (restrict G Z).R.left ≅ Limits.pullback Z.ι G.t.left)

/- The comparison isomorphism to `t⁻¹(Z)` commutes with the maps to `G.R`. -/
#check (AlgebraicGeometry.GroupoidAlgebraicSpace.restrict_arrowIso_targetInverseImage_hom_comp_snd : ∀ {S : Scheme.{u}}
    {B : AlgebraicSpace S} (G : GroupoidAlgebraicSpace B)
    (Z : LocallyClosedSubspace G.U.left) (hZ : G.IsLocallyClosedInvariant Z) ,
    (restrict_arrowIso_targetInverseImage G Z hZ).hom ≫
      Limits.pullback.snd Z.ι G.t.left =
    (restrictHom G Z).arrow.left)

/- The comparison isomorphism to `t⁻¹(Z)` recovers the restricted target map. -/
#check (AlgebraicGeometry.GroupoidAlgebraicSpace.restrict_arrowIso_targetInverseImage_hom_comp_fst : ∀ {S : Scheme.{u}}
    {B : AlgebraicSpace S} (G : GroupoidAlgebraicSpace B)
    (Z : LocallyClosedSubspace G.U.left) (hZ : G.IsLocallyClosedInvariant Z) ,
    (restrict_arrowIso_targetInverseImage G Z hZ).hom ≫
      Limits.pullback.fst Z.ι G.t.left =
    (restrict G Z).t.left)

end AlgebraicGeometry.GroupoidAlgebraicSpace
