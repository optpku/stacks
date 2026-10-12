/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Geometry.RingedSpace.OpenImmersion
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Restriction to open subspaces

This file owns the canonical morphisms between nested open restrictions and characterizes
restriction of a locally ringed-space morphism to compatible opens. The canonical maps are
explicit open-immersion lifts; proposition-valued statements record their factorization,
uniqueness, and functorial laws.
-/

@[expose] public section

noncomputable section

universe u

namespace AlgebraicGeometry.LocallyRingedSpace

open CategoryTheory TopologicalSpace

/-- The canonical morphism from the restriction to `U` to the restriction to a larger open `V`. -/
@[stacks 01HI "nested open restriction"]
noncomputable def homOfLE {X : LocallyRingedSpace.{u}} {U V : Opens X} (h : U ≤ V) :
    X.restrict U.isOpenEmbedding ⟶ X.restrict V.isOpenEmbedding :=
  IsOpenImmersion.lift
    (X.ofRestrict V.isOpenEmbedding)
    (X.ofRestrict U.isOpenEmbedding)
    (fun _ ⟨y, hy⟩ ↦ ⟨⟨y.1, h y.2⟩, hy⟩)

namespace homOfLE

/-- Composing the morphism between nested restrictions with the larger inclusion recovers the
smaller inclusion into the ambient locally ringed space. -/
@[reassoc (attr := simp), stacks 01HI]
theorem comp_ofRestrict {X : LocallyRingedSpace.{u}} {U V : Opens X} (h : U ≤ V) :
    homOfLE h ≫ X.ofRestrict V.isOpenEmbedding = X.ofRestrict U.isOpenEmbedding := sorry

/-- A morphism between nested open restrictions is an open immersion. -/
@[stacks 01HI "nested restriction is an open immersion"]
instance isOpenImmersion {X : LocallyRingedSpace.{u}} {U V : Opens X} (h : U ≤ V) :
    IsOpenImmersion (homOfLE h) := sorry

/-- The morphism from an open restriction to itself is the identity. -/
@[simp, stacks 01HI]
theorem refl {X : LocallyRingedSpace.{u}} (U : Opens X) :
    homOfLE (le_rfl : U ≤ U) = 𝟙 _ := sorry

/-- Morphisms between nested open restrictions compose according to transitivity of inclusion. -/
@[simp, stacks 01HI]
theorem comp {X : LocallyRingedSpace.{u}} {U V W : Opens X}
    (hUV : U ≤ V) (hVW : V ≤ W) :
    homOfLE hUV ≫ homOfLE hVW = homOfLE (hUV.trans hVW) := sorry

end homOfLE

/-- The canonical morphism from the restriction to `U ⊓ V` to the restriction to `U`. -/
@[stacks 01HI "left overlap restriction"]
noncomputable abbrev overlapToLeft {X : LocallyRingedSpace.{u}} (U V : Opens X) :
    X.restrict (U ⊓ V).isOpenEmbedding ⟶ X.restrict U.isOpenEmbedding :=
  homOfLE inf_le_left

/-- The canonical morphism from the restriction to `U ⊓ V` to the restriction to `V`. -/
@[stacks 01HI "right overlap restriction"]
noncomputable abbrev overlapToRight {X : LocallyRingedSpace.{u}} (U V : Opens X) :
    X.restrict (U ⊓ V).isOpenEmbedding ⟶ X.restrict V.isOpenEmbedding :=
  homOfLE inf_le_right

/-- Composing `overlapToLeft U V` with the inclusion into `X` gives the inclusion of `U ⊓ V`. -/
@[reassoc (attr := simp), stacks 01HI]
theorem overlapToLeft_fac {X : LocallyRingedSpace.{u}} (U V : Opens X) :
    overlapToLeft U V ≫ X.ofRestrict U.isOpenEmbedding =
      X.ofRestrict (U ⊓ V).isOpenEmbedding := sorry

/-- Composing `overlapToRight U V` with the inclusion into `X` gives the inclusion of `U ⊓ V`. -/
@[reassoc (attr := simp), stacks 01HI]
theorem overlapToRight_fac {X : LocallyRingedSpace.{u}} (U V : Opens X) :
    overlapToRight U V ≫ X.ofRestrict V.isOpenEmbedding =
      X.ofRestrict (U ⊓ V).isOpenEmbedding := sorry

end AlgebraicGeometry.LocallyRingedSpace

namespace AlgebraicGeometry.LocallyRingedSpace.Hom

open CategoryTheory TopologicalSpace

variable {X Y : LocallyRingedSpace.{u}}

/-- The inverse image of an open subset along a locally ringed-space morphism. -/
@[stacks 01HI "inverse-image open"]
abbrev preimageOpen (f : X ⟶ Y) (V : Opens Y) : Opens X :=
  (Opens.map f.base).obj V

/-- A morphism between open restrictions is a restriction of `f` when its composite with the
target-open inclusion is the ambient composite through `f`. -/
@[stacks 01HI "restriction to open subspaces"]
def IsOpenRestriction (f : X ⟶ Y) (U : Opens X) (V : Opens Y)
    (fUV : X.restrict U.isOpenEmbedding ⟶ Y.restrict V.isOpenEmbedding) : Prop :=
  fUV ≫ Y.ofRestrict V.isOpenEmbedding =
    X.ofRestrict U.isOpenEmbedding ≫ f

/-- Unfolding the restriction relation. -/
@[simp, stacks 01HI]
theorem isOpenRestriction_iff (f : X ⟶ Y) (U : Opens X) (V : Opens Y)
    (fUV : X.restrict U.isOpenEmbedding ⟶ Y.restrict V.isOpenEmbedding) :
    f.IsOpenRestriction U V fUV ↔
      fUV ≫ Y.ofRestrict V.isOpenEmbedding =
        X.ofRestrict U.isOpenEmbedding ≫ f := sorry

/-- The composite from `X|_U` to `Y` has image in `V` when `U ≤ f⁻¹(V)`. -/
@[stacks 01HI "restriction range condition"]
theorem restrictToOpen.range_subset (f : X ⟶ Y) (U : Opens X) (V : Opens Y)
    (hUV : U ≤ f.preimageOpen V) :
    Set.range ((X.ofRestrict U.isOpenEmbedding ≫ f).base) ⊆
      Set.range (Y.ofRestrict V.isOpenEmbedding).base := sorry

/-- The canonical restriction of a morphism on a source open through an arbitrary target open
immersion containing its image. -/
@[stacks 01HI "restriction through an open immersion"]
noncomputable def restrictToOpenImmersion
    {T : LocallyRingedSpace.{u}} (f : X ⟶ Y) (U : Opens X) (j : T ⟶ Y)
    [IsOpenImmersion j]
    (hU : Set.range ((X.ofRestrict U.isOpenEmbedding ≫ f).base) ⊆
      Set.range j.base) :
    X.restrict U.isOpenEmbedding ⟶ T :=
  IsOpenImmersion.lift j (X.ofRestrict U.isOpenEmbedding ≫ f) hU

namespace restrictToOpenImmersion

/-- Restriction through an open immersion recovers the ambient morphism after composing with
that immersion. -/
@[reassoc (attr := simp), stacks 01HI]
theorem fac
    {T : LocallyRingedSpace.{u}} (f : X ⟶ Y) (U : Opens X) (j : T ⟶ Y)
    [IsOpenImmersion j]
    (hU : Set.range ((X.ofRestrict U.isOpenEmbedding ≫ f).base) ⊆
      Set.range j.base) :
    f.restrictToOpenImmersion U j hU ≫ j =
      X.ofRestrict U.isOpenEmbedding ≫ f := sorry

/-- A factorization through the same target open immersion is the canonical restriction. -/
@[stacks 01HI "restriction through an open immersion uniqueness"]
theorem unique
    {T : LocallyRingedSpace.{u}} (f : X ⟶ Y) (U : Opens X) (j : T ⟶ Y)
    [IsOpenImmersion j]
    (hU : Set.range ((X.ofRestrict U.isOpenEmbedding ≫ f).base) ⊆
      Set.range j.base)
    {g : X.restrict U.isOpenEmbedding ⟶ T}
    (hg : g ≫ j = X.ofRestrict U.isOpenEmbedding ≫ f) :
    g = f.restrictToOpenImmersion U j hU := sorry

end restrictToOpenImmersion

/-- The canonical restriction of `f : X ⟶ Y` from `U` to `V`, obtained by specializing
`restrictToOpenImmersion` to the standard target-open inclusion. -/
@[stacks 01HI "canonical restriction to open subspaces"]
noncomputable def restrictToOpen (f : X ⟶ Y) (U : Opens X) (V : Opens Y)
    (hUV : U ≤ f.preimageOpen V) :
    X.restrict U.isOpenEmbedding ⟶ Y.restrict V.isOpenEmbedding :=
  f.restrictToOpenImmersion U (Y.ofRestrict V.isOpenEmbedding)
    (fun _ ⟨x, hx⟩ ↦ ⟨⟨f.base x.1, hUV x.2⟩, hx⟩)

namespace restrictToOpen

/-- Restriction to opens factors the ambient open inclusions through `f`. -/
@[reassoc (attr := simp), stacks 01HI]
theorem fac (f : X ⟶ Y) (U : Opens X) (V : Opens Y)
    (hUV : U ≤ f.preimageOpen V) :
    f.restrictToOpen U V hUV ≫ Y.ofRestrict V.isOpenEmbedding =
      X.ofRestrict U.isOpenEmbedding ≫ f := sorry

/-- The canonical restriction satisfies the open-restriction relation. -/
@[stacks 01HI]
theorem isOpenRestriction (f : X ⟶ Y) (U : Opens X) (V : Opens Y)
    (hUV : U ≤ f.preimageOpen V) :
    f.IsOpenRestriction U V (f.restrictToOpen U V hUV) := sorry

/-- Every restriction satisfying the ambient factorization is the canonical restriction. -/
@[stacks 01HI "canonical restriction uniqueness"]
theorem unique (f : X ⟶ Y) (U : Opens X) (V : Opens Y)
    (hUV : U ≤ f.preimageOpen V)
    {fUV : X.restrict U.isOpenEmbedding ⟶ Y.restrict V.isOpenEmbedding}
    (hfUV : f.IsOpenRestriction U V fUV) :
    fUV = f.restrictToOpen U V hUV := sorry

/-- A morphism carrying `U` into `V` has a unique restriction between the
corresponding open subspaces. -/
@[stacks 01HI]
theorem existsUnique (f : X ⟶ Y) (U : Opens X) (V : Opens Y)
    (hUV : U ≤ f.preimageOpen V) :
    ∃! fUV : X.restrict U.isOpenEmbedding ⟶ Y.restrict V.isOpenEmbedding,
      f.IsOpenRestriction U V fUV := sorry

end restrictToOpen

/-- Two restrictions of the same morphism to the same source and target opens are equal. -/
@[stacks 01HI]
theorem IsOpenRestriction.eq {f : X ⟶ Y} {U : Opens X} {V : Opens Y}
    {fUV gUV : X.restrict U.isOpenEmbedding ⟶ Y.restrict V.isOpenEmbedding}
    (hf : f.IsOpenRestriction U V fUV) (hg : f.IsOpenRestriction U V gUV) :
    fUV = gUV := sorry

/-- The canonical morphism between nested restrictions is the restriction of the identity
morphism on the ambient locally ringed space. -/
@[stacks 01HI]
theorem IsOpenRestriction.homOfLE {U V : Opens X} (h : U ≤ V) :
    IsOpenRestriction (𝟙 X) U V (LocallyRingedSpace.homOfLE h) := sorry

/-- Inclusion `U ≤ V` induces inclusion into the inverse image of `V` under the identity. -/
@[stacks 01HI]
theorem preimageOpen.le_id {U V : Opens X} (h : U ≤ V) :
    U ≤ preimageOpen (𝟙 X) V := sorry

/-- The inverse image of an open along the identity is the same open. -/
@[simp, stacks 01HI "identity inverse-image open"]
theorem preimageOpen.id (V : Opens X) :
    preimageOpen (𝟙 X) V = V := sorry

/-- Restricting the identity morphism along `U ≤ V` is the canonical morphism between the two
open restrictions. -/
@[simp, stacks 01HI]
theorem restrictToOpen.id {U V : Opens X} (h : U ≤ V) :
    restrictToOpen (𝟙 X) U V (preimageOpen.le_id h) =
      LocallyRingedSpace.homOfLE h := sorry

/-- Compatible inclusions remain compatible after composition. -/
@[stacks 01HI]
theorem preimageOpen.comp_le
    {Z : LocallyRingedSpace.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    {U : Opens X} {V : Opens Y} {W : Opens Z}
    (hUV : U ≤ f.preimageOpen V) (hVW : V ≤ g.preimageOpen W) :
    U ≤ (f ≫ g).preimageOpen W := sorry

/-- Inverse-image opens compose contravariantly with locally ringed-space morphisms. -/
@[simp, stacks 01HI "composition of inverse-image opens"]
theorem preimageOpen.comp
    {Z : LocallyRingedSpace.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (W : Opens Z) :
    (f ≫ g).preimageOpen W = f.preimageOpen (g.preimageOpen W) := sorry

/-- The composite of restrictions is a restriction of the composite ambient morphism. -/
@[stacks 01HI]
theorem IsOpenRestriction.comp
    {Z : LocallyRingedSpace.{u}} {f : X ⟶ Y} {g : Y ⟶ Z}
    {U : Opens X} {V : Opens Y} {W : Opens Z}
    {fUV : X.restrict U.isOpenEmbedding ⟶ Y.restrict V.isOpenEmbedding}
    {gVW : Y.restrict V.isOpenEmbedding ⟶ Z.restrict W.isOpenEmbedding}
    (hf : f.IsOpenRestriction U V fUV)
    (hg : g.IsOpenRestriction V W gVW) :
    (f ≫ g).IsOpenRestriction U W (fUV ≫ gVW) := sorry

/-- Restriction of a composite agrees with composition of the canonical restrictions. -/
@[reassoc, stacks 01HI]
theorem restrictToOpen.comp
    {Z : LocallyRingedSpace.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (U : Opens X) (V : Opens Y) (W : Opens Z)
    (hUV : U ≤ f.preimageOpen V) (hVW : V ≤ g.preimageOpen W) :
    f.restrictToOpen U V hUV ≫ g.restrictToOpen V W hVW =
      (f ≫ g).restrictToOpen U W
        (preimageOpen.comp_le f g hUV hVW) := sorry

/-- The canonical restriction of `f` to the inverse image of `V`. -/
@[stacks 01HI "restriction to an inverse-image open"]
noncomputable abbrev restrictToPreimageOpen (f : X ⟶ Y) (V : Opens Y) :
    X.restrict (f.preimageOpen V).isOpenEmbedding ⟶
      Y.restrict V.isOpenEmbedding :=
  f.restrictToOpen (f.preimageOpen V) V le_rfl

namespace restrictToPreimageOpen

/-- The inverse-image restriction factors the target-open inclusion through `f`. -/
@[reassoc (attr := simp), stacks 01HI]
theorem fac (f : X ⟶ Y) (V : Opens Y) :
    f.restrictToPreimageOpen V ≫ Y.ofRestrict V.isOpenEmbedding =
      X.ofRestrict (f.preimageOpen V).isOpenEmbedding ≫ f := sorry

/-- The inverse-image restriction satisfies its canonical open-restriction specification. -/
@[stacks 01HI]
theorem isOpenRestriction (f : X ⟶ Y) (V : Opens Y) :
    f.IsOpenRestriction (f.preimageOpen V) V (f.restrictToPreimageOpen V) := sorry

/-- Any morphism satisfying the inverse-image restriction specification is canonical. -/
@[stacks 01HI "inverse-image restriction uniqueness"]
theorem unique (f : X ⟶ Y) (V : Opens Y)
    {fV : X.restrict (f.preimageOpen V).isOpenEmbedding ⟶
      Y.restrict V.isOpenEmbedding}
    (hfV : f.IsOpenRestriction (f.preimageOpen V) V fV) :
    fV = f.restrictToPreimageOpen V := sorry

/-- Successive inverse-image restrictions agree with restriction of a composite. -/
@[reassoc, stacks 01HI]
theorem comp
    {Z : LocallyRingedSpace.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (W : Opens Z) :
    f.restrictToPreimageOpen (g.preimageOpen W) ≫ g.restrictToPreimageOpen W =
      (f ≫ g).restrictToPreimageOpen W := sorry

/-- The inverse-image open `f⁻¹(V)` has a unique restriction morphism to `V`. -/
@[stacks 01HI "restriction to an inverse-image open"]
theorem existsUnique (f : X ⟶ Y) (V : Opens Y) :
    ∃! fV : X.restrict (f.preimageOpen V).isOpenEmbedding ⟶
        Y.restrict V.isOpenEmbedding,
      f.IsOpenRestriction (f.preimageOpen V) V fV := sorry

end restrictToPreimageOpen

end AlgebraicGeometry.LocallyRingedSpace.Hom
