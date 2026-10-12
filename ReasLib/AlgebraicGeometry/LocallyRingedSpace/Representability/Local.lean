/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.LocallyRingedSpace.Representability.OpenCover
public import ReasLib.AlgebraicGeometry.LocallyRingedSpace.Representability.OnSchemes
public import ReasLib.AlgebraicGeometry.LocallyRingedSpace.ZariskiTopology
public import ReasLib.AlgebraicGeometry.Scheme.BigZariski.Representability
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Local representability criteria on locally ringed spaces

This leaf packages the locally-ringed-space forms of the open-immersion and
covering predicates, their restriction to schemes, and the resulting local
representability criterion.
-/

@[expose] public section

open CategoryTheory Opposite TopologicalSpace
open AlgebraicGeometry.LocallyRingedSpace.Hom
open CategoryTheory.Functor CategoryTheory.Subfunctor

universe u v w

namespace AlgebraicGeometry.LocallyRingedSpace.BigZariski.Subfunctor

variable {F : LocallyRingedSpace.{u}ᵒᵖ ⥤ Type v}

/-- An open restriction `X|_U` represents membership in `H` after pulling back the section `ξ`
when a morphism to `X` factors through `X|_U` exactly when the pulled-back section belongs to
`H`. This is the specification owner for the locally-ringed-space representing-open API. -/
@[stacks 01JK "locally-ringed-space representing-open specification"]
def RepresentsOpen (H : CategoryTheory.Subfunctor F) {X : LocallyRingedSpace.{u}}
    (ξ : F.obj (op X)) (U : Opens X) : Prop :=
  ∀ ⦃Y : LocallyRingedSpace.{u}⦄ (f : Y ⟶ X),
    (∃ lift : Y ⟶ X.restrict U.isOpenEmbedding,
      lift ≫ X.ofRestrict U.isOpenEmbedding = f) ↔
        F.map f.op ξ ∈ H.obj (op Y)

/-- Membership in a subfunctor is equivalent to factorization through a representing open. -/
@[stacks 01JK "locally-ringed-space representing-open membership readout"]
theorem RepresentsOpen.mem_iff {H : CategoryTheory.Subfunctor F}
    {X : LocallyRingedSpace.{u}} {ξ : F.obj (op X)} {U : Opens X}
    (hU : RepresentsOpen H ξ U) {Y : LocallyRingedSpace.{u}} (f : Y ⟶ X) :
    F.map f.op ξ ∈ H.obj (op Y) ↔
      ∃ lift : Y ⟶ X.restrict U.isOpenEmbedding,
        lift ≫ X.ofRestrict U.isOpenEmbedding = f := sorry

/-- Membership in a represented open subfunctor gives a unique factorization through the
representing open restriction. -/
@[stacks 01JK "unique locally-ringed-space representing-open factorization"]
theorem RepresentsOpen.mem_iff_existsUnique_lift
    {H : CategoryTheory.Subfunctor F}
    {X : LocallyRingedSpace.{u}} {ξ : F.obj (op X)} {U : Opens X}
    (hU : RepresentsOpen H ξ U) {Y : LocallyRingedSpace.{u}} (f : Y ⟶ X) :
    F.map f.op ξ ∈ H.obj (op Y) ↔
      ∃! lift : Y ⟶ X.restrict U.isOpenEmbedding,
        lift ≫ X.ofRestrict U.isOpenEmbedding = f := sorry

/-- Pulling back a representing open preserves its membership specification. -/
@[stacks 01JK "locally-ringed-space pullback of a representing open"]
theorem RepresentsOpen.preimage {H : CategoryTheory.Subfunctor F}
    {X Y : LocallyRingedSpace.{u}} {ξ : F.obj (op X)} {U : Opens X}
    (hU : RepresentsOpen H ξ U) (f : Y ⟶ X) :
    RepresentsOpen H (F.map f.op ξ) (f.preimageOpen U) := sorry

/-- A subfunctor of a locally-ringed-space functor is represented by open immersions when pullback
membership is detected by factorization through a chosen open restriction. -/
@[stacks 01JK "Zariski-open subfunctor on locally ringed spaces"]
def IsZariskiOpen (H : CategoryTheory.Subfunctor F) : Prop :=
  ∀ ⦃X : LocallyRingedSpace.{u}⦄ (ξ : F.obj (op X)),
    ∃ U : Opens X, RepresentsOpen H ξ U

/-- Two opens representing membership in the same subfunctor for the same locally-ringed-space
section are equal. -/
@[stacks 01JK]
theorem RepresentsOpen.eq {H : CategoryTheory.Subfunctor F}
    {X : LocallyRingedSpace.{u}} {ξ : F.obj (op X)} {U V : Opens X}
    (hU : RepresentsOpen H ξ U) (hV : RepresentsOpen H ξ V) :
    U = V := sorry

/-- The canonical representing open restriction supplied by a Zariski-open subfunctor. Its
defining choice is exposed only through the specification and uniqueness API below. -/
@[stacks 01JK "representing open of an LRS Zariski-open subfunctor"]
noncomputable def IsZariskiOpen.representingOpen
    {H : CategoryTheory.Subfunctor F} (hH : IsZariskiOpen H)
    {X : LocallyRingedSpace.{u}} (ξ : F.obj (op X)) : Opens X :=
  Classical.choose (hH ξ)

/-- The canonical representing open restriction has the required pullback-membership
specification. -/
@[stacks 01JK]
theorem IsZariskiOpen.representingOpen_spec
    {H : CategoryTheory.Subfunctor F} (hH : IsZariskiOpen H)
    {X : LocallyRingedSpace.{u}} (ξ : F.obj (op X)) :
    RepresentsOpen H ξ (hH.representingOpen ξ) := sorry

/-- Pullback membership in a Zariski-open subfunctor is equivalent to factorization through its
canonical representing open restriction. -/
@[stacks 01JK]
theorem IsZariskiOpen.map_mem_iff
    {H : CategoryTheory.Subfunctor F} (hH : IsZariskiOpen H)
    {X Y : LocallyRingedSpace.{u}} (ξ : F.obj (op X)) (f : Y ⟶ X) :
    F.map f.op ξ ∈ H.obj (op Y) ↔
      ∃ lift : Y ⟶ X.restrict (hH.representingOpen ξ).isOpenEmbedding,
        lift ≫ X.ofRestrict (hH.representingOpen ξ).isOpenEmbedding = f := sorry

/-- Pullback membership in a Zariski-open subfunctor gives a unique factorization through its
canonical representing open restriction. -/
@[stacks 01JK "unique factorization through the canonical LRS representing open"]
theorem IsZariskiOpen.map_mem_iff_existsUnique_lift
    {H : CategoryTheory.Subfunctor F} (hH : IsZariskiOpen H)
    {X Y : LocallyRingedSpace.{u}} (ξ : F.obj (op X)) (f : Y ⟶ X) :
    F.map f.op ξ ∈ H.obj (op Y) ↔
      ∃! lift : Y ⟶ X.restrict (hH.representingOpen ξ).isOpenEmbedding,
        lift ≫ X.ofRestrict (hH.representingOpen ξ).isOpenEmbedding = f := sorry

/-- A section restricts to the open restriction that represents its membership in a
Zariski-open subfunctor. -/
@[stacks 01JK "membership on the representing open restriction"]
theorem IsZariskiOpen.representingOpen_ofRestrict_mem
    {H : CategoryTheory.Subfunctor F} (hH : IsZariskiOpen H)
    {X : LocallyRingedSpace.{u}} (ξ : F.obj (op X)) :
    F.map (X.ofRestrict (hH.representingOpen ξ).isOpenEmbedding).op ξ ∈
      H.obj (op (X.restrict (hH.representingOpen ξ).isOpenEmbedding)) := sorry

/-- The open representing a pulled-back section is the inverse image of the original
representing open. -/
@[stacks 01JK "representing open restrictions commute with pullback"]
theorem IsZariskiOpen.representingOpen_map
    {H : CategoryTheory.Subfunctor F} (hH : IsZariskiOpen H)
    {X Y : LocallyRingedSpace.{u}} (f : Y ⟶ X) (ξ : F.obj (op X)) :
    hH.representingOpen (F.map f.op ξ) =
      f.preimageOpen (hH.representingOpen ξ) := sorry

/-- Any open restriction with the pullback-membership specification is the canonical
representing open. -/
@[stacks 01JK]
theorem RepresentsOpen.eq_representingOpen
    {H : CategoryTheory.Subfunctor F} (hH : IsZariskiOpen H)
    {X : LocallyRingedSpace.{u}} {ξ : F.obj (op X)} {U : Opens X}
    (hU : RepresentsOpen H ξ U) :
    U = hH.representingOpen ξ := sorry

/-- The representing open restriction is independent of the proof that the subfunctor is
Zariski open. -/
@[stacks 01JK]
theorem IsZariskiOpen.representingOpen_eq
    {H : CategoryTheory.Subfunctor F} (hH hH' : IsZariskiOpen H)
    {X : LocallyRingedSpace.{u}} (ξ : F.obj (op X)) :
    hH.representingOpen ξ = hH'.representingOpen ξ := sorry

/-- A family of subfunctors covers a locally-ringed-space functor when every section belongs to a
member of the family after restriction along an open cover. -/
@[stacks 01JK "Zariski cover on locally ringed spaces"]
def IsZariskiCover {I : Type w} (H : I → CategoryTheory.Subfunctor F) : Prop :=
  ∀ ⦃X : LocallyRingedSpace.{u}⦄ (ξ : F.obj (op X)),
    ∃ U : I → Opens X, IsOpenCover U ∧
      ∀ i : I,
        F.map (X.ofRestrict (U i).isOpenEmbedding).op ξ ∈
          (H i).obj (op (X.restrict (U i).isOpenEmbedding))

/-- A nonempty constant family of maximal subfunctors is a Zariski cover. -/
@[stacks 01JK "maximal subfunctors cover"]
theorem isZariskiCover_top {I : Type w} [Nonempty I] :
    IsZariskiCover (fun _ : I ↦ (⊤ : CategoryTheory.Subfunctor F)) := sorry

/-- The source-facing open-subfunctor predicate is equivalent to relative representability of the
inclusion by open immersions. -/
@[stacks 01JK "canonical open-subfunctor bridge"]
theorem isZariskiOpen_iff_presheaf
    {F : LocallyRingedSpace.{u}ᵒᵖ ⥤ Type u} (H : CategoryTheory.Subfunctor F) :
    IsZariskiOpen H ↔ LocallyRingedSpace.openImmersionProperty.presheaf H.ι := sorry

/-- A source-facing Zariski cover makes the coproduct of its inclusions locally surjective for the
canonical locally-ringed-space Zariski topology. -/
@[stacks 01JK "canonical Zariski-cover bridge"]
theorem IsZariskiCover.sigmaDesc_isLocallySurjective
    {I : Type w} [Small.{v} I] {H : I → CategoryTheory.Subfunctor F}
    (hH : IsZariskiCover H) :
    Presheaf.IsLocallySurjective LocallyRingedSpace.zariskiTopology
      (Limits.Sigma.desc (fun i ↦ (H i).ι)) := sorry

/-- A Zariski-open subfunctor on locally ringed spaces restricts to a Zariski-open subfunctor on
schemes. -/
@[stacks 01JK "representing-open restriction to schemes"]
theorem RepresentsOpen.onSchemes
    {H : CategoryTheory.Subfunctor F} {X : Scheme.{u}}
    {ξ : F.obj (op X.toLocallyRingedSpace)} {U : X.Opens}
    (hU : RepresentsOpen H ξ U) :
    Scheme.BigZariski.Subfunctor.RepresentsOpen H.onSchemes ξ U := sorry

/-- A Zariski-open subfunctor on locally ringed spaces restricts to a Zariski-open subfunctor on
schemes. -/
@[stacks 01JK]
theorem IsZariskiOpen.onSchemes
    {H : CategoryTheory.Subfunctor F} (hH : IsZariskiOpen H) :
    Scheme.BigZariski.Subfunctor.IsZariskiOpen H.onSchemes := sorry

/-- A representing open chosen in the LRS layer agrees with a scheme-side choice. -/
@[stacks 01JK "representing-open choice compatibility on schemes"]
theorem IsZariskiOpen.representingOpen_onSchemes
    {H : CategoryTheory.Subfunctor F} (hH : IsZariskiOpen H)
    {X : Scheme.{u}} (ξ : F.obj (op X.toLocallyRingedSpace)) :
    Scheme.BigZariski.Subfunctor.IsZariskiOpen.representingOpen
      (IsZariskiOpen.onSchemes hH) ξ = hH.representingOpen ξ := sorry

/-- A Zariski cover on locally ringed spaces restricts to a Zariski cover on schemes. -/
@[stacks 01JK]
theorem IsZariskiCover.onSchemes
    {I : Type w} {H : I → CategoryTheory.Subfunctor F} (hH : IsZariskiCover H) :
    Scheme.BigZariski.Subfunctor.IsZariskiCover (fun i ↦ (H i).onSchemes) := sorry

end AlgebraicGeometry.LocallyRingedSpace.BigZariski.Subfunctor

namespace CategoryTheory.Functor

/-- The explicit gluing condition for canonical open restrictions is equivalent to the canonical
Zariski sheaf condition on locally ringed spaces. -/
@[stacks 01JK "canonical locally-ringed-space sheaf bridge"]
theorem openCoverGluing_iff_isSheaf
    (F : AlgebraicGeometry.LocallyRingedSpace.{u}ᵒᵖ ⥤ Type v) :
    F.openCoverGluing ↔
      Presheaf.IsSheaf AlgebraicGeometry.LocallyRingedSpace.zariskiTopology F := sorry

end CategoryTheory.Functor

namespace AlgebraicGeometry.LocallyRingedSpace.LocalRepresentability

/-- The locally-ringed-space open-cover gluing condition restricts to the canonical Zariski sheaf
condition on schemes. -/
@[stacks 01JK]
theorem onSchemes_isSheaf
    (F : AlgebraicGeometry.LocallyRingedSpace.{u}ᵒᵖ ⥤ Type v)
    (hFsheaf : F.openCoverGluing) :
    Presheaf.IsSheaf Scheme.zariskiTopology F.onSchemes := sorry

/-- A locally-ringed-space functor is represented by a scheme when it satisfies open-cover gluing
and is locally covered by scheme-representable subfunctors with open-immersion inclusions. -/
@[stacks 01JK "local representability on locally ringed spaces"]
theorem ofSubfunctorCover
    (F : AlgebraicGeometry.LocallyRingedSpace.{u}ᵒᵖ ⥤ Type u)
    {I : Type v} [Small.{u} I] (H : I → CategoryTheory.Subfunctor F)
    (hFsheaf : F.openCoverGluing)
    (hHrep : ∀ i, (H i).IsRepresentableByScheme)
    (hHopen : ∀ i, BigZariski.Subfunctor.IsZariskiOpen (H i))
    (hHcover : BigZariski.Subfunctor.IsZariskiCover H) :
    F.IsRepresentableByScheme := sorry

end AlgebraicGeometry.LocallyRingedSpace.LocalRepresentability
