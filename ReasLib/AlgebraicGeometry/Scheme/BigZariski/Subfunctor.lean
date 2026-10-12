/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Mathlib.AlgebraicGeometry.Sites.BigZariski
public import Mathlib.CategoryTheory.Limits.Shapes.Products
public import Mathlib.CategoryTheory.MorphismProperty.Representable
public import Mathlib.CategoryTheory.Sites.LocallySurjective
public import Mathlib.CategoryTheory.Subfunctor.Basic
public import Mathlib.Topology.Sets.OpenCover
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Open subfunctors and covers in the big Zariski topology
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace
open scoped AlgebraicGeometry

universe u v w

namespace AlgebraicGeometry.Scheme.BigZariski.Subfunctor

variable {F : Scheme.{u}ᵒᵖ ⥤ Type v}

/-- An open subscheme `U ⊆ T` represents membership in `H` after pulling back the section `ξ`
when a morphism to `T` factors through `U` exactly when the pulled-back section belongs to `H`.
This is the specification owner for the canonical representing-open API. -/
@[stacks 01JI "representing-open specification"]
def RepresentsOpen (H : CategoryTheory.Subfunctor F) {T : Scheme.{u}}
    (ξ : F.obj (op T)) (U : T.Opens) : Prop :=
  ∀ ⦃T' : Scheme.{u}⦄ (f : T' ⟶ T),
    (∃ lift : T' ⟶ U.toScheme, lift ≫ U.ι = f) ↔
      F.map f.op ξ ∈ H.obj (op T')

/-- Membership in a subfunctor is equivalent to factorization through a representing open. -/
@[stacks 01JI "representing-open membership readout"]
theorem RepresentsOpen.mem_iff {H : CategoryTheory.Subfunctor F} {T : Scheme.{u}}
    {ξ : F.obj (op T)} {U : T.Opens} (hU : RepresentsOpen H ξ U)
    {T' : Scheme.{u}} (f : T' ⟶ T) :
    F.map f.op ξ ∈ H.obj (op T') ↔
      ∃ lift : T' ⟶ U.toScheme, lift ≫ U.ι = f := sorry

/-- Membership in a represented open subfunctor gives a unique factorization through the
representing open. -/
@[stacks 01JI "unique representing-open factorization"]
theorem RepresentsOpen.mem_iff_existsUnique_lift
    {H : CategoryTheory.Subfunctor F} {T : Scheme.{u}}
    {ξ : F.obj (op T)} {U : T.Opens} (hU : RepresentsOpen H ξ U)
    {T' : Scheme.{u}} (f : T' ⟶ T) :
    F.map f.op ξ ∈ H.obj (op T') ↔
      ∃! lift : T' ⟶ U.toScheme, lift ≫ U.ι = f := sorry

/-- Pulling back a representing open preserves its membership specification. -/
@[stacks 01JI "pullback of a representing open"]
theorem RepresentsOpen.preimage {H : CategoryTheory.Subfunctor F} {T T' : Scheme.{u}}
    {ξ : F.obj (op T)} {U : T.Opens} (hU : RepresentsOpen H ξ U) (f : T' ⟶ T) :
    RepresentsOpen H (F.map f.op ξ) (f ⁻¹ᵁ U) := sorry

/-- A subfunctor is Zariski open when pullback membership is represented by an
open subscheme for every section. -/
@[stacks 01JI]
def IsZariskiOpen (H : CategoryTheory.Subfunctor F) : Prop :=
  ∀ ⦃T : Scheme.{u}⦄ (ξ : F.obj (op T)), ∃ U : T.Opens, RepresentsOpen H ξ U

/-- Two opens representing membership in the same subfunctor for the same section are equal. -/
@[stacks 01JI "uniqueness of a representing open"]
theorem RepresentsOpen.eq {H : CategoryTheory.Subfunctor F} {T : Scheme.{u}}
    {ξ : F.obj (op T)} {U V : T.Opens}
    (hU : RepresentsOpen H ξ U) (hV : RepresentsOpen H ξ V) : U = V := sorry

/-- The canonical representing open supplied by a Zariski-open subfunctor. Its defining choice is
exposed only through `representingOpen_spec` and the uniqueness API below. -/
@[stacks 01JI "representing open of a Zariski-open subfunctor"]
noncomputable def IsZariskiOpen.representingOpen
    {H : CategoryTheory.Subfunctor F} (hH : IsZariskiOpen H)
    {T : Scheme.{u}} (ξ : F.obj (op T)) : T.Opens :=
  Classical.choose (hH ξ)

/-- The canonical representing open has the required pullback-membership specification. -/
@[stacks 01JI "canonical representing-open specification"]
theorem IsZariskiOpen.representingOpen_spec
    {H : CategoryTheory.Subfunctor F} (hH : IsZariskiOpen H)
    {T : Scheme.{u}} (ξ : F.obj (op T)) :
    RepresentsOpen H ξ (hH.representingOpen ξ) := sorry

/-- Pullback membership in a Zariski-open subfunctor is equivalent to factorization through its
canonical representing open. -/
@[stacks 01JI "membership through the representing open"]
theorem IsZariskiOpen.map_mem_iff
    {H : CategoryTheory.Subfunctor F} (hH : IsZariskiOpen H)
    {T T' : Scheme.{u}} (ξ : F.obj (op T)) (f : T' ⟶ T) :
    F.map f.op ξ ∈ H.obj (op T') ↔
      ∃ lift : T' ⟶ (hH.representingOpen ξ).toScheme,
        lift ≫ (hH.representingOpen ξ).ι = f := sorry

/-- Pullback membership in a Zariski-open subfunctor gives a unique factorization through its
canonical representing open. -/
@[stacks 01JI "unique factorization through the canonical representing open"]
theorem IsZariskiOpen.map_mem_iff_existsUnique_lift
    {H : CategoryTheory.Subfunctor F} (hH : IsZariskiOpen H)
    {T T' : Scheme.{u}} (ξ : F.obj (op T)) (f : T' ⟶ T) :
    F.map f.op ξ ∈ H.obj (op T') ↔
      ∃! lift : T' ⟶ (hH.representingOpen ξ).toScheme,
        lift ≫ (hH.representingOpen ξ).ι = f := sorry

/-- A section restricts to the open that represents its membership in a Zariski-open
subfunctor. -/
@[stacks 01JI "membership on the representing open"]
theorem IsZariskiOpen.representingOpen_ι_mem
    {H : CategoryTheory.Subfunctor F} (hH : IsZariskiOpen H)
    {T : Scheme.{u}} (ξ : F.obj (op T)) :
    F.map (hH.representingOpen ξ).ι.op ξ ∈
      H.obj (op (hH.representingOpen ξ).toScheme) := sorry

/-- The open representing a pulled-back section is the inverse image of the original
representing open. -/
@[stacks 01JI "representing opens commute with pullback"]
theorem IsZariskiOpen.representingOpen_map
    {H : CategoryTheory.Subfunctor F} (hH : IsZariskiOpen H)
    {T T' : Scheme.{u}} (f : T' ⟶ T) (ξ : F.obj (op T)) :
    hH.representingOpen (F.map f.op ξ) = f ⁻¹ᵁ hH.representingOpen ξ := sorry

/-- Any open with the pullback-membership specification is the canonical representing open. -/
@[stacks 01JI "characterization of the canonical representing open"]
theorem RepresentsOpen.eq_representingOpen
    {H : CategoryTheory.Subfunctor F} (hH : IsZariskiOpen H)
    {T : Scheme.{u}} {ξ : F.obj (op T)} {U : T.Opens}
    (hU : RepresentsOpen H ξ U) : U = hH.representingOpen ξ := sorry

/-- The representing open is independent of the proof that the subfunctor is Zariski open. -/
@[stacks 01JI "proof independence of the representing open"]
theorem IsZariskiOpen.representingOpen_eq
    {H : CategoryTheory.Subfunctor F} (hH hH' : IsZariskiOpen H)
    {T : Scheme.{u}} (ξ : F.obj (op T)) :
    hH.representingOpen ξ = hH'.representingOpen ξ := sorry

/-- For same-universe functors, Zariski openness is equivalent to relative
representability of the inclusion by open immersions. -/
@[stacks 01JI]
theorem isZariskiOpen_iff_presheaf
    {F : Scheme.{u}ᵒᵖ ⥤ Type u} (H : CategoryTheory.Subfunctor F) :
    IsZariskiOpen H ↔ IsOpenImmersion.presheaf H.ι := sorry

variable {I : Type w}

/-- An indexed family is a Zariski cover when every section locally belongs to
the correspondingly indexed subfunctor. -/
@[stacks 01JI]
def IsZariskiCover (H : I → CategoryTheory.Subfunctor F) : Prop :=
  ∀ ⦃T : Scheme.{u}⦄ (ξ : F.obj (op T)),
    ∃ U : I → T.Opens, IsOpenCover U ∧
      ∀ i, F.map (U i).ι.op ξ ∈ (H i).obj (op (U i).toScheme)

/-- A nonempty constant family of maximal subfunctors is a Zariski cover. -/
@[stacks 01JI]
theorem isZariskiCover_top [Nonempty I] :
    IsZariskiCover (fun _ : I ↦ (⊤ : CategoryTheory.Subfunctor F)) := sorry

/-- An index-preserving Zariski cover makes the coproduct of its inclusions
locally surjective. -/
@[stacks 01JI]
theorem IsZariskiCover.sigmaDesc_isLocallySurjective
    {H : I → CategoryTheory.Subfunctor F} [Small.{v} I]
    (hH : IsZariskiCover H) :
    Presheaf.IsLocallySurjective Scheme.zariskiTopology
      (Limits.Sigma.desc (fun i ↦ (H i).ι)) := sorry

end AlgebraicGeometry.Scheme.BigZariski.Subfunctor
