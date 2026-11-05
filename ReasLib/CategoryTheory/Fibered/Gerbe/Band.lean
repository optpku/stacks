/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Fibered.Gerbe.Basic
public import ReasLib.CategoryTheory.Fibered.InGroupoids.AbelianAutomorphisms.Sections
public import ReasLib.CategoryTheory.Sites.Descent.HomSheaf.Automorphism
public import Mathlib.CategoryTheory.Sites.Over
import Mathlib.Tactic.CrossRefAttribute

/-!
# Bands of gerbes

The projection-level `Automorphism.IsAbelian` class is the canonical abelianity owner. It owns the
`CommGrpCat`/`AddCommGrpCat` automorphism sheaves and their conjugation maps. A band of a gerbe is a
global additive sheaf equipped, merely nonemptily, with local comparison isomorphisms compatible
with same-fiber conjugation. `Band.Comparison.IsCoherent` separately records compatibility with
base restriction, which is required for existence of a compatible global isomorphism. The raw
comparison data remains available for arbitrary prestacks in groupoids.
-/

@[expose] public section

universe uC vC uS vS

namespace CategoryTheory

/-! ## Projection-level band owner -/

namespace Functor.IsFibered.InGroupoids

variable {C' : Type uC} [Category.{vC} C']
variable {S' : Type uS} [Category.{vS} S']

/-! The restriction comparison below uses the composition isomorphism of the existing selected
cleavage. Its forward map is conjugation from `(g ≫ f)⁎x` to `g⁎(f⁎x)`; the inverse is
conjugation by the inverse composition isomorphism. No inverse is selected from an `IsIso` proof. -/

/-- The sectionwise canonical comparison for restriction of an automorphism sheaf. -/
noncomputable def Automorphism.addComm.sheaf.pullbackAppIso
    (p : S' ⥤ C') (J : GrothendieckTopology C')
    [Functor.IsFibered.InGroupoids p] [Automorphism.IsAbelian p]
    [Pseudofunctor.IsPrestack (Functor.fiberPseudofunctor p) J]
    {U V : C'} (f : V ⟶ U) (x : p.Fiber U) (T : (Over V)ᵒᵖ) :
    (((J.overMapPullback AddCommGrpCat f).obj
      (Automorphism.addComm.sheaf p J x)).1.obj T) ≅
      ((Automorphism.addComm.sheaf p J ((Functor.Chosen.reindex p f).obj x)).1.obj T) :=
  (Functor.Chosen.Reindex.compIsoApp p f T.unop.hom x).conj.toAdditive.toAddCommGrpIso

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The composition comparison commutes with restriction in the slice site. -/
theorem Automorphism.addComm.sheaf.pullbackAppIso_naturality
    (p : S' ⥤ C') (J : GrothendieckTopology C')
    [Functor.IsFibered.InGroupoids p] [Automorphism.IsAbelian p]
    [Pseudofunctor.IsPrestack (Functor.fiberPseudofunctor p) J]
    {U V : C'} (f : V ⟶ U) (x : p.Fiber U)
    {T T' : (Over V)ᵒᵖ} (g : T ⟶ T') :
    (((J.overMapPullback AddCommGrpCat f).obj
      (Automorphism.addComm.sheaf p J x)).1.map g) ≫
        (Automorphism.addComm.sheaf.pullbackAppIso p J f x T').hom =
      (Automorphism.addComm.sheaf.pullbackAppIso p J f x T).hom ≫
        (Automorphism.addComm.sheaf p J ((Functor.Chosen.reindex p f).obj x)).1.map g :=
  by
    have component (W : (Over V)ᵒᵖ)
        (b : (((Functor.fiberPseudofunctor p).presheafHom x x).obj
          ((Over.map f).op.obj W))) :
        (((Functor.fiberPseudofunctor p).overMapCompPresheafHomIso x x f).hom.app W) b =
          (Automorphism.addComm.sheaf.pullbackAppIso p J f x W).hom b := by
      dsimp [Pseudofunctor.overMapCompPresheafHomIso]
      simp only [Pseudofunctor.mapComp'_eq_mapComp]
      change ((Functor.Chosen.Reindex.compIsoApp p f W.unop.hom x).inv ≫ b) ≫
          (Functor.Chosen.Reindex.compIsoApp p f W.unop.hom x).hom =
        (Functor.Chosen.Reindex.compIsoApp p f W.unop.hom x).inv ≫ b ≫
          (Functor.Chosen.Reindex.compIsoApp p f W.unop.hom x).hom
      exact Category.assoc _ _ _
    ext a
    have h := ConcreteCategory.congr_hom
      (((Functor.fiberPseudofunctor p).overMapCompPresheafHomIso x x f).hom.naturality g) a
    change (((Functor.fiberPseudofunctor p).overMapCompPresheafHomIso x x f).hom.app T')
        (((Functor.fiberPseudofunctor p).presheafHom x x).map ((Over.map f).op.map g) a) =
      (((Functor.fiberPseudofunctor p).presheafHom
        ((Functor.Chosen.reindex p f).obj x) ((Functor.Chosen.reindex p f).obj x)).map g)
        ((((Functor.fiberPseudofunctor p).overMapCompPresheafHomIso x x f).hom.app T) a) at h
    rw [component, component] at h
    exact h

/-- The canonical pullback of an automorphism sheaf, with explicit maps in both directions. -/
noncomputable def Automorphism.addComm.sheaf.pullbackIso
    (p : S' ⥤ C') (J : GrothendieckTopology C')
    [Functor.IsFibered.InGroupoids p] [Automorphism.IsAbelian p]
    [Pseudofunctor.IsPrestack (Functor.fiberPseudofunctor p) J]
    {U V : C'} (f : V ⟶ U) (x : p.Fiber U) :
    (J.overMapPullback AddCommGrpCat f).obj (Automorphism.addComm.sheaf p J x) ≅
      Automorphism.addComm.sheaf p J ((Functor.Chosen.reindex p f).obj x) :=
  (fullyFaithfulSheafToPresheaf (J.over V) AddCommGrpCat).preimageIso
    (NatIso.ofComponents
      (Automorphism.addComm.sheaf.pullbackAppIso p J f x)
      (fun g ↦ Automorphism.addComm.sheaf.pullbackAppIso_naturality p J f x g))

/-- The pullback comparison acts on sections by conjugation by the cleavage composition map. -/
theorem Automorphism.addComm.sheaf.pullbackIso_hom_app
    (p : S' ⥤ C') (J : GrothendieckTopology C')
    [Functor.IsFibered.InGroupoids p] [Automorphism.IsAbelian p]
    [Pseudofunctor.IsPrestack (Functor.fiberPseudofunctor p) J]
    {U V : C'} (f : V ⟶ U) (x : p.Fiber U) (T : (Over V)ᵒᵖ) :
    (Automorphism.addComm.sheaf.pullbackIso p J f x).hom.hom.app T =
      (Automorphism.addComm.sheaf.pullbackAppIso p J f x T).hom := rfl

/-- The inverse pullback comparison has the explicit inverse conjugation formula. -/
theorem Automorphism.addComm.sheaf.pullbackIso_inv_app
    (p : S' ⥤ C') (J : GrothendieckTopology C')
    [Functor.IsFibered.InGroupoids p] [Automorphism.IsAbelian p]
    [Pseudofunctor.IsPrestack (Functor.fiberPseudofunctor p) J]
    {U V : C'} (f : V ⟶ U) (x : p.Fiber U) (T : (Over V)ᵒᵖ) :
    (Automorphism.addComm.sheaf.pullbackIso p J f x).inv.hom.app T =
      (Automorphism.addComm.sheaf.pullbackAppIso p J f x T).inv := rfl

namespace Band

/-- Lemma 8.11.8 (tag 0CJY), data layer: a comparison family from a global additive sheaf to the
canonical local automorphism sheaves, with its conjugation compatibility law. -/
@[stacks 0CJY "band comparison data"]
structure Comparison
    (p : S' ⥤ C') (J : GrothendieckTopology C')
    [Functor.IsFibered.InGroupoids p]
    [Automorphism.IsAbelian p]
    [Pseudofunctor.IsPrestack (Functor.fiberPseudofunctor p) J]
    (G : Sheaf J AddCommGrpCat.{vS}) where
  /-- The local comparison isomorphism over each base object and fiber object. -/
  iso : ∀ {U : C'} (x : p.Fiber U),
    G.over U ≅ Automorphism.addComm.sheaf p J x
  /-- Compatibility with conjugation by a fiber morphism. -/
  naturality : ∀ {U : C'} {x y : p.Fiber U} (φ : x ⟶ y),
    iso x ≪≫ Automorphism.addComm.sheaf.conjOfHom p J φ = iso y

attribute [stacks 0CJY "band local comparison isomorphism"]
  CategoryTheory.Functor.IsFibered.InGroupoids.Band.Comparison.iso
attribute [stacks 0CJY "band comparison conjugation compatibility"]
  CategoryTheory.Functor.IsFibered.InGroupoids.Band.Comparison.naturality

/-- Cross-base compatibility of a comparison family. This is additional to the same-fiber
condition in `Comparison`: after restriction along `f`, the comparison agrees with the one for
`f⁎x` through the canonical automorphism-sheaf pullback isomorphism. -/
def Comparison.IsCoherent
    {p : S' ⥤ C'} {J : GrothendieckTopology C'}
    [Functor.IsFibered.InGroupoids p] [Automorphism.IsAbelian p]
    [Pseudofunctor.IsPrestack (Functor.fiberPseudofunctor p) J]
    {G : Sheaf J AddCommGrpCat.{vS}} (c : Comparison p J G) : Prop :=
  ∀ {U V : C'} (f : V ⟶ U) (x : p.Fiber U),
    (J.overMapPullback AddCommGrpCat f).mapIso (c.iso x) ≪≫
        Automorphism.addComm.sheaf.pullbackIso p J f x =
      c.iso ((Functor.Chosen.reindex p f).obj x)

/-- An isomorphism between the global sheaves underlying two band comparisons is compatible when
its restriction identifies their local comparison isomorphisms. -/
@[stacks 0CJY "compatible isomorphism of band comparisons"]
def Comparison.IsCompatibleIso
    {p : S' ⥤ C'} {J : GrothendieckTopology C'}
    [Functor.IsFibered.InGroupoids p]
    [Automorphism.IsAbelian p]
    [Pseudofunctor.IsPrestack (Functor.fiberPseudofunctor p) J]
    {G H : Sheaf J AddCommGrpCat.{vS}}
    (c : Comparison p J G) (d : Comparison p J H) (e : G ≅ H) : Prop :=
  ∀ {U : C'} (x : p.Fiber U),
    (J.overPullback AddCommGrpCat U).mapIso e ≪≫ d.iso x = c.iso x

/-- The identity isomorphism is compatible with a band comparison. -/
@[stacks 0CJY "compatible band comparison reflexivity"]
theorem Comparison.IsCompatibleIso.refl
    {p : S' ⥤ C'} {J : GrothendieckTopology C'}
    [Functor.IsFibered.InGroupoids p]
    [Automorphism.IsAbelian p]
    [Pseudofunctor.IsPrestack (Functor.fiberPseudofunctor p) J]
    {G : Sheaf J AddCommGrpCat.{vS}} (c : Comparison p J G) :
    c.IsCompatibleIso c (Iso.refl G) := sorry

/-- The inverse of a compatible isomorphism is compatible in the reverse direction. -/
@[stacks 0CJY "compatible band comparison symmetry"]
theorem Comparison.IsCompatibleIso.symm
    {p : S' ⥤ C'} {J : GrothendieckTopology C'}
    [Functor.IsFibered.InGroupoids p]
    [Automorphism.IsAbelian p]
    [Pseudofunctor.IsPrestack (Functor.fiberPseudofunctor p) J]
    {G H : Sheaf J AddCommGrpCat.{vS}}
    {c : Comparison p J G} {d : Comparison p J H} {e : G ≅ H}
    (he : c.IsCompatibleIso d e) :
    d.IsCompatibleIso c e.symm := sorry

/-- Compatible isomorphisms of band comparisons compose. -/
@[stacks 0CJY "compatible band comparison transitivity"]
theorem Comparison.IsCompatibleIso.trans
    {p : S' ⥤ C'} {J : GrothendieckTopology C'}
    [Functor.IsFibered.InGroupoids p]
    [Automorphism.IsAbelian p]
    [Pseudofunctor.IsPrestack (Functor.fiberPseudofunctor p) J]
    {G H K : Sheaf J AddCommGrpCat.{vS}}
    {c : Comparison p J G} {d : Comparison p J H} {k : Comparison p J K}
    {e : G ≅ H} {f : H ≅ K}
    (he : c.IsCompatibleIso d e) (hf : d.IsCompatibleIso k f) :
    c.IsCompatibleIso k (e ≪≫ f) := sorry

/-- Two compatible isomorphisms for fixed weak comparison data coincide. Cross-base coherence
is needed for existence, but not for this at-most-one statement. -/
theorem Comparison.compatibleIso_eq
    {p : S' ⥤ C'} {J : GrothendieckTopology C'}
    [IsGerbe J p] [Automorphism.IsAbelian p]
    {G H : Sheaf J AddCommGrpCat.{vS}}
    (c : Comparison p J G) (d : Comparison p J H) (e e' : G ≅ H)
    (he : c.IsCompatibleIso d e) (he' : c.IsCompatibleIso d e') :
    e = e' := by
  apply Iso.ext
  apply Sheaf.hom_ext
  apply NatTrans.ext
  funext U
  obtain ⟨T, hT⟩ := IsGerbe.locallyInhabited (J := J) (p := p) U.unop
  apply H.property.hom_ext T
  intro I
  rw [← e.hom.hom.naturality I.f.op, ← e'.hom.hom.naturality I.f.op]
  congr 1
  obtain ⟨x⟩ := hT I
  have hlocal : (J.overPullback AddCommGrpCat I.Y).mapIso e =
      (J.overPullback AddCommGrpCat I.Y).mapIso e' := by
    apply Iso.ext
    apply (cancel_mono (d.iso x).hom).mp
    exact congrArg Iso.hom ((he x).trans (he' x).symm)
  exact congrArg (fun k ↦ k.hom.hom.app (Opposite.op (Over.mk (𝟙 I.Y)))) hlocal

/-- On a gerbe, two comparisons coherent under base restriction have a unique compatible
isomorphism. Same-fiber conjugation compatibility alone does not imply existence. -/
@[stacks 0CJY "uniqueness of a coherent band comparison"]
theorem Comparison.existsUniqueCompatibleIso
    {p : S' ⥤ C'} {J : GrothendieckTopology C'}
    [IsGerbe J p]
    [Automorphism.IsAbelian p]
    {G H : Sheaf J AddCommGrpCat.{vS}}
    (c : Comparison p J G) (d : Comparison p J H)
    (hc : c.IsCoherent) (hd : d.IsCoherent) :
    ∃! e : G ≅ H, c.IsCompatibleIso d e := sorry

/-- Read out a supplied compatible isomorphism. This data boundary deliberately takes the
isomorphism itself: the coherence existence theorem still has a proof obligation, so it must not
be used to synthesize morphisms with `Classical.choose`. -/
@[stacks 0CJY "supplied compatible isomorphism of band comparisons"]
def Comparison.compatibleIso
    {p : S' ⥤ C'} {J : GrothendieckTopology C'}
    [Functor.IsFibered.InGroupoids p] [Automorphism.IsAbelian p]
    [Pseudofunctor.IsPrestack (Functor.fiberPseudofunctor p) J]
    {G H : Sheaf J AddCommGrpCat.{vS}}
    (c : Comparison p J G) (d : Comparison p J H)
    (e : { e : G ≅ H // c.IsCompatibleIso d e }) : G ≅ H :=
  e.val

/-- Readout of supplied compatibility. -/
@[stacks 0CJY "specification of the supplied band comparison isomorphism"]
theorem Comparison.compatibleIso_spec
    {p : S' ⥤ C'} {J : GrothendieckTopology C'}
    [Functor.IsFibered.InGroupoids p] [Automorphism.IsAbelian p]
    [Pseudofunctor.IsPrestack (Functor.fiberPseudofunctor p) J]
    {G H : Sheaf J AddCommGrpCat.{vS}}
    (c : Comparison p J G) (d : Comparison p J H)
    (e : { e : G ≅ H // c.IsCompatibleIso d e }) :
    c.IsCompatibleIso d (c.compatibleIso d e) := e.property

/-- Any compatible isomorphism equals the supplied one for these comparison data. -/
@[stacks 0CJY "uniqueness of the supplied band comparison isomorphism"]
theorem Comparison.compatibleIso_unique
    {p : S' ⥤ C'} {J : GrothendieckTopology C'}
    [IsGerbe J p] [Automorphism.IsAbelian p]
    {G H : Sheaf J AddCommGrpCat.{vS}}
    (c : Comparison p J G) (d : Comparison p J H)
    (w : { e : G ≅ H // c.IsCompatibleIso d e })
    (e : G ≅ H) (he : c.IsCompatibleIso d e) :
    e = c.compatibleIso d w :=
  c.compatibleIso_eq d e w.val he w.property

end Band

/-- Lemma 8.11.8 (tag 0CJY), predicate layer: a global additive sheaf is a band for a gerbe when
it admits a compatible comparison family with the gerbe's canonical local automorphism sheaves. -/
@[stacks 0CJY "band of an abelian gerbe"]
def IsBand
    (p : S' ⥤ C') (J : GrothendieckTopology C')
    [IsGerbe J p]
    [Automorphism.IsAbelian p]
    (G : Sheaf J AddCommGrpCat.{vS}) : Prop :=
  Nonempty (Band.Comparison p J G)

/-- Package comparison data into the projection-level band predicate. -/
@[stacks 0CJY "constructing a band from comparison data"]
theorem IsBand.ofComparison
    {p : S' ⥤ C'} {J : GrothendieckTopology C'}
    [IsGerbe J p]
    [Automorphism.IsAbelian p]
    {G : Sheaf J AddCommGrpCat.{vS}} (comparison : Band.Comparison p J G) :
    IsBand p J G := ⟨comparison⟩

/-- Expose comparison data from a projection-level band. -/
@[stacks 0CJY "band comparison witness"]
theorem IsBand.existsComparison
    {p : S' ⥤ C'} {J : GrothendieckTopology C'}
    [IsGerbe J p]
    [Automorphism.IsAbelian p]
    {G : Sheaf J AddCommGrpCat.{vS}} (hBand : IsBand p J G) :
    Nonempty (Band.Comparison p J G) := hBand

/-- A named comparison selected from a band witness.

`IsBand` is intentionally proposition-valued, so this is a convenience boundary rather than a
canonical comparison.  Consumers that own comparison data should pass the
`Band.Comparison` directly or use `Band.Choice`; the result itself is the named
comparison readout, so clients need not unfold this choice. -/
@[stacks 0CJY "selected comparison from a band witness"]
noncomputable def IsBand.comparison
    {p : S' ⥤ C'} {J : GrothendieckTopology C'}
    [IsGerbe J p]
    [Automorphism.IsAbelian p]
    {G : Sheaf J AddCommGrpCat.{vS}}
    (hBand : IsBand p J G) : Band.Comparison p J G :=
  Classical.choice hBand

/-- Bands with coherent comparison witnesses have isomorphic underlying global sheaves.
The source-facing weak band predicate alone does not supply cross-base coherence. -/
@[stacks 0CJY "uniqueness of the band up to isomorphism"]
theorem IsBand.nonemptyIso
    {p : S' ⥤ C'} {J : GrothendieckTopology C'}
    [IsGerbe J p]
    [Automorphism.IsAbelian p]
    {G H : Sheaf J AddCommGrpCat.{vS}}
    (c : Band.Comparison p J G) (d : Band.Comparison p J H)
    (hc : c.IsCoherent) (hd : d.IsCoherent) :
    Nonempty (G ≅ H) := by
  obtain ⟨e, _, _⟩ := c.existsUniqueCompatibleIso d hc hd
  exact ⟨e⟩

end Functor.IsFibered.InGroupoids

namespace Functor.IsFibered.InGroupoids.Band

/-- Explicit band comparison data over a prestack.

`Band.Choice` is the reusable Type-valued owner: its sheaf and comparison family are supplied as
data under exactly the hypotheses needed by `Band.Comparison`. The gerbe predicate is added only
by the companion `Choice.isBand` theorem. It deliberately does not store a second proposition-
valued `IsBand` field, since that property is determined by `comparison`. -/
@[stacks 0CJY "explicit band data choice"]
structure Choice
    {C' : Type uC} [Category.{vC} C']
    {S' : Type uS} [Category.{vS} S']
    (p : S' ⥤ C') (J : GrothendieckTopology C')
    [Functor.IsFibered.InGroupoids p]
    [Automorphism.IsAbelian p]
    [Pseudofunctor.IsPrestack (Functor.fiberPseudofunctor p) J] where
  /-- The global additive sheaf carried by the chosen band. -/
  sheaf : Sheaf J AddCommGrpCat.{vS}
  /-- The compatible comparison with the local automorphism sheaves. -/
  comparison : Comparison p J sheaf

attribute [stacks 0CJY "explicit band sheaf"] Choice.sheaf
attribute [stacks 0CJY "explicit band comparison"] Choice.comparison

namespace Choice

/-- Package an already supplied comparison as explicit band data.

This constructor is the preferred data-owner route: no witness is selected from a proposition. -/
@[stacks 0CJY "band data from an explicit comparison"]
def ofComparison
    {C' : Type uC} [Category.{vC} C']
    {S' : Type uS} [Category.{vS} S']
    {J : GrothendieckTopology C'} {p : S' ⥤ C'}
    [Functor.IsFibered.InGroupoids p]
    [Automorphism.IsAbelian p]
    [Pseudofunctor.IsPrestack (Functor.fiberPseudofunctor p) J]
    {G : Sheaf J AddCommGrpCat.{vS}}
    (c : Comparison p J G) :
    Choice p J :=
  ⟨G, c⟩

/-- Package a proposition-level existence witness as one named band choice.

The existential is accepted in the shape `∃ G, Nonempty (Comparison ...)`, so this owner does not
re-run `IsBand.existsComparison` internally. Callers that have concrete comparison data should
prefer `ofComparison`. -/
@[stacks 0CJY "band data selected from existence"]
noncomputable def ofExists
    {C' : Type uC} [Category.{vC} C']
    {S' : Type uS} [Category.{vS} S']
    {J : GrothendieckTopology C'} {p : S' ⥤ C'}
    [Functor.IsFibered.InGroupoids p]
    [Automorphism.IsAbelian p]
    [Pseudofunctor.IsPrestack (Functor.fiberPseudofunctor p) J]
    (h : ∃ G : Sheaf J AddCommGrpCat.{vS},
      Nonempty (Comparison p J G)) :
    Choice p J where
  sheaf := Classical.choose h
  comparison := Classical.choice (Classical.choose_spec h)

/-- The comparison carried by explicit band data determines its band predicate. -/
@[stacks 0CJY "band data satisfies the band predicate"]
theorem isBand
    {C' : Type uC} [Category.{vC} C']
    {S' : Type uS} [Category.{vS} S']
    {J : GrothendieckTopology C'} {p : S' ⥤ C'}
    [IsGerbe J p]
    [Functor.IsFibered.InGroupoids.Automorphism.IsAbelian p]
    (B : Choice p J) :
    Functor.IsFibered.InGroupoids.IsBand p J B.sheaf := ⟨B.comparison⟩

/-- Read out a compatible isomorphism supplied for two explicit band choices. No data is
selected from the unproved coherent-comparison existence theorem. -/
@[stacks 0CJY "supplied comparison of explicit band choices"]
def comparisonIso
    {C' : Type uC} [Category.{vC} C']
    {S' : Type uS} [Category.{vS} S']
    {J : GrothendieckTopology C'} {p : S' ⥤ C'}
    [Functor.IsFibered.InGroupoids p]
    [Automorphism.IsAbelian p]
    [Pseudofunctor.IsPrestack (Functor.fiberPseudofunctor p) J]
    (B B' : Choice p J)
    (e : { e : B.sheaf ≅ B'.sheaf // B.comparison.IsCompatibleIso B'.comparison e }) :
    B.sheaf ≅ B'.sheaf :=
  B.comparison.compatibleIso B'.comparison e

/-- The supplied comparison between two band choices is compatible. -/
@[stacks 0CJY "specification of the supplied comparison of explicit band choices"]
theorem comparisonIso_spec
    {C' : Type uC} [Category.{vC} C']
    {S' : Type uS} [Category.{vS} S']
    {J : GrothendieckTopology C'} {p : S' ⥤ C'}
    [Functor.IsFibered.InGroupoids p]
    [Automorphism.IsAbelian p]
    [Pseudofunctor.IsPrestack (Functor.fiberPseudofunctor p) J]
    (B B' : Choice p J)
    (e : { e : B.sheaf ≅ B'.sheaf // B.comparison.IsCompatibleIso B'.comparison e }) :
    B.comparison.IsCompatibleIso B'.comparison (comparisonIso B B' e) := e.property

/-- Any compatible comparison between two band choices equals the supplied one. -/
@[stacks 0CJY "uniqueness of the supplied comparison of explicit band choices"]
theorem comparisonIso_unique
    {C' : Type uC} [Category.{vC} C']
    {S' : Type uS} [Category.{vS} S']
    {J : GrothendieckTopology C'} {p : S' ⥤ C'}
    [IsGerbe J p]
    [Functor.IsFibered.InGroupoids.Automorphism.IsAbelian p]
    (B B' : Choice p J)
    (w : { e : B.sheaf ≅ B'.sheaf // B.comparison.IsCompatibleIso B'.comparison e })
    (e : B.sheaf ≅ B'.sheaf)
    (he : B.comparison.IsCompatibleIso B'.comparison e) :
    e = comparisonIso B B' w :=
  B.comparison.compatibleIso_eq B'.comparison e w.val he w.property

end Choice

end Functor.IsFibered.InGroupoids.Band

/-- Lemma 8.11.8: an abelian gerbe admits a global sheaf band. -/
@[stacks 0CJY]
theorem IsGerbe.existsBand
    {C' : Type uC} [Category.{vC} C']
    {S' : Type uS} [Category.{vS} S']
    {J : GrothendieckTopology C'} {p : S' ⥤ C'}
    [IsGerbe J p]
    [Functor.IsFibered.InGroupoids.Automorphism.IsAbelian p] :
    ∃ G : Sheaf J AddCommGrpCat.{vS},
      Functor.IsFibered.InGroupoids.IsBand p J G := sorry

namespace IsGerbe

/-- An abelian gerbe admits comparison data in the explicit shape used by `Band.Choice`.

This is a proposition-level bridge from the source existential theorems. Keeping it separate
means the Type-valued `Band.Choice.ofExists` owner can also be used with independently supplied
comparison data. -/
@[stacks 0CJY "existence of explicit band comparison data"]
theorem existsBandComparison
    {C' : Type uC} [Category.{vC} C']
    {S' : Type uS} [Category.{vS} S']
    {J : GrothendieckTopology C'} {p : S' ⥤ C'}
    [IsGerbe J p]
    [Functor.IsFibered.InGroupoids.Automorphism.IsAbelian p] :
    ∃ G : Sheaf J AddCommGrpCat.{vS},
      Nonempty (Functor.IsFibered.InGroupoids.Band.Comparison p J G) :=
  IsGerbe.existsBand (J := J) (p := p)

/-- A convenient selected band obtained from the gerbe existence theorem.

This is intentionally documented as noncanonical: its mathematical content is the explicit
`Band.Choice` owner and its same-fiber comparison API, while this definition only gives callers
an easy default value. It does not assert `Comparison.IsCoherent`; a coherent band producer and a
proved construction of comparison isomorphisms remain separate obligations. -/
@[stacks 0CJY "convenient selected band choice"]
noncomputable def bandChoice
    {C' : Type uC} [Category.{vC} C']
    {S' : Type uS} [Category.{vS} S']
    {J : GrothendieckTopology C'} {p : S' ⥤ C'}
    [IsGerbe J p]
    [Functor.IsFibered.InGroupoids.Automorphism.IsAbelian p] :
    Functor.IsFibered.InGroupoids.Band.Choice p J :=
  Functor.IsFibered.InGroupoids.Band.Choice.ofExists
    (existsBandComparison (J := J) (p := p))

/-- The convenient selected band satisfies the band predicate. -/
@[stacks 0CJY "specification of the convenient selected band"]
theorem bandChoice_spec
    {C' : Type uC} [Category.{vC} C']
    {S' : Type uS} [Category.{vS} S']
    {J : GrothendieckTopology C'} {p : S' ⥤ C'}
    [IsGerbe J p]
    [Functor.IsFibered.InGroupoids.Automorphism.IsAbelian p] :
    Functor.IsFibered.InGroupoids.IsBand p J (bandChoice (J := J) (p := p)).sheaf :=
  ⟨(bandChoice (J := J) (p := p)).comparison⟩

/- Data audit: `Band.Choice` and `ofComparison` carry only caller-supplied non-Prop data. Any
reported `sorryAx` is inherited from Prop-valued category, functor, and coherence laws in the field
types; no sheaf or comparison is synthesized by a placeholder. `ofExists` and `bandChoice` are
explicit convenience boundaries around proposition-level existence. In particular `bandChoice`
still depends on the existing unproved `IsGerbe.existsBand`; it is not a proved band producer.
The supplied-isomorphism readouts above do not use this existence theorem. -/

end IsGerbe

/- Axiom audit: `Band.Comparison` stores caller-supplied isomorphisms. Its inherited `sorryAx`
dependency comes from Prop-valued functor, sheaf, and coherence laws in the types of the canonical
automorphism sheaves; no comparison object or morphism is generated by a placeholder. -/

end CategoryTheory
