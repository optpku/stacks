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
global additive sheaf equipped, merely nonemptily, with compatible local comparison isomorphisms.
The raw comparison data remains available for arbitrary prestacks in groupoids, while the gerbe
hypotheses own its choice-independence API.
-/

@[expose] public section

universe uC vC uS vS

namespace CategoryTheory

/-! ## Projection-level band owner -/

namespace Functor.IsFibered.InGroupoids

variable {C' : Type uC} [Category.{vC} C']
variable {S' : Type uS} [Category.{vS} S']

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

/-- On a gerbe, any two band comparisons are identified by a unique compatible isomorphism of
their global sheaves. -/
@[stacks 0CJY "uniqueness of a band comparison"]
theorem Comparison.existsUniqueCompatibleIso
    {p : S' ⥤ C'} {J : GrothendieckTopology C'}
    [IsGerbe J p]
    [Automorphism.IsAbelian p]
    {G H : Sheaf J AddCommGrpCat.{vS}}
    (c : Comparison p J G) (d : Comparison p J H) :
    ∃! e : G ≅ H, c.IsCompatibleIso d e := sorry

/-- The selected compatible isomorphism between two band comparisons.

This is a convenience owner for the unique witness in
`Comparison.existsUniqueCompatibleIso`.  The comparison data themselves remain explicit; this
definition only packages the propositionally unique bridge so that downstream constructions do
not repeat `Classical.choose` at every use site. -/
@[stacks 0CJY "selected compatible isomorphism of band comparisons"]
noncomputable def Comparison.compatibleIso
    {p : S' ⥤ C'} {J : GrothendieckTopology C'}
    [IsGerbe J p]
    [Automorphism.IsAbelian p]
    {G H : Sheaf J AddCommGrpCat.{vS}}
    (c : Comparison p J G) (d : Comparison p J H) : G ≅ H :=
  Classical.choose (Comparison.existsUniqueCompatibleIso c d)

/-- The selected compatible isomorphism satisfies the comparison compatibility condition. -/
@[stacks 0CJY "specification of the selected band comparison isomorphism"]
theorem Comparison.compatibleIso_spec
    {p : S' ⥤ C'} {J : GrothendieckTopology C'}
    [IsGerbe J p]
    [Automorphism.IsAbelian p]
    {G H : Sheaf J AddCommGrpCat.{vS}}
    (c : Comparison p J G) (d : Comparison p J H) :
    c.IsCompatibleIso d (c.compatibleIso d) := sorry

/-- Any compatible isomorphism between two band comparisons equals the selected one. -/
@[stacks 0CJY "uniqueness of the selected band comparison isomorphism"]
theorem Comparison.compatibleIso_unique
    {p : S' ⥤ C'} {J : GrothendieckTopology C'}
    [IsGerbe J p]
    [Automorphism.IsAbelian p]
    {G H : Sheaf J AddCommGrpCat.{vS}}
    (c : Comparison p J G) (d : Comparison p J H)
    (e : G ≅ H) (he : c.IsCompatibleIso d e) :
    e = c.compatibleIso d := sorry

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
    IsBand p J G := sorry

/-- Expose comparison data from a projection-level band. -/
@[stacks 0CJY "band comparison witness"]
theorem IsBand.existsComparison
    {p : S' ⥤ C'} {J : GrothendieckTopology C'}
    [IsGerbe J p]
    [Automorphism.IsAbelian p]
    {G : Sheaf J AddCommGrpCat.{vS}} (hBand : IsBand p J G) :
    Nonempty (Band.Comparison p J G) := sorry

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
  Classical.choice (IsBand.existsComparison hBand)

/-- Any two bands of the same abelian gerbe have isomorphic underlying global sheaves. -/
@[stacks 0CJY "uniqueness of the band up to isomorphism"]
theorem IsBand.nonemptyIso
    {p : S' ⥤ C'} {J : GrothendieckTopology C'}
    [IsGerbe J p]
    [Automorphism.IsAbelian p]
    {G H : Sheaf J AddCommGrpCat.{vS}}
    (hG : IsBand p J G) (hH : IsBand p J H) :
    Nonempty (G ≅ H) := sorry

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
    Functor.IsFibered.InGroupoids.IsBand p J B.sheaf := sorry

/-- The comparison isomorphism between two explicit band choices.

It is induced by the unique compatible isomorphism of their stored comparison families; no
additional sheaf or comparison data is selected here. -/
@[stacks 0CJY "comparison of explicit band choices"]
noncomputable def comparisonIso
    {C' : Type uC} [Category.{vC} C']
    {S' : Type uS} [Category.{vS} S']
    {J : GrothendieckTopology C'} {p : S' ⥤ C'}
    [IsGerbe J p]
    [Functor.IsFibered.InGroupoids.Automorphism.IsAbelian p]
    (B B' : Choice p J) : B.sheaf ≅ B'.sheaf :=
  B.comparison.compatibleIso B'.comparison

/-- The comparison between two band choices is compatible with their local comparison families. -/
@[stacks 0CJY "specification of the comparison of explicit band choices"]
theorem comparisonIso_spec
    {C' : Type uC} [Category.{vC} C']
    {S' : Type uS} [Category.{vS} S']
    {J : GrothendieckTopology C'} {p : S' ⥤ C'}
    [IsGerbe J p]
    [Functor.IsFibered.InGroupoids.Automorphism.IsAbelian p]
    (B B' : Choice p J) :
    B.comparison.IsCompatibleIso B'.comparison (comparisonIso B B') := sorry

/-- Any compatible comparison between two band choices equals `comparisonIso`. -/
@[stacks 0CJY "uniqueness of the comparison of explicit band choices"]
theorem comparisonIso_unique
    {C' : Type uC} [Category.{vC} C']
    {S' : Type uS} [Category.{vS} S']
    {J : GrothendieckTopology C'} {p : S' ⥤ C'}
    [IsGerbe J p]
    [Functor.IsFibered.InGroupoids.Automorphism.IsAbelian p]
    (B B' : Choice p J) (e : B.sheaf ≅ B'.sheaf)
    (he : B.comparison.IsCompatibleIso B'.comparison e) :
    e = comparisonIso B B' := sorry

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
      Nonempty (Functor.IsFibered.InGroupoids.Band.Comparison p J G) := sorry

/-- A convenient selected band obtained from the gerbe existence theorem.

This is intentionally documented as noncanonical: its mathematical content is the explicit
`Band.Choice` owner and its comparison-independence API, while this definition only gives callers
an easy default value. -/
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
    Functor.IsFibered.InGroupoids.IsBand p J (bandChoice (J := J) (p := p)).sheaf := sorry

/- Data audit: `Band.Choice` and `ofComparison` carry only caller-supplied non-Prop data. Any
reported `sorryAx` is inherited from Prop-valued category, functor, and coherence laws in the field
types; no sheaf or comparison is synthesized by a placeholder. `ofExists` and `bandChoice` are
explicit convenience boundaries around proposition-level existence; clients should consume their
named fields and specification/uniqueness theorems rather than unfold `Classical.choice`. -/

end IsGerbe

/- Axiom audit: `Band.Comparison` stores caller-supplied isomorphisms. Its inherited `sorryAx`
dependency comes from Prop-valued functor, sheaf, and coherence laws in the types of the canonical
automorphism sheaves; no comparison object or morphism is generated by a placeholder. -/

end CategoryTheory
