/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.CommAlg.TensorWithObject.Derived.Adjunction
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.CommAlg.TensorWithObject.Derived.SelfExt
public import ReasLib.CategoryTheory.Pretriangulated.Functor.FullyFaithful

/-!
# Full faithfulness of coefficient-generic derived tensoring

The regular object compactly generates the derived category of right DG modules.  The
derived tensor-representable adjunction and the regular self-Ext comparison therefore give a
compact-generator criterion for full faithfulness over any commutative coefficient ring.
-/

@[expose] public section

noncomputable section

universe r u v w z

open CategoryTheory CategoryTheory.Limits
open CategoryTheory.Pretriangulated
open DifferentialGradedCategory
open scoped DifferentialGradedCategory SheafOfModules.CommAlg

namespace SheafOfModules.CommAlg.TensorWithObject.Derived

variable {R : Type r} [CommRing R]
variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ (CommAlgCat.{w} R) CommRingCat.{w})]
variable [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
variable [UnivLE.{max u v, max u z}]
variable [HasWeakSheafify J AddCommGrpCat.{max u z}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{max u z}]
variable {O : Sheaf J (CommAlgCat.{w} R)}

/-- The universe bounds needed to apply the compact-generator criterion to derived tensoring
with `K`.  This named specialization keeps category-universe formulas out of downstream theorem
signatures.  In normalized universe configurations the bound can be inferred as an ambient class;
for arbitrary coefficient or sheaf universes, construct it explicitly at the category level and
pass it to `fullyFaithful_withBounds` (or to the generic
`Functor.FullyFaithful.ofCompactGenerator_withBounds`). -/
@[stacks 09LZ "universe bounds for derived tensor full faithfulness"]
abbrev GeneratorBounds (K : Complex.{r, u, v, w, max u z} O) : Prop :=
  Functor.CompactGeneratorBounds
    (DifferentialGradedModule.Derived.Category.{r, max u z} (endDGA K))
    (DerivedCategory
      (SheafOfModules.CommAlg.Modules.{r, u, v, w, max u z} O))

namespace FullyFaithful

/-- Computing self-Ext makes derived tensor fully faithful on all shifts of the regular generator.
-/
@[stacks 09LZ "arbitrary-ring full faithfulness on regular shifts"]
theorem regularShifts
    (K : Complex.{r, u, v, w, max u z} O)
    (h_ext : CategoryTheory.CochainComplex.Enriched.Over.RHom.ComputesSelfExt
      (R := R) K) :
    (tensorFunctor K).IsFullyFaithfulOnSelfShifts
      (DifferentialGradedModule.Derived.regularObject (endDGA K)) := sorry

end FullyFaithful

/-- Lemma 22.35.6 (09LZ): if `K` is compact and its enriched Hom complex computes all shifted
self-Ext groups, then `- ⊗ᴸ_(endDGA K) K` is fully faithful. -/
@[stacks 09LZ "fully faithful arbitrary-ring derived tensor with a compact complex"]
noncomputable def fullyFaithful_withBounds
    (K : Complex.{r, u, v, w, max u z} O) [HasRepresentable K]
    (h_bounds : GeneratorBounds K)
    (h_compact : IsCompactObject (DerivedCategory.Q.obj K))
    (h_ext : CategoryTheory.CochainComplex.Enriched.Over.RHom.ComputesSelfExt
      (R := R) K) :
    (tensorFunctor K).FullyFaithful :=
  Functor.FullyFaithful.ofCompactGenerator_withBounds
    (C := DifferentialGradedModule.Derived.Category.{r, max u z} (endDGA K))
    (D := DerivedCategory
      (SheafOfModules.CommAlg.Modules.{r, u, v, w, max u z} O))
    (F := tensorFunctor K) (G := representableFunctor K)
    h_bounds
    (adjunction K)
    (DifferentialGradedModule.Derived.regularObject (endDGA K))
    (DifferentialGradedModule.Derived.regularObject_isLocalizingGenerator (endDGA K))
    (DifferentialGradedModule.Derived.regularObject_shifts_isDetecting (endDGA K))
    (DifferentialGradedModule.Derived.regularObject_isCompact (endDGA K))
    (regularImage_isCompact K h_compact)
    (FullyFaithful.regularShifts K h_ext)

/-- The instance-based wrapper is the concise path when the ambient bounds are inferable. -/
@[stacks 09LZ "fully faithful arbitrary-ring derived tensor with inferred bounds"]
noncomputable def fullyFaithful
    (K : Complex.{r, u, v, w, max u z} O) [HasRepresentable K]
    [h_bounds : GeneratorBounds K]
    (h_compact : IsCompactObject (DerivedCategory.Q.obj K))
    (h_ext : CategoryTheory.CochainComplex.Enriched.Over.RHom.ComputesSelfExt
      (R := R) K) :
    (tensorFunctor K).FullyFaithful :=
  fullyFaithful_withBounds K h_bounds h_compact h_ext

end SheafOfModules.CommAlg.TensorWithObject.Derived
