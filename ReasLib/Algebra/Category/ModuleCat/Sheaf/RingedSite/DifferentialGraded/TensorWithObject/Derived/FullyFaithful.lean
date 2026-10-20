/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.DifferentialGraded.TensorWithObject.Derived.Adjunction
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.DifferentialGraded.TensorWithObject.Derived.SelfExt
public import ReasLib.CategoryTheory.Pretriangulated.Functor.FullyFaithful

/-!
# Full faithfulness of derived tensoring

The regular object compactly generates the derived category of right DG modules.  Combining the
derived tensor-representable adjunction with the self-Ext comparison therefore upgrades
compactness of `K` and self-Ext computation to a fully faithful derived tensor functor.
-/

@[expose] public section

noncomputable section

universe u v

open CategoryTheory CategoryTheory.Limits
open CategoryTheory.Pretriangulated
open CategoryTheory.CochainComplex.Enriched
open DifferentialGradedCategory
open scoped DifferentialGradedCategory

namespace SheafOfModules.RingedSite.TensorWithObject.Derived

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat.{max u v} RingCat.{max u v})]
variable {O : Sheaf J CommRingCat.{max u v}}

namespace FullyFaithful

/-- Computing self-Ext makes derived tensor fully faithful on all shifts of the canonical
regular generator. -/
@[stacks 09LZ "full faithfulness on regular shifts"]
theorem regularShifts
    (K : Complex (J := J) (O := O))
    (h_ext : CochainComplex.Enriched.ComputesSelfExt K) :
    (tensorFunctor K).IsFullyFaithfulOnSelfShifts
      (DifferentialGradedModule.Derived.regularObject (endDGA K)) := sorry

end FullyFaithful

/-- Lemma 22.35.6 (09LZ): if `K` is compact and its endomorphism Hom complex computes its
self-Ext groups, then `- ⊗^L_(endDGA K) K` is fully faithful. -/
@[stacks 09LZ "fully faithful derived tensor with a compact complex"]
noncomputable def fullyFaithful
    (K : Complex (J := J) (O := O))
    (h_compact : IsCompactObject (DerivedCategory.Q.obj K))
    (h_ext : CochainComplex.Enriched.ComputesSelfExt K) :
    (tensorFunctor K).FullyFaithful :=
  Functor.FullyFaithful.ofCompactGenerator_of_bounds
    (C := DifferentialGradedModule.Derived.Category (endDGA K))
    (D := RingedSiteDerived.max J O)
    (F := tensorFunctor K) (G := representableFunctor K)
    (adjunction K)
    (DifferentialGradedModule.Derived.regularObject (endDGA K))
    (DifferentialGradedModule.Derived.regularObject_isLocalizingGenerator (endDGA K))
    (DifferentialGradedModule.Derived.regularObject_shifts_isDetecting (endDGA K))
    (DifferentialGradedModule.Derived.regularObject_isCompact (endDGA K))
    (regularImage_isCompact K h_compact)
    (FullyFaithful.regularShifts K h_ext)

end SheafOfModules.RingedSite.TensorWithObject.Derived
