/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.Localization.BasicOpen
import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Finite Principal-Open Covers

`PrimeSpectrum.StandardOpenCoverOf f` is the concrete finite family of
principal opens covering `D(f)`.  Its API supplies the induced localization
restriction maps and the equivalent spanning criterion.
-/

noncomputable section

universe u v w

namespace PrimeSpectrum

section

variable {R : Type u} [CommSemiring R]

/-- A standard open cover of `D(f)` is a family of principal opens whose
supremum is `D(f)`, together with its finite index type and the explicit
finiteness witness `U.finiteIndex` for a cover `U`. -/
@[stacks 01HT]
structure StandardOpenCoverOf (f : R) where
  /-- The finite index type of the covering family. -/
  index : Type v
  /-- The covering family has finitely many members. -/
  finiteIndex : Finite index
  /-- The element defining each principal open in the cover. -/
  generator : index → R
  /-- The associated principal opens cover `D(f)`. -/
  cover : basicOpen f = ⨆ i, basicOpen (generator i)

/-- The localized unit-ideal criterion constructs the covering equality for a family of
principal opens contained in `D(f)`. -/
@[stacks 01HT "standard-open cover equality from generators"]
theorem StandardOpenCoverOf.cover_eq_iSup_of_span_eq_top
    {f : R} {ι : Type v} (generator : ι → R)
    (le : ∀ i, basicOpen (generator i) ≤ basicOpen f)
    (span_eq_top :
      Ideal.span
        (Set.range fun i : ι ↦
          algebraMap R (Localization.Away f) (generator i)) = ⊤) :
    basicOpen f = ⨆ i, basicOpen (generator i) := sorry

/-- Construct a standard open cover from a finite family contained in `D(f)` whose localized
generators span the unit ideal. -/
@[stacks 01HT "standard open cover constructor"]
def StandardOpenCoverOf.ofGenerator
    {f : R} {ι : Type v} [Finite ι] (generator : ι → R)
    (le : ∀ i, basicOpen (generator i) ≤ basicOpen f)
    (span_eq_top :
      Ideal.span
        (Set.range fun i : ι ↦
          algebraMap R (Localization.Away f) (generator i)) = ⊤) :
    StandardOpenCoverOf f where
  index := ι
  finiteIndex := inferInstance
  generator := generator
  cover := StandardOpenCoverOf.cover_eq_iSup_of_span_eq_top generator le span_eq_top

/-- The family of principal opens underlying a standard open cover. -/
@[stacks 01HT "standard-open cover family"]
def StandardOpenCoverOf.opens {f : R} (U : StandardOpenCoverOf f) :
    U.index → TopologicalSpace.Opens (PrimeSpectrum R) :=
  fun i ↦ basicOpen (U.generator i)

/-- Evaluation of the family underlying a standard open cover. -/
@[simp, stacks 01HT "standard-open cover family evaluation"]
theorem StandardOpenCoverOf.opens_apply {f : R} (U : StandardOpenCoverOf f)
    (i : U.index) :
    U.opens i = basicOpen (U.generator i) := sorry

/-- The principal opens in a standard open cover have supremum `D(f)`. -/
@[stacks 01HT "standard-open cover supremum"]
theorem StandardOpenCoverOf.iSup_eq {f : R} (U : StandardOpenCoverOf f) :
    (⨆ i, U.opens i) = basicOpen f := sorry

/-- Each member of a standard open cover of `D(f)` is contained in `D(f)`. -/
@[stacks 01HT "standard-open cover containment"]
theorem StandardOpenCoverOf.le {f : R} (U : StandardOpenCoverOf f) (i : U.index) :
    U.opens i ≤ basicOpen f := sorry

/-- The restriction `R`-algebra homomorphism between localizations attached to
a member of a standard open cover. -/
@[stacks 01HT "standard-open restriction algebra map"]
noncomputable abbrev StandardOpenCoverOf.restrictionAlgHom {f : R}
    (U : StandardOpenCoverOf f) (i : U.index) :
    Localization.Away f →ₐ[R] Localization.Away (U.generator i) :=
  awayToAwayAlgHom f (U.generator i)
    (U.cover ▸ le_iSup (fun j ↦ basicOpen (U.generator j)) i)

/-- The restriction homomorphism between localizations attached to a member of
a standard open cover. -/
@[stacks 01HT "standard-open restriction ring map"]
noncomputable abbrev StandardOpenCoverOf.restrictionRingHom {f : R}
    (U : StandardOpenCoverOf f) (i : U.index) :
    Localization.Away f →+* Localization.Away (U.generator i) :=
  (U.restrictionAlgHom i).toRingHom

/-- The ring-hom view of a standard-cover restriction is the underlying map
of its algebra-hom owner. -/
@[simp, stacks 01HT "standard-open restriction ring bridge"]
theorem StandardOpenCoverOf.restrictionAlgHom_toRingHom {f : R}
    (U : StandardOpenCoverOf f) (i : U.index) :
    (U.restrictionAlgHom i).toRingHom = U.restrictionRingHom i := sorry

/-- A standard-cover restriction algebra map commutes with the maps from the
ambient semiring. -/
@[simp, stacks 01HT "standard-open restriction algebra map law"]
theorem StandardOpenCoverOf.restrictionAlgHom_algebraMap {f : R}
    (U : StandardOpenCoverOf f) (i : U.index) (r : R) :
    U.restrictionAlgHom i (algebraMap R (Localization.Away f) r) =
      algebraMap R (Localization.Away (U.generator i)) r := sorry

/-- The restriction homomorphism of a standard open cover commutes with the
ambient maps from `R`. -/
@[simp, stacks 01HT "standard-open restriction ring map law"]
theorem StandardOpenCoverOf.restrictionRingHom_algebraMap {f : R}
    (U : StandardOpenCoverOf f) (i : U.index) (r : R) :
    U.restrictionRingHom i (algebraMap R (Localization.Away f) r) =
      algebraMap R (Localization.Away (U.generator i)) r := sorry

section ModuleMap

/-- The restriction map between localized modules attached to a member of a
standard open cover. -/
@[stacks 01HT "standard-open restriction module map"]
noncomputable abbrev StandardOpenCoverOf.restrictionModuleMap {f : R}
    (U : StandardOpenCoverOf f) (M : Type*) [AddCommMonoid M] [Module R M]
    (i : U.index) :
    LocalizedModule.Away f M →ₛₗ[U.restrictionRingHom i]
      LocalizedModule.Away (U.generator i) M :=
  awayToAwayModuleMap M f (U.generator i)
    (U.cover ▸ le_iSup (fun j ↦ basicOpen (U.generator j)) i)

/-- The localized-module restriction map commutes with the canonical maps from
the original module. -/
@[simp, stacks 01HT "standard-open restriction module law"]
theorem StandardOpenCoverOf.restrictionModuleMap_mkLinearMap {f : R}
    (U : StandardOpenCoverOf f) (M : Type*) [AddCommMonoid M] [Module R M]
    (i : U.index) (m : M) :
    U.restrictionModuleMap M i
        (LocalizedModule.mkLinearMap (Submonoid.powers f) M m) =
      LocalizedModule.mkLinearMap (Submonoid.powers (U.generator i)) M m := sorry

end ModuleMap

/-- The generators of a standard open cover span the unit ideal after
localizing away from the covered principal open. -/
@[stacks 01HT "standard-open localized span criterion"]
theorem StandardOpenCoverOf.span_eq_top_localization {f : R}
    (U : StandardOpenCoverOf f) :
    Ideal.span
        (Set.range fun i : U.index ↦ algebraMap R (Localization.Away f) (U.generator i)) = ⊤ := sorry

/-- A standard open cover simultaneously records its covering equality and its
localized unit-ideal spanning criterion. -/
@[stacks 01HT "standard-open cover specification"]
theorem StandardOpenCoverOf.spec {f : R} (U : StandardOpenCoverOf f) :
    (⨆ i, U.opens i) = basicOpen f ∧
      Ideal.span
          (Set.range fun i : U.index ↦ algebraMap R (Localization.Away f) (U.generator i)) = ⊤ := sorry

/-- Every open cover of `D(f)` admits a refinement by a principal-open family packaged as a
`StandardOpenCoverOf f`; the finiteness witness for the resulting index type is the explicit
field `U.finiteIndex`. -/
@[stacks 01HS "standard-open refinement of a principal-open cover"]
theorem StandardOpenCoverOf.exists_refinement_of_open_cover
    {f : R} {ι : Type w} (V : ι → TopologicalSpace.Opens (PrimeSpectrum R))
    (hV : basicOpen f ≤ ⨆ i, V i) :
    ∃ U : StandardOpenCoverOf.{u, v} f,
      ∀ i : U.index, ∃ j : ι, U.opens i ≤ V j := sorry

/-- A standard open cover of `Spec(R)` is a standard open cover of `D(1)`;
for a cover `U`, its index type is `U.index` and its explicit finiteness
witness is `U.finiteIndex`. -/
@[stacks 01HT]
abbrev StandardOpenCover : Type _ := StandardOpenCoverOf (1 : R)

/-- The unit-ideal criterion gives the covering equality needed to construct
a standard open cover of `Spec(R)`. -/
@[stacks 01HT "standard-open spectrum cover equality"]
theorem StandardOpenCover.cover_eq_iSup_of_span_eq_top
    {ι : Type v} (generator : ι → R)
    (span_eq_top : (Ideal.span (Set.range generator) : Ideal R) = ⊤) :
    basicOpen (1 : R) = ⨆ i, basicOpen (generator i) := sorry

/-- Construct a standard open cover of `Spec(R)` directly from a finite family
whose generators span the unit ideal. -/
@[stacks 01HT "standard open cover of the spectrum"]
def StandardOpenCover.ofGenerator
    {ι : Type v} [Finite ι] (generator : ι → R)
    (span_eq_top : (Ideal.span (Set.range generator) : Ideal R) = ⊤) :
    StandardOpenCoverOf (1 : R) where
  index := ι
  finiteIndex := inferInstance
  generator := generator
  cover := StandardOpenCover.cover_eq_iSup_of_span_eq_top generator span_eq_top

/-- The principal opens in a standard open cover of `Spec(R)` have supremum
`⊤`. -/
@[stacks 01HT "standard-open spectrum cover supremum"]
theorem StandardOpenCover.iSup_eq_top (U : StandardOpenCover) :
    (⨆ i, U.opens i) = (⊤ : TopologicalSpace.Opens (PrimeSpectrum R)) := sorry

/-- The generators of a standard open cover of `Spec(R)` span the unit ideal. -/
@[stacks 01HT "standard-open spectrum span criterion"]
theorem StandardOpenCover.span_eq_top (U : StandardOpenCover) :
    (Ideal.span (Set.range U.generator) : Ideal R) = ⊤ := sorry

/-- A standard open cover of `Spec(R)` simultaneously records its covering
equality and its unit-ideal spanning criterion. -/
@[stacks 01HT "standard-open spectrum cover specification"]
theorem StandardOpenCover.spec (U : StandardOpenCover) :
    (⨆ i, U.opens i) = (⊤ : TopologicalSpace.Opens (PrimeSpectrum R)) ∧
      (Ideal.span (Set.range U.generator) : Ideal R) = ⊤ := sorry

end

end PrimeSpectrum
