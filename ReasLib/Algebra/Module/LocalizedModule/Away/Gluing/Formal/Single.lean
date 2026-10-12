/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.RingTheory.Localization.Away.Basic
public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.RingTheory.RingHom.Flat
public import ReasLib.Algebra.Module.LocalizedModule.Away.Gluing.Formal
public import ReasLib.CategoryTheory.Limits.CategoricalPullback.CatCommSqOver
import Mathlib.Tactic.CrossRefAttribute

/-!
# Single-principal-open formal gluing

This leaf is the reusable single-element specialization of formal gluing.  It
keeps the ring map explicit, and packages the overlap square and the induced
module pullback functor without importing any chapter file.

@stack 05ES
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open scoped CategoricalPullback

universe u

noncomputable section

namespace LocalizedModule.Away.FormalGluing

namespace Single

variable {R S : Type u} [CommRing R] [CommRing S]

/-- The one-point principal-open family associated with `f : R`. -/
@[stacks 05ES "single principal-open family"]
abbrev family (f : R) : Fin 1 → R := fun _ ↦ f

/-- The canonical map between the two single principal-open overlap rings. -/
@[stacks 05ES "single principal-open overlap map"]
abbrev overlapMap (φ : R →+* S) (f : R) :
    Localization.Away f →+* Localization.Away (φ f) :=
  Localization.awayMap φ f

/-- The direct base-to-overlap ring map, kept explicit for ring-hom-parametric APIs. -/
@[stacks 05ES "single principal-open base-to-overlap map"]
abbrev baseToOverlap (φ : R →+* S) (f : R) :
    R →+* Localization.Away (φ f) :=
  (algebraMap S (Localization.Away (φ f))).comp φ

/-- The ring square underlying single-element formal gluing. -/
@[stacks 05ES "single principal-open overlap square"]
theorem square_comm (φ : R →+* S) (f : R) :
    baseToOverlap φ f =
      (overlapMap φ f).comp (algebraMap R (Localization.Away f)) := sorry

/-- The comparison between the two extension-of-scalars paths to the overlap. -/
@[stacks 05ES "single principal-open comparison isomorphism"]
noncomputable def comparison (φ : R →+* S) (f : R) :
    ModuleCat.extendScalars φ ⋙
        ModuleCat.extendScalars (algebraMap S (Localization.Away (φ f))) ≅
      ModuleCat.extendScalars (algebraMap R (Localization.Away f)) ⋙
        ModuleCat.extendScalars (overlapMap φ f) :=
  (ModuleCat.extendScalarsComp φ
      (algebraMap S (Localization.Away (φ f)))).symm ≪≫
    eqToIso (congrArg ModuleCat.extendScalars (square_comm φ f)) ≪≫
    ModuleCat.extendScalarsComp
      (algebraMap R (Localization.Away f)) (overlapMap φ f)

/-- The commutative square of module functors used to form the pullback target. -/
@[stacks 05ES "single principal-open module square"]
noncomputable def square (φ : R →+* S) (f : R) :
    CategoricalPullback.CatCommSqOver
      (ModuleCat.extendScalars (algebraMap S (Localization.Away (φ f))))
      (ModuleCat.extendScalars (overlapMap φ f))
      (ModuleCat R) where
  fst := ModuleCat.extendScalars φ
  snd := ModuleCat.extendScalars (algebraMap R (Localization.Away f))
  iso := comparison φ f

/-- The canonical single-element formal-gluing functor into the module pullback. -/
@[stacks 05ES "single principal-open formal gluing functor"]
noncomputable abbrev functor (φ : R →+* S) (f : R) :
    ModuleCat R ⥤
      CategoricalPullback
        (ModuleCat.extendScalars (algebraMap S (Localization.Away (φ f))))
        (ModuleCat.extendScalars (overlapMap φ f)) :=
  (CategoricalPullback.CatCommSqOver.toFunctorToCategoricalPullback
      (ModuleCat.extendScalars (algebraMap S (Localization.Away (φ f))))
      (ModuleCat.extendScalars (overlapMap φ f))
      (ModuleCat R)).obj (square φ f)

/-- If `φ` is flat and induces an isomorphism modulo `f`, the single-element
formal-gluing functor is an equivalence. -/
@[stacks 05ES "single principal-open formal gluing equivalence"]
theorem functor_isEquivalence_of_flat_of_quotientMap_bijective
    (φ : R →+* S) (f : R) (hflat : RingHom.Flat φ)
    (hquot :
      Function.Bijective
        (Ideal.quotientMap
          (Ideal.map φ (Ideal.span ({f} : Set R))) φ Ideal.le_comap_map)) :
    Functor.IsEquivalence (functor φ f) := sorry

end Single

end LocalizedModule.Away.FormalGluing
