/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Fibered.ChosenCleavage.Pseudofunctor
public import ReasLib.CategoryTheory.Sites.Family
public import Mathlib.CategoryTheory.Sites.Descent.DescentData
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Descent data for fixed-target families

The canonical descent functor from the fibre over `U` to descent data for an arbitrary family
`𝒰 : SemiRepresentableFamily.Over U`, the trivial descent datum, and the effectiveness predicate.

## Main declarations

* `CategoryTheory.DescentDatum.canonicalFunctor` — the functor from `p.Fiber U` to descent data.
* `CategoryTheory.DescentDatum.IsEffective` — a descent datum is effective.

## Implementation note

The construction uses the fibre pseudofunctor's `toDescentData` and requires a chosen cleavage.
The canonical owner is mathlib's `Pseudofunctor.DescentData`; it does not require chosen pairwise
or triple pullbacks. Such choices belong only to overlap-specific presentation APIs.
-/

@[expose] public section

noncomputable section

universe w v₁ v₂ u₁ u₂

namespace CategoryTheory

open Functor
open SemiRepresentableFamily.Over

variable {C : Type u₁} [Category.{v₁} C]
variable {S : Type u₂} [Category.{v₂} S]
variable {p : S ⥤ C}
variable (hc : Functor.Cleavage p)

/-! ## Singleton identity family -/

/-- The identity of `U` factors through the unique member of its singleton identity family. -/
@[simp, stacks 026E "singleton family identity factorization"]
theorem SemiRepresentableFamily.Over.singleton_id_fac (U : C) :
    𝟙 U ≫ ((SemiRepresentableFamily.Over.singleton (𝟙 U)).obj PUnit.unit).hom = 𝟙 U := sorry

/-! ## Descent data type alias -/

/-- A descent datum for a family `𝒰` over `U` in the fibred category presented by a
cleavage `hc` is an object of the canonical descent-data category of the fibre pseudofunctor. -/
@[stacks 026B]
abbrev DescentDatum
    {U : C} (𝒰 : SemiRepresentableFamily.Over U) :=
  (hc.toPseudofunctor).DescentData (fun i : 𝒰.index ↦ (𝒰.obj i).hom)

/-! ## Canonical descent functor -/

variable {U : C} (𝒰 : SemiRepresentableFamily.Over U)

/-- The canonical functor from the fiber over `U` to descent data for the family `𝒰`. -/
@[stacks 026E]
abbrev DescentDatum.canonicalFunctor :
    p.Fiber U ⥤ DescentDatum hc 𝒰 :=
  (hc.toPseudofunctor).toDescentData (fun i : 𝒰.index ↦ (𝒰.obj i).hom)

/-- The object component of the canonical descent datum is reindexing along the corresponding
member of the family. -/
@[simp, stacks 026E "canonical object component"]
theorem DescentDatum.canonicalFunctor_obj_obj
    (X : p.Fiber U) (i : 𝒰.index) :
    ((DescentDatum.canonicalFunctor hc 𝒰).obj X).obj i =
      (hc.reindex (𝒰.obj i).hom).obj X := sorry

/-- The component of a canonical descent morphism is the corresponding reindexed fiber
morphism. -/
@[simp, stacks 026E "canonical map component"]
theorem DescentDatum.canonicalFunctor_map_hom
    {X Y : p.Fiber U} (f : X ⟶ Y) (i : 𝒰.index) :
    ((DescentDatum.canonicalFunctor hc 𝒰).map f).hom i =
      (hc.reindex (𝒰.obj i).hom).map f := sorry

/-- The trivial descent datum on the singleton identity family `{𝟙 U}`. -/
@[stacks 026E]
abbrev DescentDatum.trivial (X : p.Fiber U) :
    DescentDatum hc (SemiRepresentableFamily.Over.singleton (𝟙 U)) :=
  (DescentDatum.canonicalFunctor hc (SemiRepresentableFamily.Over.singleton (𝟙 U))).obj X

/-- The unique object component of the trivial descent datum is identity reindexing. -/
@[simp, stacks 026E "trivial object component"]
theorem DescentDatum.trivial_obj (X : p.Fiber U) :
    (DescentDatum.trivial hc X).obj PUnit.unit =
      (hc.reindex (𝟙 U)).obj X := sorry

/-- The source object is canonically isomorphic to the unique object component of its trivial
descent datum.  It is the cleavage unit comparison followed by the inverse of the canonical
comparison from pseudofunctor reindexing to cleavage reindexing. -/
@[stacks 026E "trivial descent object comparison"]
noncomputable abbrev DescentDatum.trivialObjIso (X : p.Fiber U) :
    X ≅ (DescentDatum.trivial hc X).obj PUnit.unit :=
  Functor.Cleavage.Reindex.idIsoApp hc U X ≪≫
    ((Functor.Cleavage.toPseudofunctor.mapIso hc (𝟙 U)).app X).symm

/-- The canonical overlap isomorphism of the trivial descent datum, with the two identity
factorizations fixed internally. -/
@[stacks 026E "trivial overlap comparison"]
abbrev DescentDatum.trivialOverlapIso (X : p.Fiber U) :
    (hc.toPseudofunctor.map (𝟙 U).op.toLoc).toFunctor.obj
        ((DescentDatum.trivial.{v₁, v₂, u₁, u₂, 0} hc X).obj PUnit.unit) ≅
      (hc.toPseudofunctor.map (𝟙 U).op.toLoc).toFunctor.obj
        ((DescentDatum.trivial.{v₁, v₂, u₁, u₂, 0} hc X).obj PUnit.unit) :=
  (DescentDatum.trivial.{v₁, v₂, u₁, u₂, 0} hc X).iso (𝟙 U)
    (i₁ := PUnit.unit) (i₂ := PUnit.unit) (𝟙 U) (𝟙 U)
    (SemiRepresentableFamily.Over.singleton_id_fac.{v₁, u₁, 0} U)
    (SemiRepresentableFamily.Over.singleton_id_fac.{v₁, u₁, 0} U)

/-- The comparison isomorphism of the trivial descent datum on the identity overlap is the
identity isomorphism. -/
@[simp, stacks 026E "trivial overlap identity"]
theorem DescentDatum.trivial_iso (X : p.Fiber U) :
    DescentDatum.trivialOverlapIso hc X = Iso.refl _ := sorry

/-! ## Effectiveness -/

/-- A descent datum for `𝒰` is effective when it lies in the essential image of the canonical
descent functor. -/
@[stacks 026E]
abbrev DescentDatum.IsEffective (D : DescentDatum hc 𝒰) : Prop :=
  (DescentDatum.canonicalFunctor hc 𝒰).essImage D

/-- The canonical descent datum of any fiber object is effective. -/
@[stacks 026E "canonical descent datum effectiveness"]
theorem DescentDatum.IsEffective.of_canonical (X : p.Fiber U) :
    (DescentDatum.canonicalFunctor hc 𝒰).obj X |>.IsEffective (hc := hc) := sorry

/- Data audit: `canonicalFunctor` is the canonical `toDescentData` functor of the cleavage
pseudofunctor, and `trivial` is its object action on the singleton identity family.
`trivialObjIso` composes the existing `Reindex.idIsoApp` and `toPseudofunctor.mapIso` canonical
components, while `trivialOverlapIso` evaluates the canonical descent-data comparison at the
two identity factorizations. No declaration selects a second descent-data presentation or hides
object, morphism, or isomorphism payload. -/

end CategoryTheory
