/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.RingedSite.Module.Derived.LocalHomotopy
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.OpenSubspace.Restriction
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.Perfect.StrictlyPerfect
import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Open-cover homotopy and lifting for strictly perfect complexes

This is the ringed-space view of the cover-wise predicates owned by
`RingedSite.CochainComplex`.  The restriction functor is written explicitly on every public
surface, so downstream statements can use the API without local complex notation.
-/

open AlgebraicGeometry
open CategoryTheory
open CategoryTheory.Limits
open ComplexShape
open TopologicalSpace

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace.CochainComplex

variable {X : RingedSpace.{u}}

/-- A morphism of `𝒪_X`-complexes is null-homotopic on an open `U` after restriction to `U`. -/
@[stacks 08C7 "restriction-level null homotopy"]
def IsNullHomotopicOn
    {E F : _root_.CochainComplex (Modules X) ℤ}
    (α : E ⟶ F) (U : Opens X.carrier) : Prop :=
  Nonempty (Homotopy ((moduleRestrictionComplexToOpen X U).map α) 0)

/-- A morphism is locally null-homotopic at a point when it is null-homotopic on some
neighborhood of that point. -/
@[stacks 08C7 "point-neighborhood null homotopy"]
def IsLocallyNullHomotopicAt
    {E F : _root_.CochainComplex (Modules X) ℤ}
    (α : E ⟶ F) (x : X) : Prop :=
  ∃ U : Opens X.carrier, x ∈ U ∧ IsNullHomotopicOn α U

/-- The point-neighborhood predicate unfolds to its source-facing existential form. -/
theorem isLocallyNullHomotopicAt_iff
    {E F : _root_.CochainComplex (Modules X) ℤ}
    (α : E ⟶ F) (x : X) :
    IsLocallyNullHomotopicAt α x ↔
      ∃ U : Opens X.carrier, x ∈ U ∧
        Nonempty (Homotopy ((moduleRestrictionComplexToOpen X U).map α) 0) := sorry

/-- A morphism `α : E ⟶ F` lifts through `f : G ⟶ F` on an open `U` up to homotopy. -/
@[stacks 08C8 "restriction-level lifting"]
def IsLiftableOn
    {E F G : _root_.CochainComplex (Modules X) ℤ}
    (α : E ⟶ F) (f : G ⟶ F) (U : Opens X.carrier) : Prop :=
  ∃ β : (moduleRestrictionComplexToOpen X U).obj E ⟶
      (moduleRestrictionComplexToOpen X U).obj G,
    Nonempty (Homotopy ((moduleRestrictionComplexToOpen X U).map α)
      (β ≫ (moduleRestrictionComplexToOpen X U).map f))

/-- A morphism lifts locally at a point when the restricted lift exists on a neighborhood. -/
@[stacks 08C8 "point-neighborhood lifting"]
def IsLocallyLiftableAt
    {E F G : _root_.CochainComplex (Modules X) ℤ}
    (α : E ⟶ F) (f : G ⟶ F) (x : X) : Prop :=
  ∃ U : Opens X.carrier, x ∈ U ∧ IsLiftableOn α f U

/-- The point-neighborhood lifting predicate unfolds to the displayed restricted factorization. -/
theorem isLocallyLiftableAt_iff
    {E F G : _root_.CochainComplex (Modules X) ℤ}
    (α : E ⟶ F) (f : G ⟶ F) (x : X) :
    IsLocallyLiftableAt α f x ↔
      ∃ U : Opens X.carrier, x ∈ U ∧
        ∃ β : (moduleRestrictionComplexToOpen X U).obj E ⟶
            (moduleRestrictionComplexToOpen X U).obj G,
          Nonempty (Homotopy ((moduleRestrictionComplexToOpen X U).map α)
            (β ≫ (moduleRestrictionComplexToOpen X U).map f)) := sorry

namespace IsStrictlyPerfect

namespace NullHomotopy

/-- Lemma 20.46.6 (1): a strictly perfect source has null-homotopic restriction on an open cover
when the target complex is acyclic. -/
@[stacks 08C7 "open-cover null homotopy"]
theorem cover_of_acyclic
    {E F : _root_.CochainComplex (Modules X) ℤ}
    (hE : _root_.SheafOfModules.CochainComplex.IsStrictlyPerfect E)
    (α : E ⟶ F) (hF : F.Acyclic) :
    ∃ (I : Type u) (U : I → Opens X.carrier), IsOpenCover U ∧
      ∀ i : I, IsNullHomotopicOn α (U i) := sorry

/-- Lemma 20.46.6 (1), point-neighborhood form. -/
@[stacks 08C7 "point-neighborhood null homotopy"]
theorem at_of_acyclic
    {E F : _root_.CochainComplex (Modules X) ℤ}
    (hE : _root_.SheafOfModules.CochainComplex.IsStrictlyPerfect E)
    (α : E ⟶ F) (hF : F.Acyclic) (x : X) :
    IsLocallyNullHomotopicAt α x := sorry

/-- Lemma 20.46.6 (2): a strictly perfect source bounded below by `a` has null-homotopic
restriction on an open cover when the target homology vanishes in degrees `≥ a`. -/
@[stacks 08C7 "bounded-below open-cover null homotopy"]
theorem cover_of_isStrictlyGE
    {E F : _root_.CochainComplex (Modules X) ℤ} (a : ℤ)
    (hE : _root_.SheafOfModules.CochainComplex.IsStrictlyPerfect E)
    (hE_ge : E.IsStrictlyGE a) (α : E ⟶ F)
    (hF : ∀ i : ℤ, a ≤ i → IsZero (F.homology i)) :
    ∃ (I : Type u) (U : I → Opens X.carrier), IsOpenCover U ∧
      ∀ i : I, IsNullHomotopicOn α (U i) := sorry

/-- Lemma 20.46.6 (2), point-neighborhood form. -/
@[stacks 08C7 "bounded-below point-neighborhood null homotopy"]
theorem at_of_isStrictlyGE
    {E F : _root_.CochainComplex (Modules X) ℤ} (a : ℤ)
    (hE : _root_.SheafOfModules.CochainComplex.IsStrictlyPerfect E)
    (hE_ge : E.IsStrictlyGE a) (α : E ⟶ F)
    (hF : ∀ i : ℤ, a ≤ i → IsZero (F.homology i)) (x : X) :
    IsLocallyNullHomotopicAt α x := sorry

end NullHomotopy

namespace Lift

/-- Lemma 20.46.7: a bounded-below strictly perfect source lifts through a homology isomorphism
above `a` and an epimorphism in degree `a`, on an open cover and up to homotopy. -/
@[stacks 08C8 "open-cover lifting"]
theorem cover_of_isStrictlyGE
    {E F G : _root_.CochainComplex (Modules X) ℤ} (a : ℤ)
    (hE : _root_.SheafOfModules.CochainComplex.IsStrictlyPerfect E)
    (hE_ge : E.IsStrictlyGE a) (α : E ⟶ F) (f : G ⟶ F)
    (hf_iso : ∀ j : ℤ, a < j → IsIso (HomologicalComplex.homologyMap f j))
    (hf_epi : Epi (HomologicalComplex.homologyMap f a)) :
    ∃ (I : Type u) (U : I → Opens X.carrier), IsOpenCover U ∧
      ∀ i : I, IsLiftableOn α f (U i) := sorry

/-- Lemma 20.46.7, point-neighborhood form. -/
@[stacks 08C8 "point-neighborhood lifting"]
theorem at_of_isStrictlyGE
    {E F G : _root_.CochainComplex (Modules X) ℤ} (a : ℤ)
    (hE : _root_.SheafOfModules.CochainComplex.IsStrictlyPerfect E)
    (hE_ge : E.IsStrictlyGE a) (α : E ⟶ F) (f : G ⟶ F)
    (hf_iso : ∀ j : ℤ, a < j → IsIso (HomologicalComplex.homologyMap f j))
    (hf_epi : Epi (HomologicalComplex.homologyMap f a)) (x : X) :
    IsLocallyLiftableAt α f x := sorry

end Lift

end IsStrictlyPerfect

end AlgebraicGeometry.RingedSpace.CochainComplex
