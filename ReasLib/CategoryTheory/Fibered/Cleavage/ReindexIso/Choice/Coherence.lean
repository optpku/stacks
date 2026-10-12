/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Fibered.Cleavage.ReindexIso.Choice.Basic
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Coherence for change of cleavage

The canonical comparisons between reindexing choices are uniquely determined by cartesian
factorization. Consequently they are reflexive, symmetric, and transitive without additional
choices. This leaf exposes those laws in componentwise and natural-isomorphism forms.
-/

@[expose] public section

universe vC vS uC uS

namespace CategoryTheory

open Functor

variable {C : Type uC} [Category.{vC} C]
variable {S : Type uS} [Category.{vS} S]

namespace Functor.Cleavage

variable {p : S ⥤ C}

/-- A vertical map between two selected reindexing objects which identifies their cartesian
arrows is the canonical forward change-of-cleavage comparison. -/
theorem Reindex.uniqueIsoApp.hom.unique
    (chi₁ chi₂ : p.Cleavage) {U V : C} (f : V ⟶ U) (x : Fiber p U)
    (alpha : (chi₁.reindex f).obj x ⟶ (chi₂.reindex f).obj x)
    (halpha : alpha.1 ≫ chi₂.cartesianHom f x = chi₁.cartesianHom f x) :
    alpha = (Reindex.uniqueIsoApp chi₁ chi₂ f x).hom := sorry

/-- A vertical map in the reverse direction which identifies the two selected cartesian arrows
is the canonical inverse change-of-cleavage comparison. -/
theorem Reindex.uniqueIsoApp.inv.unique
    (chi₁ chi₂ : p.Cleavage) {U V : C} (f : V ⟶ U) (x : Fiber p U)
    (alpha : (chi₂.reindex f).obj x ⟶ (chi₁.reindex f).obj x)
    (halpha : alpha.1 ≫ chi₁.cartesianHom f x = chi₂.cartesianHom f x) :
    alpha = (Reindex.uniqueIsoApp chi₁ chi₂ f x).inv := sorry

/-- The natural change-of-cleavage isomorphism is uniquely characterized by its cartesian
factorization at every object. -/
theorem Reindex.uniqueIso.unique
    (chi₁ chi₂ : p.Cleavage) {U V : C} (f : V ⟶ U)
    (alpha : chi₁.reindex f ≅ chi₂.reindex f)
    (halpha : ∀ x : Fiber p U,
      (alpha.hom.app x).1 ≫ chi₂.cartesianHom f x = chi₁.cartesianHom f x) :
    alpha = Reindex.uniqueIso chi₁ chi₂ f := sorry

/-- Conjugating first-choice reindexing by the canonical comparison gives second-choice
reindexing. -/
@[reassoc]
theorem Reindex.uniqueIsoApp.conjugation.toSecond
    (chi₁ chi₂ : p.Cleavage) {U V : C} (f : V ⟶ U)
    {x y : Fiber p U} (phi : x ⟶ y) :
    (Reindex.uniqueIsoApp chi₁ chi₂ f x).inv ≫
        (chi₁.reindex f).map phi ≫
        (Reindex.uniqueIsoApp chi₁ chi₂ f y).hom =
      (chi₂.reindex f).map phi := sorry

/-- Conjugating second-choice reindexing by the inverse canonical comparison recovers
first-choice reindexing. -/
@[reassoc]
theorem Reindex.uniqueIsoApp.conjugation.toFirst
    (chi₁ chi₂ : p.Cleavage) {U V : C} (f : V ⟶ U)
    {x y : Fiber p U} (phi : x ⟶ y) :
    (Reindex.uniqueIsoApp chi₁ chi₂ f x).hom ≫
        (chi₂.reindex f).map phi ≫
        (Reindex.uniqueIsoApp chi₁ chi₂ f y).inv =
      (chi₁.reindex f).map phi := sorry

/-- Comparing a cleavage with itself gives the identity objectwise isomorphism. -/
@[simp]
theorem Reindex.uniqueIsoApp.self
    (chi : p.Cleavage) {U V : C} (f : V ⟶ U) (x : Fiber p U) :
    Reindex.uniqueIsoApp chi chi f x = Iso.refl _ := sorry

/-- The forward comparison from a cleavage to itself is the identity. -/
@[simp]
theorem Reindex.uniqueIsoApp.hom.self
    (chi : p.Cleavage) {U V : C} (f : V ⟶ U) (x : Fiber p U) :
    (Reindex.uniqueIsoApp chi chi f x).hom = 𝟙 _ := sorry

/-- The inverse comparison from a cleavage to itself is the identity. -/
@[simp]
theorem Reindex.uniqueIsoApp.inv.self
    (chi : p.Cleavage) {U V : C} (f : V ⟶ U) (x : Fiber p U) :
    (Reindex.uniqueIsoApp chi chi f x).inv = 𝟙 _ := sorry

/-- Reversing the two cleavage choices reverses the canonical objectwise isomorphism. -/
@[simp]
theorem Reindex.uniqueIsoApp.symm
    (chi₁ chi₂ : p.Cleavage) {U V : C} (f : V ⟶ U) (x : Fiber p U) :
    (Reindex.uniqueIsoApp chi₁ chi₂ f x).symm =
      Reindex.uniqueIsoApp chi₂ chi₁ f x := sorry

/-- Forward comparison maps compose transitively through an intermediate cleavage. -/
@[simp, reassoc]
theorem Reindex.uniqueIsoApp.hom.trans
    (chi₁ chi₂ chi₃ : p.Cleavage) {U V : C} (f : V ⟶ U) (x : Fiber p U) :
    (Reindex.uniqueIsoApp chi₁ chi₂ f x).hom ≫
        (Reindex.uniqueIsoApp chi₂ chi₃ f x).hom =
      (Reindex.uniqueIsoApp chi₁ chi₃ f x).hom := sorry

/-- Inverse comparison maps compose transitively through an intermediate cleavage. -/
@[simp, reassoc]
theorem Reindex.uniqueIsoApp.inv.trans
    (chi₁ chi₂ chi₃ : p.Cleavage) {U V : C} (f : V ⟶ U) (x : Fiber p U) :
    (Reindex.uniqueIsoApp chi₂ chi₃ f x).inv ≫
        (Reindex.uniqueIsoApp chi₁ chi₂ f x).inv =
      (Reindex.uniqueIsoApp chi₁ chi₃ f x).inv := sorry

/-- Comparing a cleavage's reindexing functor with itself gives the identity natural
isomorphism. -/
@[simp]
theorem Reindex.uniqueIso.self
    (chi : p.Cleavage) {U V : C} (f : V ⟶ U) :
    Reindex.uniqueIso chi chi f = Iso.refl _ := sorry

/-- Reversing two cleavage choices reverses their canonical reindexing natural isomorphism. -/
@[simp]
theorem Reindex.uniqueIso.symm
    (chi₁ chi₂ : p.Cleavage) {U V : C} (f : V ⟶ U) :
    (Reindex.uniqueIso chi₁ chi₂ f).symm =
      Reindex.uniqueIso chi₂ chi₁ f := sorry

/-- Canonical reindexing comparisons compose transitively through an intermediate cleavage. -/
@[simp]
theorem Reindex.uniqueIso.trans
    (chi₁ chi₂ chi₃ : p.Cleavage) {U V : C} (f : V ⟶ U) :
    (Reindex.uniqueIso chi₁ chi₂ f).trans
        (Reindex.uniqueIso chi₂ chi₃ f) =
      Reindex.uniqueIso chi₁ chi₃ f := sorry

end Functor.Cleavage

end CategoryTheory
