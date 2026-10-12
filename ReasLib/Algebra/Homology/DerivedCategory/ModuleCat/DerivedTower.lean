/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Category.CommRingCat.InverseSystem
public import ReasLib.Algebra.Homology.DerivedCategory.ModuleCat.DerivedExtension

/-!
# Derived Module Towers

A `ModuleCat.DerivedTower A` is a compatible family of derived module objects over a sequential
inverse system `A` of commutative rings.  Its primitive transition is written after restriction of
scalars.  Base-change comparisons are formed from explicit `DerivedExtension` models, so their
concrete data is never selected from a proof that a derived functor exists.
@stack 0CQF
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u

namespace CategoryTheory.ModuleCat

/-- A compatible family of derived module objects over a sequential inverse system of commutative
rings. -/
@[stacks 0CQF "derived module tower over a ring inverse system"]
structure DerivedTower (A : SequentialInverseSystem CommRingCat.{u}) where
  /-- The derived module object at stage `n`. -/
  obj (n : ℕ) : DerivedCategory (ModuleCat.{u, u} (A.family n : Type u))
  /-- The successor morphism, viewed over the source ring by restriction of scalars. -/
  step (n : ℕ) :
    obj (n + 1) ⟶
      (derivedRestrictionOfScalars (A.stepMap n).hom).obj (obj n)

namespace DerivedTower

variable {A : SequentialInverseSystem CommRingCat.{u}}

/-- The derived base change of stage `n + 1` to the ring at stage `n`, relative to an explicit
derived extension model. -/
noncomputable abbrev baseChange (T : DerivedTower A) (n : ℕ)
    (E : DerivedExtension (A.stepMap n).hom) :
    DerivedCategory (ModuleCat.{u, u} (A.family n : Type u)) :=
  E.obj (T.obj (n + 1))

/-- The base-change comparison adjoint to the successor morphism of a derived module tower,
formed in an explicit derived extension model. -/
@[stacks 0CQF "successor base-change comparison"]
noncomputable def baseChangeMap (T : DerivedTower A) (n : ℕ)
    (E : DerivedExtension (A.stepMap n).hom) :
    T.baseChange n E ⟶ T.obj n :=
  E.transpose (T.step n)

/-- The base-change comparison transposes back to the primitive restricted transition. -/
@[simp]
theorem baseChangeMap_untranspose (T : DerivedTower A) (n : ℕ)
    (E : DerivedExtension (A.stepMap n).hom) :
    E.untranspose (T.baseChangeMap n E) = T.step n := sorry

/-- Cartesianity at one transition, stated independently of the chosen derived extension model.
The first clause rules out a vacuous universal statement when no model has yet been installed. -/
def IsCartesianAt (T : DerivedTower A) (n : ℕ) : Prop :=
  Nonempty (DerivedExtension (A.stepMap n).hom) ∧
    ∀ E : DerivedExtension (A.stepMap n).hom, IsIso (T.baseChangeMap n E)

/-- A derived module tower is Cartesian when every successor base-change comparison is an
isomorphism, independently of the explicit derived extension model. -/
@[stacks 0CQF "Cartesian derived module tower"]
def IsCartesian (T : DerivedTower A) : Prop :=
  ∀ n : ℕ, T.IsCartesianAt n

/-- A Cartesian tower guarantees that a derived extension model exists at every transition. -/
theorem IsCartesian.nonemptyExtension {T : DerivedTower A} (h : T.IsCartesian) (n : ℕ) :
    Nonempty (DerivedExtension (A.stepMap n).hom) := sorry

/-- A Cartesian tower supplies invertibility of each comparison in every explicit derived
extension model. -/
theorem IsCartesian.isIso {T : DerivedTower A} (h : T.IsCartesian) (n : ℕ)
    (E : DerivedExtension (A.stepMap n).hom) :
    IsIso (T.baseChangeMap n E) := sorry

/-- Cartesianity at one transition can be checked in any one explicit derived extension model. -/
theorem isCartesianAt_iff (T : DerivedTower A) (n : ℕ)
    (E : DerivedExtension (A.stepMap n).hom) :
    T.IsCartesianAt n ↔ IsIso (T.baseChangeMap n E) := sorry

/-- Cartesianity of a tower can be checked using any explicit family of derived extension
models. -/
theorem isCartesian_iff (T : DerivedTower A)
    (E : ∀ n : ℕ, DerivedExtension (A.stepMap n).hom) :
    T.IsCartesian ↔ ∀ n : ℕ, IsIso (T.baseChangeMap n (E n)) := sorry

/-- Build a derived module tower from successor maps written in the derived base-change
direction relative to explicit derived extension models. -/
noncomputable def ofBaseChange
    (E : ∀ n : ℕ, DerivedExtension (A.stepMap n).hom)
    (obj : (n : ℕ) → DerivedCategory (ModuleCat.{u, u} (A.family n : Type u)))
    (map : ∀ n : ℕ, (E n).obj (obj (n + 1)) ⟶ obj n) :
    DerivedTower A where
  obj := obj
  step n := (E n).untranspose (map n)

/-- The stages of a tower built from base-change maps are the supplied stages. -/
@[simp]
theorem ofBaseChange_obj
    (E : ∀ n : ℕ, DerivedExtension (A.stepMap n).hom)
    (obj : (n : ℕ) → DerivedCategory (ModuleCat.{u, u} (A.family n : Type u)))
    (map : ∀ n : ℕ, (E n).obj (obj (n + 1)) ⟶ obj n)
    (n : ℕ) :
    (ofBaseChange E obj map).obj n = obj n := sorry

/-- The successor morphism of a tower built from base-change maps is the adjoint of the supplied
map. -/
theorem ofBaseChange_step
    (E : ∀ n : ℕ, DerivedExtension (A.stepMap n).hom)
    (obj : (n : ℕ) → DerivedCategory (ModuleCat.{u, u} (A.family n : Type u)))
    (map : ∀ n : ℕ, (E n).obj (obj (n + 1)) ⟶ obj n)
    (n : ℕ) :
    (ofBaseChange E obj map).step n = (E n).untranspose (map n) := sorry

/-- Transposing the successor morphism of `ofBaseChange` recovers the supplied base-change map. -/
@[simp]
theorem baseChangeMap_ofBaseChange
    (E : ∀ n : ℕ, DerivedExtension (A.stepMap n).hom)
    (obj : (n : ℕ) → DerivedCategory (ModuleCat.{u, u} (A.family n : Type u)))
    (map : ∀ n : ℕ, (E n).obj (obj (n + 1)) ⟶ obj n)
    (n : ℕ) :
    (ofBaseChange E obj map).baseChangeMap n (E n) = map n := sorry

end DerivedTower

end CategoryTheory.ModuleCat
