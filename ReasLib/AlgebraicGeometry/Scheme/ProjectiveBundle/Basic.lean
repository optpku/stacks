/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import ReasLib.CategoryTheory.Monoidal.InvertibleQuotient
public import ReasLib.AlgebraicGeometry.Scheme.Module.Invertible.Basic
public import ReasLib.AlgebraicGeometry.Scheme.ProjectiveBundle.Lift
public import ReasLib.AlgebraicGeometry.Scheme.RelativeProj.Presentation
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Projective bundles

This file owns the representation-style definition of a projective bundle over a scheme.  It is
independent of any textbook chapter: a projective bundle represents invertible quotients of the
pullback of its defining module.
-/

@[expose] public section

open AlgebraicGeometry
open CategoryTheory
open CategoryTheory.MonoidalCategory
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme

variable {X P : Scheme.{u}} {ℰ : X.Modules}

namespace ProjectiveBundle

/-- A projective-bundle representation records the universal lift/quotient equivalence, an
explicit relative projective-spectrum presentation of the structure morphism, and the
invertibility of every integral twist. The canonical tensor product on every scheme-module
category is inferred, so the representation cannot depend on an ambient ad hoc monoidal
instance. -/
@[stacks 01OB "projective-bundle quotient representation"]
structure Representation (π : P ⟶ X) (ℰ : X.Modules) where
  /-- The universal quotient description after every base change. -/
  liftEquiv :
    ∀ ⦃T : Scheme.{u}⦄ (f : T ⟶ X),
      Lift π f ≃
        CategoryTheory.InvertibleQuotient ((Scheme.Modules.pullback f).obj ℰ)
  /-- Pulling the target of the identity quotient back along a lift identifies it with the
  target of the quotient classified by that lift. -/
  pullbackTautologicalIso :
    ∀ ⦃T : Scheme.{u}⦄ (f : T ⟶ X) (σ : Lift π f),
      (Scheme.Modules.pullback σ.hom).obj
          ((liftEquiv π (Lift.identity π)).object) ≅
        (liftEquiv f σ).object
  /-- The pullback of the identity quotient agrees with the quotient classified by a lift,
  after the canonical comparison of their source modules. -/
  pullbackTautologicalIso_hom :
    ∀ ⦃T : Scheme.{u}⦄ (f : T ⟶ X) (σ : Lift π f),
      (Scheme.Modules.pullback σ.hom).map
            ((liftEquiv π (Lift.identity π)).hom) ≫
          (pullbackTautologicalIso f σ).hom =
        (Lift.pullbackSourceIso σ ℰ).hom ≫ (liftEquiv f σ).hom
  /-- An explicit presentation of the structure morphism as a relative projective spectrum. -/
  presentation : Scheme.Hom.RelativeProjPresentation π
  /-- Every integral twist in the relative projective-spectrum presentation is invertible. -/
  twist_isInvertible :
    ∀ n : ℤ, Scheme.Modules.Invertible (presentation.twist n)

/-- The integral twists in a projective-bundle representation. -/
abbrev Representation.twist {π : P ⟶ X}
    (hπ : Representation π ℰ) (n : ℤ) : P.Modules :=
  hπ.presentation.twist n

/-- Build a projective-bundle representation from its universal quotient equivalences, an
explicit relative projective-spectrum presentation, and invertibility of its integral twists. -/
def Representation.ofUniversalProperty
    (liftEquiv :
      ∀ ⦃T : Scheme.{u}⦄ (f : T ⟶ X),
        Lift π f ≃
          CategoryTheory.InvertibleQuotient ((Scheme.Modules.pullback f).obj ℰ))
    (pullbackTautologicalIso :
      ∀ ⦃T : Scheme.{u}⦄ (f : T ⟶ X) (σ : Lift π f),
        (Scheme.Modules.pullback σ.hom).obj
            ((liftEquiv π (Lift.identity π)).object) ≅
          (liftEquiv f σ).object)
    (pullbackTautologicalIso_hom :
      ∀ ⦃T : Scheme.{u}⦄ (f : T ⟶ X) (σ : Lift π f),
        (Scheme.Modules.pullback σ.hom).map
              ((liftEquiv π (Lift.identity π)).hom) ≫
            (pullbackTautologicalIso f σ).hom =
          (Lift.pullbackSourceIso σ ℰ).hom ≫ (liftEquiv f σ).hom)
    (presentation : Scheme.Hom.RelativeProjPresentation π)
    (twist_isInvertible :
      ∀ n : ℤ, Scheme.Modules.Invertible (presentation.twist n)) :
    Representation π ℰ :=
  ⟨liftEquiv, pullbackTautologicalIso, pullbackTautologicalIso_hom, presentation,
    twist_isInvertible⟩

/-- The structure morphism of a projective-bundle representation is separated. -/
@[stacks 01OB "projective-bundle separatedness"]
theorem Representation.isSeparated
    (hπ : Representation π ℰ) : IsSeparated π := hπ.presentation.isSeparated

/-- The invertible quotient represented by the identity lift of a projective bundle. -/
@[stacks 01OB "tautological quotient of a projective bundle",
  stacks 01VM "tautological quotient in relative very ampleness"]
noncomputable def tautologicalQuotient
    (π : P ⟶ X) (hπ : Representation π ℰ) :
    CategoryTheory.InvertibleQuotient ((Scheme.Modules.pullback π).obj ℰ) :=
  hπ.liftEquiv π (Lift.identity π)

/-- The target module of the identity quotient of a projective-bundle representation. -/
@[stacks 01OB "tautological module of a projective bundle",
  stacks 01VM "tautological module in relative very ampleness"]
noncomputable abbrev tautologicalSheaf
    (π : P ⟶ X) (hπ : Representation π ℰ) : P.Modules :=
  (tautologicalQuotient π hπ).object

/-- The comparison isomorphism of a projective-bundle representation identifies the pullback
of its tautological module with the target of the quotient classified by a lift. -/
noncomputable abbrev Representation.pullbackTautologicalSheafIso
    (hπ : Representation π ℰ) {T : Scheme.{u}} (f : T ⟶ X) (σ : Lift π f) :
    (Scheme.Modules.pullback σ.hom).obj (tautologicalSheaf π hπ) ≅
      (hπ.liftEquiv f σ).object :=
  hπ.pullbackTautologicalIso f σ

/-- Pulling back the tautological quotient morphism along a lift gives the quotient morphism
classified by that lift, after the canonical source comparison. -/
theorem Representation.pullbackTautologicalIso_spec
    (hπ : Representation π ℰ) {T : Scheme.{u}} (f : T ⟶ X) (σ : Lift π f) :
    (Scheme.Modules.pullback σ.hom).map (tautologicalQuotient π hπ).hom ≫
        (hπ.pullbackTautologicalIso f σ).hom =
      (Lift.pullbackSourceIso σ ℰ).hom ≫ (hπ.liftEquiv f σ).hom :=
  hπ.pullbackTautologicalIso_hom f σ

/-- The tautological module of a projective-bundle representation is invertible. -/
@[stacks 01OB "invertibility of the projective-bundle tautological module",
  stacks 01VM "invertibility of the projective-bundle tautological module"]
theorem tautologicalSheaf_isInvertible
    (π : P ⟶ X) (hπ : Representation π ℰ) :
    Scheme.Modules.Invertible (tautologicalSheaf π hπ) := sorry

end ProjectiveBundle

end AlgebraicGeometry.Scheme
