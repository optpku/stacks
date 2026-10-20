module

public import Mathlib.Algebra.Category.FGModuleCat.Basic
public import Mathlib.Algebra.Category.ModuleCat.Projective
public import Mathlib.CategoryTheory.ObjectProperty.ClosedUnderIsomorphisms
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.Algebra.Category.ModuleCat.Finite
public import ReasLib.RingTheory.Finiteness.Projective

/-!
# Finite Projective Module Categories

This file bundles the canonical predicate `Module.FiniteProjective` into an object property and a
full subcategory of `ModuleCat`.  The construction is independent of Grothendieck groups and is
therefore available to derived-category, descent, and K-theoretic applications alike.
-/

@[expose] public section

universe u v

namespace CategoryTheory.ModuleCat

variable (R : Type u) [Ring R]

/-- The object property of a bundled `R`-module being finite projective. -/
@[stacks 00JH "finite projective module property"]
def finiteProjective : ObjectProperty (ModuleCat.{v} R) :=
  fun M ↦ Module.FiniteProjective R M

/-- Finite-projective bundled modules are closed under isomorphisms. -/
@[stacks 00JH "finite projective module isomorphism closure"]
instance finiteProjective.isClosedUnderIsomorphisms :
    (finiteProjective.{u, v} R).IsClosedUnderIsomorphisms where
  of_iso {X Y} e hX := by
    -- Local instance justification (proof-local temporary data): expose the finite predicate
    -- component of the supplied finite-projective evidence to the equivalence theorem.
    letI : Module.Finite R X := hX.1
    -- Local instance justification (proof-local temporary data): expose the projective predicate
    -- component of the supplied finite-projective evidence to the equivalence theorem.
    letI : Module.Projective R X := hX.2
    exact ⟨Module.Finite.equiv e.toLinearEquiv,
      Module.Projective.of_equiv' e.toLinearEquiv⟩

/-- A subsingleton bundled module is finite projective. -/
@[stacks 00JH "subsingleton module is finite projective"]
theorem finiteProjective_of_subsingleton (M : ModuleCat.{v} R) [Subsingleton M] :
    finiteProjective.{u, v} R M := by
  -- Local instance justification (proof-local temporary data): provide the free-module evidence
  -- needed by the canonical theorem converting free modules to projective modules.
  letI : Module.Free R M := Module.Free.of_subsingleton R M
  exact ⟨ModuleCat.isFG_of_subsingleton R M, Module.Projective.of_free⟩

/-- The full subcategory of finite projective `R`-modules. -/
@[stacks 00JH "finite projective module category"]
abbrev FiniteProjective := (finiteProjective.{u, v} R).FullSubcategory

/-- Bundle a module that is already known to be finite and projective as an object of
`ModuleCat.FiniteProjective R`. -/
@[stacks 00JH "finite projective module constructor"]
abbrev FiniteProjective.of (M : ModuleCat.{v} R)
    [Module.Finite R M] [Module.Projective R M] :
    FiniteProjective R :=
  ⟨M, ⟨inferInstance, inferInstance⟩⟩

/-- Bundle a finite categorically projective module as a finite-projective module.

The `Small.{v} R` assumption is exactly the universe condition used by Mathlib to recover the
raw module-theoretic projectivity instance from categorical projectivity. -/
@[stacks 00JH "categorically projective finite module constructor"]
noncomputable def FiniteProjective.ofProjective
    (M : ModuleCat.{v} R) [Small.{v} R] [Module.Finite R M] (hM : Projective M) :
    FiniteProjective R :=
  ⟨M, ⟨inferInstance, (IsProjective.iff_projective (R := R) M).mpr hM⟩⟩

/-- A bundled finite-projective module is finite. -/
instance (M : FiniteProjective.{u, v} R) : Module.Finite R M.obj :=
  M.property.1

/-- A bundled finite-projective module is projective. -/
instance (M : FiniteProjective.{u, v} R) : Module.Projective R M.obj :=
  M.property.2

/-- Finite-projective modules form a subproperty of finitely generated modules. -/
@[stacks 00JH "finite projective modules are finite"]
theorem finiteProjective_le_isFG :
    finiteProjective.{u, v} R ≤ ModuleCat.isFG.{v} R :=
  fun _ hM ↦ hM.1

end CategoryTheory.ModuleCat
