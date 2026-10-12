/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Limits.Presentation
public import Mathlib.CategoryTheory.Sites.LocallySurjective
public import Mathlib.RingTheory.Finiteness.Defs
public import stacks_project.Chap70.Lemma_70_9_4_FinitePresentation

/-!
# Finite quasi-coherent algebras on QCQS algebraic spaces

If `X` is a quasi-compact quasi-separated algebraic space over a scheme `S`,
every finite quasi-coherent `𝒪_X`-algebra is a small filtered colimit of
finite and finitely presented quasi-coherent `𝒪_X`-algebras with locally
surjective transition maps.
-/

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u

namespace AlgebraicGeometry.AlgebraicSpace.QcAlgebraUnder

/-- A quasi-coherent `𝒪_X`-algebra is finite if, for every affine object of `X_étale`,
the algebra of sections is finite as a module over the corresponding structure-sheaf
sections. -/
class IsFinite {S : Scheme.{u}} {X : AlgebraicSpace S} (A : X.QcAlgebraUnder) : Prop where
  /-- Section algebras on affine étale objects are finite as modules. -/
  moduleFinite_affineEtale :
    ∀ U : affineEtaleSite X, Module.Finite Γ(U.obj.left.left, ⊤) (sectionRing A U.obj)

/-- Finiteness of a quasi-coherent `𝒪_X`-algebra is equivalent to finiteness of its
section algebras as modules on every affine étale object. -/
theorem isFinite_iff {S : Scheme.{u}} {X : AlgebraicSpace S} (A : X.QcAlgebraUnder) :
    IsFinite A ↔
      ∀ U : affineEtaleSite X, Module.Finite Γ(U.obj.left.left, ⊤) (sectionRing A U.obj) :=
  sorry

/-- The structure sheaf `𝒪_X` is finite as an `𝒪_X`-algebra. -/
instance instIsFinite_structureQcAlgebra {S : Scheme.{u}} (X : AlgebraicSpace S) :
    IsFinite (structureQcAlgebra X) :=
  sorry

/-- The property of an `𝒪_X`-algebra of being quasi-coherent and finite. -/
def finiteProperty {S : Scheme.{u}} (X : AlgebraicSpace S) :
    ObjectProperty (Under (commRingStructureSheaf X)) :=
  fun B ↦ ∃ h : qcAlgebraUnderProperty X B, IsFinite ⟨B, h⟩

/-- Membership in `finiteProperty X` means the algebra is quasi-coherent and finite. -/
theorem finiteProperty_iff {S : Scheme.{u}} {X : AlgebraicSpace S}
    (B : Under (commRingStructureSheaf X)) :
    finiteProperty X B ↔ ∃ h : qcAlgebraUnderProperty X B, IsFinite ⟨B, h⟩ :=
  sorry

/-- A bundled quasi-coherent `𝒪_X`-algebra satisfies `finiteProperty` if and only if it is
finite. -/
theorem finiteProperty_obj {S : Scheme.{u}} {X : AlgebraicSpace S} (A : X.QcAlgebraUnder) :
    finiteProperty X A.obj ↔ IsFinite A :=
  sorry

/-- If `X` is a quasi-compact and quasi-separated algebraic space over a scheme `S`, then every
finite quasi-coherent `𝒪_X`-algebra is a small filtered colimit of finite and finitely presented
quasi-coherent `𝒪_X`-algebras with locally surjective transition maps. -/
theorem exists_finite_finitelyPresentable_colimitPresentation_locallySurjective
    {S : Scheme.{u}} {X : AlgebraicSpace S} [IsQuasiCompact X]
    [IsAbsolutelyQuasiSeparated X] (A : X.QcAlgebraUnder) [IsFinite A] :
    ∃ (I : Type u) (_ : SmallCategory I) (_ : IsFiltered I),
      ∃ pres : ColimitPresentation I A.obj,
        (∀ i : I, finiteProperty X (pres.diag.obj i)) ∧
          (∀ i : I, finitelyPresentableProperty X (pres.diag.obj i)) ∧
            ∀ {i i' : I} (f : i ⟶ i'), Sheaf.IsLocallySurjective (pres.diag.map f).right :=
  sorry

/-- A finite quasi-coherent algebra on a quasi-compact quasi-separated algebraic space admits a
locally surjective algebra map from a finite and finitely presented quasi-coherent algebra. -/
theorem exists_finite_finitelyPresentable_locallySurjective
    {S : Scheme.{u}} {X : AlgebraicSpace S} [IsQuasiCompact X]
    [IsAbsolutelyQuasiSeparated X] (A : X.QcAlgebraUnder) [IsFinite A] :
    ∃ (B : X.QcAlgebraUnder) (_ : IsFinite B) (_ : IsFinitePresentation B)
      (f : B.obj ⟶ A.obj), Sheaf.IsLocallySurjective f.right :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.QcAlgebraUnder
