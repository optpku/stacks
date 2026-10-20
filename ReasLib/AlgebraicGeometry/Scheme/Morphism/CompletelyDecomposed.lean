/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FinitePresentation
public import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap
public import Mathlib.AlgebraicGeometry.Morphisms.Immersion
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.AlgebraicGeometry.ResidueField

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open AlgebraicGeometry
open scoped AlgebraicGeometry

universe u v w

namespace AlgebraicGeometry

/-- A family of scheme morphisms to `T` is completely decomposed if every canonical
residue-field point of `T` lifts through some member of the family. -/
class CompletelyDecomposedFamily {I : Type v} {T : Scheme.{u}}
    (X : I → Scheme.{u}) (π : ∀ i, X i ⟶ T) : Prop where
  /-- Every canonical residue-field point of the target lifts through a family member. -/
  exists_lift : ∀ t : T, ∃ i, ∃ s : Spec (T.residueField t) ⟶ X i,
    s ≫ π i = T.fromSpecResidueField t

namespace CompletelyDecomposedFamily

/-- Complete decomposition of a family is equivalent to lifting every canonical
residue-field point through some member of the family. -/
theorem iff_exists_residueField_lift {I : Type v} {T : Scheme.{u}}
    (X : I → Scheme.{u}) (π : ∀ i, X i ⟶ T) :
    CompletelyDecomposedFamily X π ↔
      ∀ t : T, ∃ i, ∃ s : Spec (T.residueField t) ⟶ X i,
        s ≫ π i = T.fromSpecResidueField t := sorry

/-- An isomorphism, viewed as a singleton family, is completely decomposed. -/
instance singletonOfIsIso {X T : Scheme.{u}} (f : X ⟶ T) [IsIso f] :
    CompletelyDecomposedFamily
      (fun _ : PUnit.{1} ↦ X)
      (fun _ : PUnit.{1} ↦ f) := sorry

/-- Dependent composition of completely decomposed families of scheme morphisms is
completely decomposed. -/
instance comp {T : Scheme.{u}} {I : Type v}
    (X : I → Scheme.{u}) (π : ∀ i, X i ⟶ T) [CompletelyDecomposedFamily X π]
    (J : I → Type w) (Y : ∀ i, J i → Scheme.{u})
    (ρ : ∀ i, ∀ j : J i, Y i j ⟶ X i)
    [∀ i, CompletelyDecomposedFamily (Y i) (ρ i)] :
    CompletelyDecomposedFamily (fun p : Sigma J ↦ Y p.1 p.2)
      (fun p : Sigma J ↦ ρ p.1 p.2 ≫ π p.1) := sorry

/-- A completely decomposed family of scheme morphisms remains completely decomposed
after base change along an arbitrary scheme morphism. -/
instance pullback {I : Type v} {Y Y' : Scheme.{u}}
    (X : I → Scheme.{u}) (π : ∀ i, X i ⟶ Y) [CompletelyDecomposedFamily X π]
    (g : Y' ⟶ Y) :
    CompletelyDecomposedFamily (fun i ↦ pullback (π i) g)
      (fun i ↦ pullback.snd (π i) g) := sorry

end CompletelyDecomposedFamily

namespace Scheme.Hom

/-- A scheme morphism is completely decomposed when its singleton family is completely
decomposed. -/
abbrev CompletelyDecomposed {X T : Scheme.{u}} (f : X ⟶ T) : Prop :=
  CompletelyDecomposedFamily
    (fun _ : PUnit.{1} ↦ X)
    (fun _ : PUnit.{1} ↦ f)

namespace CompletelyDecomposed

/-- A scheme morphism is completely decomposed exactly when every canonical residue-field
point of its target lifts through it. -/
theorem iff_exists_residueField_lift {X T : Scheme.{u}} (f : X ⟶ T) :
    CompletelyDecomposed f ↔
      ∀ t : T, ∃ s : Spec (T.residueField t) ⟶ X,
        s ≫ f = T.fromSpecResidueField t := sorry

/-- The composition of completely decomposed scheme morphisms is completely decomposed. -/
instance comp {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    [CompletelyDecomposed f] [CompletelyDecomposed g] :
    CompletelyDecomposed (f ≫ g) := sorry

end CompletelyDecomposed

/-- A locally finitely presented morphism of schemes admitting a residue-field lift over every
target point, with quasi-compact quasi-separated target, admits a finite surjective family of
finite-presentation immersions over which its pullbacks have sections. -/
theorem exists_finite_immersion_cover {X Y : Scheme.{u}} (f : X ⟶ Y)
    (h_decomposed : ∀ y : Y, ∃ σ : Spec (Y.residueField y) ⟶ X,
      σ ≫ f = Y.fromSpecResidueField y)
    [LocallyOfFinitePresentation f] [CompactSpace Y] [QuasiSeparatedSpace Y] :
    ∃ n : ℕ, ∃ Z : Fin n → Scheme.{u}, ∃ z : ∀ i, Z i ⟶ Y,
      Surjective (Limits.Sigma.desc z) ∧
        (∀ i, IsImmersion (z i)) ∧
          (∀ i, FinitePresentation (z i)) ∧
            (∀ i, IsSplitEpi (pullback.snd f (z i))) := sorry

end Scheme.Hom

end AlgebraicGeometry
