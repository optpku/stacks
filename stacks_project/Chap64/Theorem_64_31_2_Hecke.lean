/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.NumberTheory.Automorphic.UnramifiedHecke
public import stacks_project.Chap64.Theorem_64_31_2_Eigenform
public import stacks_project.Chap64.Theorem_64_31_2_Frobenius

@[expose] public section
open AlgebraicGeometry AlgebraicGeometry.Scheme AlgebraicGeometry.SchemeOverField Matrix
open Finset
noncomputable section
universe u v
namespace AlgebraicGeometry.SchemeOverField
variable {k : Type u} [Field k] {Λ : Type v} [CommRing Λ]
variable (X : SchemeOverField k)
variable [Curve X] [Smooth X.hom] [Projective X.hom] [GeometricallyIrreducible X.hom]
variable [Fintype k] [Invertible (ringChar k : Λ)]

/-- Compatibility spelling for the canonical uniformizer. -/
abbrev chosenUniformizer (v : closedPoints X.left) : (completion X v)ˣ := uniformizer X v

/-! Typed checks preserve the chapter-facing Hecke API. -/
#check (residueRep X : ∀ v : closedPoints X.left, X.left.residueField v.1 → completion X v)
#check (heckeUMatrix X : ∀ v : closedPoints X.left, (completion X v)ˣ → GL (Fin 2) (adeleRing X))
#check (heckeTDiag X : ∀ v : closedPoints X.left, (completion X v)ˣ → GL (Fin 2) (adeleRing X))
#check (heckeTOff X : ∀ v : closedPoints X.left, (completion X v)ˣ → completion X v → GL (Fin 2) (adeleRing X))
#check (UnramifiedCuspForm.smul X : ∀ (a : Λ), UnramifiedCuspForm X Λ → UnramifiedCuspForm X Λ)
#check (heckeU X : ∀ v : closedPoints X.left, UnramifiedCuspForm X Λ → UnramifiedCuspForm X Λ)
#check (heckeT X : ∀ v : closedPoints X.left, UnramifiedCuspForm X Λ → UnramifiedCuspForm X Λ)
#check (IsEigenform X : UnramifiedCuspForm X Λ → Eigenform X Λ → Prop)

end AlgebraicGeometry.SchemeOverField
