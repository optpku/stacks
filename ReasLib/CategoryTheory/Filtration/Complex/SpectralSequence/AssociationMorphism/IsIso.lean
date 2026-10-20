/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Filtration.Complex.SpectralSequence.AssociationMorphism

/-!
# Isomorphism transport for associated spectral-sequence morphisms

The association morphism is the unique lift of a filtered-complex morphism. Consequently an
isomorphism of filtered complexes lifts to an isomorphism of the associated spectral sequences.
This support leaf keeps that transport available without forcing applications to construct the
inverse lift manually.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe v u

namespace CategoryTheory.FilteredComplex.Association.Hom

variable {C : Type u} [Category.{v} C] [Abelian C]
variable {K L : FilteredComplex C}
variable {E E' : CohomologicalSpectralSequence C 0}
variable {A : FilteredComplex.Association K E}
variable {B : FilteredComplex.Association L E'}
variable {α : K ⟶ L}

/-- The spectral-sequence component of an associated morphism is an isomorphism whenever its
underlying filtered-complex morphism is an isomorphism. -/
@[stacks 012O "isomorphism transport for associated spectral-sequence morphisms"]
noncomputable instance hom_isIso (φ : Association.Hom A B α) [IsIso α] : IsIso φ.hom := sorry

/-- Every page component of an associated spectral-sequence isomorphism is an isomorphism. -/
@[stacks 012O "page-component isomorphism transport for associated spectral-sequence morphisms"]
noncomputable instance hom_f_isIso (φ : Association.Hom A B α) (r : ℤ) (hr : 0 ≤ r)
    (p q : ℤ) [IsIso α] : IsIso ((φ.hom.hom r hr).f (p, q)) := sorry

variable (φ : Association.Hom A B α) [IsIso α]
#synth IsIso φ.hom
#synth IsIso ((φ.hom.hom 1).f (0, 0))

end CategoryTheory.FilteredComplex.Association.Hom
