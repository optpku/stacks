/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Conormal
public import ReasLib.AlgebraicGeometry.Scheme.ProjectiveBundle.Section
public import ReasLib.CategoryTheory.Monoidal.InvertibleQuotient.Conormal

/-!
# Conormal sheaves of projective-bundle sections

This leaf identifies the conormal sheaf of a section classified by an invertible quotient with
the kernel of that quotient tensored with the chosen tensor inverse of its target.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.ProjectiveBundle

variable {X P : Scheme.{u}} {ℰ : X.Modules} [ℰ.IsQuasicoherent]

/-- For a lift to a represented projective bundle, the kernel-tensor-inverse object of the
classified quotient is isomorphic to the conormal sheaf of the induced base-change section. -/
theorem liftConormal_isIsomorphic
    {T : Scheme.{u}} [HasZeroMorphisms T.Modules] [HasKernels T.Modules]
    (π : P ⟶ X) (hπ : Representation π ℰ) (f : T ⟶ X) (σ : Lift π f) :
    IsIsomorphic
      (CategoryTheory.InvertibleQuotient.conormalObject (hπ.liftEquiv f σ))
      (Scheme.Hom.conormalSheaf σ.baseChangeSection) := sorry

/-- The kernel of the quotient classified by a projective-bundle section, tensored with the
chosen tensor inverse of its target, is isomorphic to the conormal sheaf of the section. -/
theorem sectionConormal_isIsomorphic
    [HasZeroMorphisms X.Modules] [HasKernels X.Modules]
    (π : P ⟶ X) (hπ : Representation π ℰ) (σ : Lift π (𝟙 X)) :
    IsIsomorphic
      (CategoryTheory.InvertibleQuotient.conormalObject (sectionQuotient π hπ σ))
      (Scheme.Hom.conormalSheaf σ.hom) := sorry

end AlgebraicGeometry.Scheme.ProjectiveBundle
