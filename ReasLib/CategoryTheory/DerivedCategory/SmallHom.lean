/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.Algebra.Homology.DerivedCategory.KInjective
public import Mathlib.CategoryTheory.Localization.SmallHom
public import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Small Hom types in a derived localization

This leaf records the reusable smallness interface for the localization of
cochain complexes at quasi-isomorphisms.  The primitive owner remains
`Localization.HasSmallLocalizedHom`; the declarations below only expose the
K-injective computation and its two transport layers.
-/

open CategoryTheory
open CategoryTheory.Localization
open ComplexShape

universe w v u

namespace CategoryTheory.DerivedCategory

variable {𝒜 : Type u} [Category.{v} 𝒜] [Abelian 𝒜]

/- The proof of this statement uses the standard localization model, but the
   public interface intentionally needs no chosen `HasDerivedCategory` instance. -/
/-- A K-injective target computes the localized Hom type through the homotopy
category, hence that Hom type is `w`-small whenever `𝒜` is `w`-locally small. -/
@[stacks 09PA]
theorem LocalizedHom.of_kInjective
    [LocallySmall.{w} 𝒜] (K I : CochainComplex 𝒜 ℤ) [I.IsKInjective] :
    HasSmallLocalizedHom.{w}
      (HomologicalComplex.quasiIso 𝒜 (up ℤ)) K I := sorry

/-- Smallness of localized morphisms is transported across a quasi-isomorphism
from an arbitrary target to a K-injective target. -/
@[stacks 09PA]
theorem LocalizedHom.of_quasiIso
    [LocallySmall.{w} 𝒜] (K : CochainComplex 𝒜 ℤ)
    {L I : CochainComplex 𝒜 ℤ} [I.IsKInjective] (f : L ⟶ I)
    (hf : QuasiIso f) :
    HasSmallLocalizedHom.{w}
      (HomologicalComplex.quasiIso 𝒜 (up ℤ)) K L := sorry

/-- If a target admits a quasi-isomorphism to a K-injective replacement, then
all localized morphisms into that target form a `w`-small type. -/
@[stacks 09PA]
theorem LocalizedHom.of_replacement
    [LocallySmall.{w} 𝒜] (K L : CochainComplex 𝒜 ℤ)
    (hL : ∃ (I : CochainComplex 𝒜 ℤ) (_ : I.IsKInjective) (f : L ⟶ I),
      QuasiIso f) :
    HasSmallLocalizedHom.{w}
      (HomologicalComplex.quasiIso 𝒜 (up ℤ)) K L := sorry

end CategoryTheory.DerivedCategory
