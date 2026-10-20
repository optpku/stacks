module

public import ReasLib.Algebra.Homology.HomologicalComplex.ShortExact.QuasiIso
public import Mathlib.Algebra.Homology.DerivedCategory.ShortExact
public import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Isomorphisms of derived triangles from short exact maps

The canonical triangle morphism is already constructed by Mathlib as
`DerivedCategory.triangleOfSES.map`.  This leaf adds only the reusable
instance-friendly criterion for it to be an isomorphism.
-/

open CategoryTheory
open CategoryTheory.Pretriangulated
open HomologicalComplex

universe w v u

namespace CategoryTheory.DerivedCategory

variable {𝒜 : Type u} [Category.{v} 𝒜] [Abelian 𝒜] [HasDerivedCategory.{w} 𝒜]

/-- Lemma 13.12.2 (`0153`): if the first two vertical maps of a morphism of short exact
sequences of cochain complexes are quasi-isomorphisms, the induced derived triangle map is an
isomorphism.  The quasi-isomorphism hypotheses are instances so that the three localized maps are
available to downstream typeclass search. -/
@[stacks 0153]
theorem triangleOfSES.map_isIso_of_quasiIso
    {S T : ShortComplex (CochainComplex 𝒜 ℤ)}
    (hS : S.ShortExact) (hT : T.ShortExact) (φ : S ⟶ T)
    [QuasiIso φ.τ₁] [QuasiIso φ.τ₂] :
    IsIso (_root_.DerivedCategory.triangleOfSES.map hS hT φ) := sorry

end CategoryTheory.DerivedCategory
