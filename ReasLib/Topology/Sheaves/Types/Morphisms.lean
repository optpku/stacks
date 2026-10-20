module

public import Mathlib.Topology.Sheaves.LocallySurjective
public import Mathlib.Topology.Sheaves.Sheaf

/-!
# Morphisms of type-valued sheaves

The categorical predicates `Mono` and `Epi` remain the owners.  Standard sectionwise criteria are
already provided by `NatTrans.mono_iff_mono_app`, `NatTrans.epi_iff_epi_app`, and the concrete
category criteria for `Type`; the genuinely useful topological bridges supplied here are the
stalkwise criteria.  The stalkwise monomorphism convenience theorem is kept
because it is a common Type-valued consumer surface and is explicitly built on mathlib's generic
stalk theorem.  Subfunctors and the sheaf condition are already provided by
`CategoryTheory.Subfunctor` and `Presieve.IsSheaf`, so this module does not introduce a second
subsheaf wrapper.
-/

@[expose] public section

open CategoryTheory TopologicalSpace
open TopCat.Presheaf

universe u

variable {X : TopCat.{u}}

namespace TopCat.Sheaf

/-- A morphism of `Type`-valued sheaves is monic exactly when all induced stalk maps are injective.

This is the Type-valued spelling of mathlib's `TopCat.Presheaf.mono_iff_stalk_mono` together with
`CategoryTheory.mono_iff_injective`. -/
theorem mono_iff_stalk_injective {ℱ 𝒢 : X.Sheaf (Type u)} (φ : ℱ ⟶ 𝒢) :
    Mono φ ↔ ∀ x : X, Function.Injective ((stalkFunctor (Type u) x).map φ.hom) := sorry

/-- A morphism of `Type`-valued sheaves is epic exactly when all induced stalk maps are
surjective. -/
theorem epi_iff_stalk_surjective {ℱ 𝒢 : X.Sheaf (Type u)} (φ : ℱ ⟶ 𝒢) :
    Epi φ ↔ ∀ x : X, Function.Surjective ((stalkFunctor (Type u) x).map φ.hom) := sorry

/-- A morphism of `Type`-valued sheaves is an isomorphism exactly when all induced stalk maps
are bijective. -/
theorem isIso_iff_stalk_bijective {ℱ 𝒢 : X.Sheaf (Type u)} (φ : ℱ ⟶ 𝒢) :
    IsIso φ ↔ ∀ x : X, Function.Bijective ((stalkFunctor (Type u) x).map φ.hom) := sorry

end TopCat.Sheaf
