/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Comma.Over.Basic
public import ReasLib.AlgebraicGeometry.LocallyRingedSpace.ClosedSubspace.Basic
public import ReasLib.AlgebraicGeometry.LocallyRingedSpace.IdealQuotient.ClosedImmersion
public import ReasLib.AlgebraicGeometry.LocallyRingedSpace.IdealQuotient.Factorization
import Mathlib.Tactic.CrossRefAttribute

/-!
# Comparison of associated closed subspaces

This leaf compares any realization of an associated closed subspace with the canonical ideal
quotient. The forward map is explicit quotient-eliminator data. Invertibility and uniqueness are
exposed as propositions; no inverse is extracted from a deferred `IsIso` proof.
-/

@[expose] public section

open CategoryTheory
open AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.LocallyRingedSpace

variable {X Y Z : LocallyRingedSpace.{u}}
variable {I : IdealSubobject Y} {f : X ⟶ Y} {i : Z ⟶ Y}

/-- The canonical map from an associated closed subspace to the ideal quotient representing its
specified ideal. -/
@[stacks 01HO "comparison with the canonical ideal quotient"]
noncomputable def ClosedSubspace.IsAssociated.toIdealQuotient
    (hi : ClosedSubspace.IsAssociated i I) :
    Z ⟶ IdealQuotient.space I :=
  IdealQuotient.lift I i hi.le_kernel

/-- The canonical comparison with the ideal quotient lies over the ambient locally ringed
space. -/
@[reassoc, simp, stacks 01HO "canonical ideal-quotient comparison triangle"]
theorem ClosedSubspace.IsAssociated.toIdealQuotient_ι
    (hi : ClosedSubspace.IsAssociated i I) :
    hi.toIdealQuotient ≫ IdealQuotient.ι I = i := sorry

/-- The canonical comparison is the unique morphism from an associated realization to the ideal
quotient over the ambient locally ringed space. -/
@[stacks 01HO "canonical ideal-quotient comparison uniqueness"]
theorem ClosedSubspace.IsAssociated.toIdealQuotient_unique
    (hi : ClosedSubspace.IsAssociated i I)
    (g : Z ⟶ IdealQuotient.space I) (hg : g ≫ IdealQuotient.ι I = i) :
    g = hi.toIdealQuotient := sorry

/-- The canonical comparison from an associated realization to the ideal quotient is
invertible. -/
@[stacks 01HO "associated realization comparison is invertible"]
theorem ClosedSubspace.IsAssociated.toIdealQuotient_isIso
    (hi : ClosedSubspace.IsAssociated i I) :
    IsIso hi.toIdealQuotient := sorry

/-- Two realizations of the same associated closed subspace have a unique comparison morphism
over the ambient space. -/
@[stacks 01HO "unique comparison of associated closed subspaces"]
theorem ClosedSubspace.IsAssociated.existsUnique_hom
    (hf : ClosedSubspace.IsAssociated f I)
    (hi : ClosedSubspace.IsAssociated i I) :
    ∃! g : X ⟶ Z, g ≫ i = f := sorry

/-- Comparison morphisms over the ambient space into an associated closed subspace are equal. -/
@[stacks 01HO "extensionality for associated closed subspaces"]
theorem ClosedSubspace.IsAssociated.hom_ext
    (hi : ClosedSubspace.IsAssociated i I)
    {g g' : X ⟶ Z} (hg : g ≫ i = f) (hg' : g' ≫ i = f) :
    g = g' := sorry

/-- Morphisms in the slice category into an associated closed subspace form a subsingleton. -/
@[stacks 01HO "slice morphisms into an associated closed subspace"]
theorem ClosedSubspace.IsAssociated.overHom_subsingleton
    (hi : ClosedSubspace.IsAssociated i I) (f : X ⟶ Y) :
    Subsingleton (Over.mk f ⟶ Over.mk i) := sorry

/-- Lemma 26.4.5: two realizations of the same associated closed subspace are uniquely
isomorphic over the ambient space. -/
@[stacks 01HO]
theorem ClosedSubspace.IsAssociated.existsUnique_iso
    (hf : ClosedSubspace.IsAssociated f I)
    (hi : ClosedSubspace.IsAssociated i I) :
    ∃! e : X ≅ Z, e.hom ≫ i = f := sorry

/-- A closed immersion is uniquely isomorphic over its target to any realization of the closed
subspace attached to its kernel ideal. -/
@[stacks 01HO "kernel ideal"]
theorem IsClosedImmersion.existsUnique_iso_to_associated
    (hf : IsClosedImmersion f)
    (hi : ClosedSubspace.IsAssociated i (Hom.kernelIdealSubobject f)) :
    ∃! e : X ≅ Z, e.hom ≫ i = f := sorry

/-- Isomorphisms in the slice category into an associated closed subspace form a subsingleton. -/
@[stacks 01HO "slice isomorphisms into an associated closed subspace"]
theorem ClosedSubspace.IsAssociated.overIso_subsingleton
    (hi : ClosedSubspace.IsAssociated i I) (f : X ⟶ Y) :
    Subsingleton (Over.mk f ≅ Over.mk i) := sorry

end AlgebraicGeometry.LocallyRingedSpace
