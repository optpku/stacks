module

public import ReasLib.Topology.Sheaves.Basis.Basic
import StacksCheckRecall

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory TopologicalSpace

universe u v

variable {X : Type u} [TopologicalSpace X]
variable {B : Set (Opens X)}

/-
The reusable category `BasisOpen B` lives in the neutral basis-open support module. Mathlib has no
generic `Presheaf` alias for an arbitrary category: the canonical owner is the functor category
itself. The construction makes sense for any collection of opens; the source additionally assumes
that `B` is a topological basis.
-/

/- Definition 6.30.1 (1): a presheaf of sets on a topological basis `B` is a contravariant
functor from the category of basis opens to `Type v`. -/
@[stacks 009I "set-valued presheaves on the category of basis opens"]
#check ((BasisOpen B)ᵒᵖ ⥤ Type v)

variable (ℱ 𝒢 : (BasisOpen B)ᵒᵖ ⥤ Type v)

/- Definition 6.30.1 (2): a morphism of presheaves on `B` is a natural transformation, whose
naturality is exactly compatibility with restriction maps. -/
@[stacks 009I "morphisms of basis presheaves as restriction-compatible natural transformations"]
#check (ℱ ⟶ 𝒢)
