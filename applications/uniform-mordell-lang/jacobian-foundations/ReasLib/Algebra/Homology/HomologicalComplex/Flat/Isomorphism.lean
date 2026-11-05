module

public import ReasLib.Algebra.Homology.HomologicalComplex.Flat
import Mathlib.Tactic.CrossRefAttribute

/-!
# Isomorphism transport for termwise-flat homological complexes

Termwise flatness depends only on the isomorphism class of a homological complex.  This file
owns the shape-general transport API; category-specific files should expose only genuinely useful
specializations.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u v w

namespace HomologicalComplex.IsTermwiseFlat

variable {C : Type u} [Category.{v} C] [Limits.HasZeroMorphisms C] [MonoidalCategory C]
variable {I : Type w} {c : ComplexShape I}

/-- Termwise flatness transports from the source to the target of an isomorphism of homological
complexes. -/
theorem of_iso {K L : HomologicalComplex C c} (hK : K.IsTermwiseFlat) (e : K ≅ L) :
    L.IsTermwiseFlat := sorry

/-- Isomorphic homological complexes are simultaneously termwise flat. -/
@[stacks 06YY "isomorphism invariance of termwise flatness"]
theorem iff_of_iso {K L : HomologicalComplex C c} (e : K ≅ L) :
    K.IsTermwiseFlat ↔ L.IsTermwiseFlat := sorry

end HomologicalComplex.IsTermwiseFlat
