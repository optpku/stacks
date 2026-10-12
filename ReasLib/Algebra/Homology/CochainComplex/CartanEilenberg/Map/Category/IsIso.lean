/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Homology.CochainComplex.CartanEilenberg.Map.Category

/-!
# Isomorphism projections for bundled Cartan--Eilenberg maps

An isomorphism in the bundled resolution category has isomorphic source and double-complex
components.  These projection instances are the bridge used by the view and total support
leaves; they avoid asking downstream code to unpack the bundled category morphism manually.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe v u

namespace CochainComplex.CartanEilenbergResolution.Bundled

variable {A : Type u} [Category.{v} A] [Abelian A]

/-- The double-complex component of a bundled resolution isomorphism is an isomorphism. -/
@[stacks 015J "double-complex component of a Cartan-Eilenberg isomorphism"]
instance hom_isIso {X Y : Bundled A} (f : X ⟶ Y) [IsIso f] : IsIso f.hom := sorry

/-- The source-complex component of a bundled resolution isomorphism is an isomorphism. -/
@[stacks 015J "source component of a Cartan-Eilenberg isomorphism"]
instance base_isIso {X Y : Bundled A} (f : X ⟶ Y) [IsIso f] : IsIso f.base := sorry

section

variable {X Y : Bundled A} (f : X ⟶ Y) [IsIso f]

#synth IsIso f.hom
#synth IsIso f.base
#synth IsIso f.base.hom

end

end CochainComplex.CartanEilenbergResolution.Bundled
