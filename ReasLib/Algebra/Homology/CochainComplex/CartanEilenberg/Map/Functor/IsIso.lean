/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Homology.CochainComplex.CartanEilenberg.Map.Functor
public import ReasLib.Algebra.Homology.CochainComplex.CartanEilenberg.Map.Category.IsIso

/-!
# Isomorphism views after applying a functor to Cartan--Eilenberg maps

The mapped double-complex and its row maps preserve isomorphisms.  These instances are kept in a
small leaf so clients that only need the mapped view do not import the additive calculation API.
-/

@[expose] public section

open CategoryTheory ComplexShape

noncomputable section

universe v₁ v₂ u₁ u₂

namespace CochainComplex.CartanEilenbergResolution.Map

variable {A : Type u₁} [Category.{v₁} A] [Abelian A]
variable {B : Type u₂} [Category.{v₂} B] [Preadditive B]
variable {K L : CochainComplex.Plus A}
variable {I : CartanEilenbergResolution K} {J : CartanEilenbergResolution L}

/-- An isomorphism of resolution maps remains an isomorphism after termwise application of an
additive functor. -/
@[stacks 015J "isomorphism of mapped Cartan-Eilenberg maps"]
instance mapped_isIso (f : Map I J) (F : A ⥤ B) [F.Additive] [IsIso f.hom] :
    IsIso (mapped f F) := sorry

/-- An isomorphism of resolution maps remains an isomorphism on every mapped row. -/
@[stacks 015J "isomorphism of mapped Cartan-Eilenberg rows"]
instance mappedRow_isIso (f : Map I J) (F : A ⥤ B) [F.Additive] (q : ℤ)
    [IsIso f.hom] : IsIso (mappedRow f F q) := sorry

end CochainComplex.CartanEilenbergResolution.Map
