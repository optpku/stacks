/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Topology.Presheaf.ExtensionByInitial.Functor

/-!
# Sheaf extension by an initial object

This module owns the sheaf-level extension-by-initial-object functor along an open-subspace
inclusion. The underlying presheaf construction `jₚ!` is owned by
`TopCat.Presheaf.ExtensionByInitial`.
-/

@[expose] public section

open CategoryTheory TopCat TopologicalSpace
open CategoryTheory.Limits
open TopCat.Opens.Subspace

noncomputable section

universe w v u

namespace TopCat.Sheaf.ExtensionByInitial

variable {X : TopCat.{w}} {C : Type u} [Category.{v} C] [HasInitial C]
variable [CategoryTheory.HasWeakSheafify (Opens.grothendieckTopology X) C]

/-- Sheaf-level extension by the initial object: `j! = sheafify ∘ jₚ!`. -/
noncomputable def functor (U : Opens X) : (space U).Sheaf C ⥤ X.Sheaf C :=
  TopCat.Sheaf.forget C (space U) ⋙
    TopCat.Presheaf.ExtensionByInitial.functor U ⋙
    CategoryTheory.presheafToSheaf (Opens.grothendieckTopology X) C

end TopCat.Sheaf.ExtensionByInitial

/-- Notation `j!` for the sheaf-level extension-by-initial functor. -/
notation:max "j! " U:max => TopCat.Sheaf.ExtensionByInitial.functor U

end

end
