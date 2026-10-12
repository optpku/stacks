/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.CardinalGeneration
public import ReasLib.CategoryTheory.ObjectProperty.Representatives

/-!
# Smallness of cardinal-generated module sheaves

Cardinal-bounded local generation is invariant under isomorphism and defines an essentially
small object property. Consequently, its isomorphism classes admit a set of representatives.
-/

@[expose] public section

open CategoryTheory

universe u v w

namespace SheafOfModules

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable {R : Sheaf J RingCat.{w}}
variable [∀ U : C, HasWeakSheafify (J.over U) AddCommGrpCat.{w}]
variable [∀ U : C, (J.over U).WEqualsLocallyBijective AddCommGrpCat.{w}]

/-- Cardinal-bounded local generation is equivalent for isomorphic module sheaves. -/
theorem isKappaGenerated_iff_of_iso {M N : SheafOfModules.{w} R}
    (e : M ≅ N) (κ : Cardinal.{w}) :
    M.IsKappaGenerated κ ↔ N.IsKappaGenerated κ := sorry

/-- Cardinal-bounded local generation is invariant under isomorphism. -/
instance isKappaGenerated_isClosedUnderIsomorphisms (κ : Cardinal.{w}) :
    ObjectProperty.IsClosedUnderIsomorphisms
      (fun M : SheafOfModules.{w} R => M.IsKappaGenerated κ) := sorry

namespace IsKappaGenerated

/-- Cardinal-generated module sheaves form an essentially small object property at the natural
universe of the module-sheaf category. -/
instance essentiallySmall (κ : Cardinal.{w}) :
    ObjectProperty.EssentiallySmall.{max u v w + 1}
      (fun M : SheafOfModules.{w} R => M.IsKappaGenerated κ) := sorry

/-- There is a set of cardinal-generated module sheaves containing a representative of every
isomorphism class of cardinal-generated module sheaves. -/
theorem exists_set_representatives (κ : Cardinal.{w}) :
    ∃ S : Set (SheafOfModules.{w} R),
      (∀ M ∈ S, M.IsKappaGenerated κ) ∧
      ∀ M : SheafOfModules.{w} R, M.IsKappaGenerated κ →
        ∃ N ∈ S, Nonempty (N ≅ M) := sorry

end IsKappaGenerated

end SheafOfModules
