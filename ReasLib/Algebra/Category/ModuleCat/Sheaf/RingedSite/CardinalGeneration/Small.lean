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

/-- Cardinal-generated module sheaves form an essentially small object property relative to the
universe `max u v w` of the site and of the section modules, so their isomorphism classes are
indexed by a type in that universe (rather than in the larger universe of all module sheaves). -/
instance essentiallySmall (κ : Cardinal.{w}) :
    ObjectProperty.EssentiallySmall.{max u v w}
      (fun M : SheafOfModules.{w} R => M.IsKappaGenerated κ) := sorry

/-- There is a family of cardinal-generated module sheaves, indexed by a type in the universe
`max u v w`, such that every cardinal-generated module sheaf is isomorphic to one of them. -/
theorem exists_set_representatives (κ : Cardinal.{w}) :
    ∃ (T : Type (max u v w)) (F : T → SheafOfModules.{w} R),
      (∀ t, (F t).IsKappaGenerated κ) ∧
      ∀ M : SheafOfModules.{w} R, M.IsKappaGenerated κ →
        ∃ t, Nonempty (F t ≅ M) :=
  ObjectProperty.EssentiallySmall.exists_family_representatives
    (fun M : SheafOfModules.{w} R => M.IsKappaGenerated κ)

end IsKappaGenerated

end SheafOfModules
