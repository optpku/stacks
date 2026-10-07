module

public import Mathlib.Algebra.Category.ModuleCat.AB
public import ReasLib.Algebra.Homology.DerivedCategory.Completeness.Category
public import ReasLib.RingTheory.Ideal.Principal
import Mathlib.Tactic.CrossRefAttribute

/-!
# Presentations of modules complete for a principal ideal

A module is derived complete for a regular principal element exactly when it has a short exact
presentation by ordinarily complete modules with no torsion for that element.

@stack 09AT
-/

@[expose] public section

open CategoryTheory CategoryTheory.ObjectProperty

universe u

namespace ModuleCat.IsDerivedCompleteWithRespectTo

variable {A : Type u} [CommRing A]

/-- Example 15.94.3 (Stacks `09AT`): if `f` is a nonzerodivisor, an `A`-module `M` is derived
complete for `(f)` exactly when it is the cokernel in a short exact presentation by
`(f)`-adically complete modules whose `f`-torsion submodules vanish. -/
@[stacks 09AT]
theorem principal_iff_exists_adicCompletePresentation
    (f : A) (M : ModuleCat.{u} A) (hf : IsRegular f) :
    M.IsDerivedCompleteWithRespectTo (principalIdeal f) ↔
      ∃ (K L : ModuleCat.{u} A) (ι : K ⟶ L) (π : L ⟶ M) (h : ι ≫ π = 0),
        (ShortComplex.mk ι π h).ShortExact ∧
          IsAdicComplete (principalIdeal f) K ∧
          IsAdicComplete (principalIdeal f) L ∧
          Submodule.torsionBy A K f = ⊥ ∧
          Submodule.torsionBy A L f = ⊥ := sorry

end ModuleCat.IsDerivedCompleteWithRespectTo
