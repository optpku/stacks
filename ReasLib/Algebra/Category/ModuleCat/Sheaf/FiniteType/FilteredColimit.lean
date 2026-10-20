module

public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Colim
public import Mathlib.Topology.Sheaves.Abelian
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.FiniteType

/-!
# Finite-type module sheaves in filtered colimits

On a quasi-compact topological space, finite type forces a filtered colimit of module sheaves to
be reached epimorphically at one stage.  For a diagram of monomorphisms, Mathlib's AB5 API makes
every colimit coprojection monic, so the colimit stabilizes at a stage.
-/

@[expose] public section

open CategoryTheory Limits

noncomputable section

universe u

namespace SheafOfModules.IsFiniteType.FilteredColimit

variable {X : TopCat.{u}} [CompactSpace X]
variable {𝒪 : TopCat.Sheaf RingCat.{u} X}
variable {I : Type u} [SmallCategory I] [IsFiltered I]
variable (ℱ : I ⥤ SheafOfModules 𝒪)

/-- Lemma 17.9.7 (01BB) (1), ringed-space-independent form: if a filtered colimit of module
sheaves on a quasi-compact space is of finite type, then one colimit coprojection is epi. -/
@[stacks 01BB "(1), module-sheaf owner"]
theorem exists_epi_ι [(colimit ℱ).IsFiniteType] :
    ∃ i : I, Epi (colimit.ι ℱ i) := sorry

/-- Lemma 17.9.7 (01BB) (2), ringed-space-independent form: a finite-type filtered colimit
of a diagram of monomorphisms on a quasi-compact space stabilizes at one stage. -/
@[stacks 01BB "(2), module-sheaf owner"]
theorem exists_isIso_ι
    [(colimit ℱ).IsFiniteType]
    [∀ ⦃i j : I⦄ (f : i ⟶ j), Mono (ℱ.map f)] :
    ∃ i : I, IsIso (colimit.ι ℱ i) := sorry

end SheafOfModules.IsFiniteType.FilteredColimit
