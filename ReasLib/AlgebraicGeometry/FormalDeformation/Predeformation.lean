module

public import Mathlib.CategoryTheory.FiberedCategory.Fiber
public import Mathlib.CategoryTheory.FiberedCategory.BasedCategory
public import Mathlib.CategoryTheory.PUnit
public import ReasLib.CategoryTheory.Fibered.InGroupoids.Basic
public import ReasLib.AlgebraicGeometry.FormalDeformation.ArtinianLocal.Residue

/-!
# Predeformation categories over `ArtinianLocalAlgCat`

A predeformation category is cofibered in groupoids with a nonempty residue fiber
and a unique morphism between each pair of objects in that fiber.
-/

@[expose] public section

open CategoryTheory

universe u v w

variable {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]
variable {F : Type v} [Category.{w} F]

namespace CategoryTheory.Functor

/-- A predeformation category over `ArtinianLocalAlgCat Λ k` is a category cofibered in
groupoids whose fibre over `ArtinianLocalAlgCat.residue Λ k` is nonempty and has a unique
morphism between any two objects. -/
class IsPredeformationCategory (p : F ⥤ ArtinianLocalAlgCat Λ k) : Prop where
  [isCofiberedInGroupoids : IsFibered.InGroupoids p.op]
  nonempty_residueFiber : Nonempty (p.Fiber (ArtinianLocalAlgCat.residue Λ k))
  unique_residueHom (x y : p.Fiber (ArtinianLocalAlgCat.residue Λ k)) :
    Nonempty (x ⟶ y) ∧ Subsingleton (x ⟶ y)

attribute [instance] IsPredeformationCategory.isCofiberedInGroupoids

/-- The identity functor on `ArtinianLocalAlgCat Λ k` is a predeformation category. -/
instance instIsPredeformationCategoryId :
    IsPredeformationCategory (𝟭 (ArtinianLocalAlgCat Λ k)) := sorry

/-- A functor is a predeformation category iff it is cofibered in groupoids and its fibre
over `k` is nonempty with a unique morphism between any two objects. -/
theorem isPredeformationCategory_spec (p : F ⥤ ArtinianLocalAlgCat Λ k) :
    IsPredeformationCategory p ↔
      IsFibered.InGroupoids p.op ∧
        Nonempty (p.Fiber (ArtinianLocalAlgCat.residue Λ k)) ∧
          ∀ x y : p.Fiber (ArtinianLocalAlgCat.residue Λ k),
            Nonempty (x ⟶ y) ∧ Subsingleton (x ⟶ y) :=
  ⟨fun h ↦ ⟨h.isCofiberedInGroupoids, h.nonempty_residueFiber, h.unique_residueHom⟩,
    fun h ↦ IsPredeformationCategory.mk (isCofiberedInGroupoids := h.1) h.2.1 h.2.2⟩

/-- A functor is a predeformation category iff it is cofibered in groupoids and its residue
fibre is equivalent to the discrete category on a singleton. -/
theorem isPredeformationCategory_iff_equiv_punit (p : F ⥤ ArtinianLocalAlgCat Λ k) :
    IsPredeformationCategory p ↔
      IsFibered.InGroupoids p.op ∧
        Nonempty (p.Fiber (ArtinianLocalAlgCat.residue Λ k) ≌ Discrete PUnit) := sorry

/-- A morphism of predeformation categories is a functor commuting with their projections
to `ArtinianLocalAlgCat Λ k`. -/
abbrev PredeformationMorphism {G : Type v} [Category.{w} G]
    (p : F ⥤ ArtinianLocalAlgCat Λ k) (q : G ⥤ ArtinianLocalAlgCat Λ k)
    [IsPredeformationCategory p] [IsPredeformationCategory q] : Type (max v w) :=
  BasedCategory.ofFunctor p ⥤ᵇ BasedCategory.ofFunctor q

end CategoryTheory.Functor
