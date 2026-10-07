module

public import Mathlib.CategoryTheory.FiberedCategory.Fiber
public import ReasLib.CategoryTheory.Fibered.InGroupoids.Basic
public import stacks_project.Chap90.Definition_90_7_3_ArtinianLocal

/-!
# Predeformation categories over `ArtinianLocalAlgCat`

A predeformation category is a category cofibered in groupoids over `C_Λ` whose
fibre over the residue field `k` is equivalent to a point: it is nonempty and
has a unique morphism between any two objects.
-/

@[expose] public section

open CategoryTheory IsLocalRing

universe u v w

variable (Λ k : Type u) [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]

namespace ArtinianLocalAlgCat

/-- The residue field `k`, viewed as an object of `ArtinianLocalAlgCat Λ k`. -/
def residue : ArtinianLocalAlgCat Λ k :=
  of k ((Ideal.quotientEquivAlgOfEq Λ maximalIdeal_eq_bot).trans (AlgEquiv.quotientBot Λ k))

/-- The bundled residue object has carrier `k`. -/
theorem residue_carrier : (residue Λ k).carrier = k := sorry

end ArtinianLocalAlgCat

variable {Λ k}
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
            Nonempty (x ⟶ y) ∧ Subsingleton (x ⟶ y) := sorry

end CategoryTheory.Functor

