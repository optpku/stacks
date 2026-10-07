module

import StacksCheckRecall
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import ReasLib.AlgebraicGeometry.CycleGroup.FlatPullback.FiniteLocallyFree

@[expose] public section

open AlgebraicGeometry CategoryTheory

universe u

section

variable
    {S : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    (X Y : Over S) [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
    (f : X ⟶ Y) (d : ℕ) [IsFiniteLocallyFreeOfRank f.left d]

/- A finite locally free morphism is proper. -/
#check (inferInstance : IsProper f.left)

/- A finite locally free morphism is flat. -/
#check (inferInstance : Flat f.left)

/- A finite locally free morphism has relative dimension zero. -/
#check (inferInstance : Scheme.Hom.RelativeDimension f.left 0)

end

/- Lemma 42.15.2: if `f : X ⟶ Y` is finite locally free of degree `d`, then
`f` is proper and flat of relative dimension zero, and `f_* (f^* α) = d • α`
for every degree-`k` cycle `α` on `Y`. -/
@[stacks 02RH] #check
  (AlgebraicGeometry.CycleGroup.mapHom_flatPullback :
    ∀ {S : Scheme.{u}} [UniversallyCatenary S]
      (δ : S → ℤ) [IsDimensionFunction δ]
      (X Y : Over S) [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
      (f : X ⟶ Y) (d : ℕ) [IsFiniteLocallyFreeOfRank f.left d]
      (k : ℤ) (α : CycleGroup Y.left (Y.hom.relativeDimensionFunction δ) k),
      CycleGroup.mapHom f.left (X.hom.relativeDimensionFunction δ)
          (Y.hom.relativeDimensionFunction δ) k
          (CycleGroup.reindex (X.hom.relativeDimensionFunction δ) (add_zero k)
            (CycleGroup.flatPullback δ X Y f 0 k α)) =
        d • α)
