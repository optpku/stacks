module

public import ReasLib.CategoryTheory.Fibered.Stack.Stackification.Construction.SmallHoms
public import Mathlib.AlgebraicGeometry.Sites.Fpqc
public import Mathlib.AlgebraicGeometry.Sites.Pretopology
public import Mathlib.CategoryTheory.Sites.Over

/-!
# Actual small fppf families inside a covering sieve

Native scheme-cover refinement gives a family indexed in the original scheme
universe. Its arrows are bundled in the slice without enlarging that index.
-/

@[expose] public section

open CategoryTheory Opposite
open CategoryTheory.Functor.StackificationConstruction.DescentCompletion

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidsOver.Stackification

variable {S : Scheme.{u}}

local instance : MorphismProperty.IsMultiplicative
    ((@Flat ⊓ @LocallyOfFinitePresentation) : MorphismProperty Scheme.{u}) where
  id_mem X := ⟨inferInstance, inferInstance⟩
  comp_mem f g hf hg := by
    letI := hf.1
    letI := hf.2
    letI := hg.1
    letI := hg.2
    exact ⟨inferInstance, inferInstance⟩

/-- The native small covering family refining the base scheme sieve. -/
def underlyingCover {U : Over S} (R : (Scheme.fppfTopology.over S).Cover U) :
    Scheme.Cover.{u} Scheme.fppfPrecoverage U.left :=
  Classical.choose (Scheme.exists_cover_of_mem_grothendieckTopology
    (P := @Flat ⊓ @LocallyOfFinitePresentation)
    ((GrothendieckTopology.mem_over_iff (J := Scheme.fppfTopology) _).mp R.2))

/-- Every native chosen arrow lies in the original specified covering sieve. -/
theorem underlyingCover_member {U : Over S}
    (R : (Scheme.fppfTopology.over S).Cover U) (i : (underlyingCover R).I₀) :
    R (Over.homMk ((underlyingCover R).f i) :
      Over.mk ((underlyingCover R).f i ≫ U.hom) ⟶ U) := by
  apply (Sieve.overEquiv_iff _ _).mp
  exact Classical.choose_spec (Scheme.exists_cover_of_mem_grothendieckTopology
    (P := @Flat ⊓ @LocallyOfFinitePresentation)
    ((GrothendieckTopology.mem_over_iff (J := Scheme.fppfTopology) _).mp R.2))
      _ _ (Presieve.ofArrows.mk i)

/-- The specified sieve has an actual small fppf refinement over the original base. -/
def smallRefinement {U : Over S} (R : (Scheme.fppfTopology.over S).Cover U) :
    SmallRefinement.{u + 1, u, u} (Scheme.fppfTopology.over S) R where
  Index := (underlyingCover R).I₀
  object i := Over.mk ((underlyingCover R).f i ≫ U.hom)
  arrow i := Over.homMk ((underlyingCover R).f i)
  member := underlyingCover_member R
  covering := by
    rw [GrothendieckTopology.mem_over_iff, Sieve.overEquiv_ofArrows]
    exact (underlyingCover R).mem_grothendieckTopology

end AlgebraicGeometry.GroupoidsOver.Stackification
