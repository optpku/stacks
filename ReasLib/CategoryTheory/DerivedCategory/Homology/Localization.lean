module

public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
import Mathlib.Tactic.CrossRefAttribute

/-!
# Homology before and after derived localization

The homology comparison isomorphism identifies the homology map of a cochain morphism with the
map induced after applying the localization functor `DerivedCategory.Q`.  This file packages the
two high-frequency categorical consequences independently of any pseudo-coherence argument.

@stack 064R
-/

@[expose] public section

noncomputable section

open CategoryTheory

universe w v u

namespace CategoryTheory.DerivedCategory.Q

variable {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]

/-- A cochain homology map is invertible exactly when the corresponding derived homology map is
invertible. -/
@[stacks 064R "homology comparison under derived localization"]
theorem homologyMap_isIso_iff {K L : CochainComplex C ℤ} (f : K ⟶ L) (n : ℤ) :
    IsIso (HomologicalComplex.homologyMap f n) ↔
      IsIso ((DerivedCategory.homologyFunctor C n).map (DerivedCategory.Q.map f)) := sorry

/-- A cochain homology map is an epimorphism exactly when the corresponding derived homology map
is an epimorphism. -/
@[stacks 064R "epimorphic homology comparison under derived localization"]
theorem homologyMap_epi_iff {K L : CochainComplex C ℤ} (f : K ⟶ L) (n : ℤ) :
    Epi (HomologicalComplex.homologyMap f n) ↔
      Epi ((DerivedCategory.homologyFunctor C n).map (DerivedCategory.Q.map f)) := sorry

end CategoryTheory.DerivedCategory.Q
