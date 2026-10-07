module

public import stacks_project.Chap03.Lemma_3_9_4_Size
public import Mathlib.AlgebraicGeometry.Sites.Fpqc

@[expose] public section

noncomputable section

universe u v

open AlgebraicGeometry CategoryTheory
open scoped Cardinal AlgebraicGeometry

namespace AlgebraicGeometry.Scheme

/-- Lemma 3.9.11: if `f : X ⟶ Y` is a morphism of schemes and `{g j : Yj j ⟶ Y}` is an
fpqc covering of `Y` such that each `g j` factors through `f`, then `Y.size ≤ X.size`. -/
@[stacks 0AHK]
theorem size_le_of_fpqcCovering_factors {X Y : Scheme.{u}} (f : X ⟶ Y) {ι : Type v}
    (Yj : ι → Scheme.{u}) (g : (j : ι) → Yj j ⟶ Y)
    (hg : Presieve.ofArrows Yj g ∈ fpqcPrecoverage Y)
    (hfactor : ∀ j, ∃ h : Yj j ⟶ X, h ≫ f = g j) :
    Y.size ≤ X.size := sorry

/-- The size of `Y` is at most the size of `X` if some fpqc cover of `Y` factors through
`f : X ⟶ Y`. -/
theorem size_le_of_fpqcCover_factors {X Y : Scheme.{u}} (f : X ⟶ Y)
    (𝒰 : Y.Cover.{v} fpqcPrecoverage)
    (hfactor : ∀ j, ∃ h : 𝒰.X j ⟶ X, h ≫ f = 𝒰.f j) :
    Y.size ≤ X.size := sorry

/-- If the sieve of morphisms factoring through `f : X ⟶ Y` is an fpqc covering sieve, then
`Y.size ≤ X.size`. -/
theorem size_le_of_generateSingleton_mem_fpqcTopology {X Y : Scheme.{u}} (f : X ⟶ Y)
    (hf : Sieve.generateSingleton f ∈ fpqcTopology Y) :
    Y.size ≤ X.size := sorry

/-- A flat, surjective, quasi-compact morphism `f : X ⟶ Y` satisfies `Y.size ≤ X.size`. -/
theorem size_le_of_flat_surjective_quasiCompact {X Y : Scheme.{u}} (f : X ⟶ Y)
    [Flat f] [Surjective f] [QuasiCompact f] :
    Y.size ≤ X.size := sorry

end AlgebraicGeometry.Scheme
