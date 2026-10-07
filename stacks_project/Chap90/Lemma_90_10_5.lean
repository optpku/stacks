module

public import Mathlib.CategoryTheory.Discrete.Basic
public import Mathlib.Combinatorics.Quiver.Basic
public import stacks_project.Chap90.Lemma_90_10_5_Associated
public import stacks_project.Chap90.Lemma_90_10_5_Schlessinger

/-!
# Transfer of Schlessinger's conditions to the associated functor

If a category cofibered in groupoids over `ArtinianLocalAlgCat Λ k` satisfies (S1), then so
does the associated functor of isomorphism classes. The same holds for (S2) under an extra
hypothesis on the fibre over `k` or on automorphisms along `k[ε] ⟶ k`.
-/

@[expose] public section

open CategoryTheory ArtinianLocalAlgCat

universe u v w

variable {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]
variable {F : Type v} [Category.{w} F]

namespace CategoryTheory.Functor

/-- Lemma 90.10.5 (1): if a category cofibered in groupoids over `ArtinianLocalAlgCat Λ k`
satisfies (S1), then so does the associated functor of isomorphism classes. -/
@[stacks 06I0]
theorem hasSchlessingerS1_isoClass (p : F ⥤ ArtinianLocalAlgCat Λ k)
    [IsFibered.InGroupoids p.op] [HasSchlessingerS1 p] :
    HasSchlessingerS1 (CategoryOfElements.π (isoClassFunctor p)) := sorry

/-- Lemma 90.10.5 (2): if a category cofibered in groupoids over `ArtinianLocalAlgCat Λ k`
satisfies (S2), then so does the associated functor of isomorphism classes, provided `p` is a
predeformation category, the fibre over `k` is a set or a setoid, or Aut pushforward along every
lift of `k[ε] ⟶ k` is surjective. -/
@[stacks 06I0]
theorem hasSchlessingerS2_isoClass (p : F ⥤ ArtinianLocalAlgCat Λ k)
    [IsFibered.InGroupoids p.op] [HasSchlessingerS2 p]
    (h : IsPredeformationCategory p ∨
      IsDiscrete (p.Fiber (residue Λ k)) ∨
      Quiver.IsThin (p.Fiber (residue Λ k)) ∨
      ∀ {xε x0 : F} (φ : xε ⟶ x0) [p.IsHomLift (dualNumberToResidue Λ k) φ],
        Function.Surjective (autPushforward p φ)) :
    HasSchlessingerS2 (CategoryOfElements.π (isoClassFunctor p)) := sorry

end CategoryTheory.Functor
