module

public import ReasLib.CategoryTheory.Fibered.InGroupoids.Basic
public import stacks_project.Chap90.Definition_90_10_1_Schlessinger
public import stacks_project.Chap90.Lemma_90_13_3_Quotient
public import stacks_project.Chap90.Lemma_90_13_3_LiftIdeal

/-!
# Least lift ideal along a kernel annihilated by the maximal ideal

If a category cofibered in groupoids over `C_Λ` satisfies (S1), then along a
surjection whose kernel is annihilated by the source maximal ideal the set of
ideals through which an object lifts has a least element.
-/

@[expose] public section

open CategoryTheory ArtinianLocalAlgCat IsLocalRing

universe u v w

variable {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]
variable {F : Type v} [Category.{w} F]

namespace CategoryTheory.Functor

/-- Lemma 90.13.3: if `p : F ⥤ ArtinianLocalAlgCat Λ k` is cofibered in groupoids
and satisfies (S1), and `f : B ⟶ A` is a surjection in `ArtinianLocalAlgCat Λ k`
whose kernel is annihilated by `maximalIdeal B.carrier`, then for `x` over `A`
the set `p.liftIdeals f hx` of ideals `J ≤ RingHom.ker f.hom.toRingHom` for which
some `y ⟶ x` lies over `quotientFactor f J hJ` has a least element, namely
`p.smallestLiftIdeal f hx`. -/
@[stacks 06SZ]
theorem smallestLiftIdeal_isLeast (p : F ⥤ ArtinianLocalAlgCat Λ k)
    [IsFibered.InGroupoids p.op] [HasSchlessingerS1 p]
    {B A : ArtinianLocalAlgCat Λ k} (f : B ⟶ A)
    (hf : Function.Surjective f.hom)
    (hI : maximalIdeal B.carrier * RingHom.ker f.hom.toRingHom = ⊥)
    {x : F} (hx : p.obj x = A) :
    IsLeast (p.liftIdeals f hx) (p.smallestLiftIdeal f hx) := sorry

end CategoryTheory.Functor
