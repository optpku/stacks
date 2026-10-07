module

public import Mathlib.CategoryTheory.FiberedCategory.HomLift
public import Mathlib.Order.Bounds.Defs
public import stacks_project.Chap90.Lemma_90_13_3_Quotient

/-!
# Lift ideals along a surjection in `C_Λ`

For a functor `p : F ⥤ ArtinianLocalAlgCat Λ k` and a morphism `f : B ⟶ A`, an
ideal `J ≤ RingHom.ker f.hom.toRingHom` is a lift ideal of an object `x` over `A`
when some morphism `y ⟶ x` in `F` lies over `quotientFactor f J hJ`.
-/

@[expose] public section

open CategoryTheory ArtinianLocalAlgCat IsLocalRing

universe u v w

variable {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]
variable {F : Type v} [Category.{w} F]

namespace CategoryTheory.Functor

/-- Ideals `J ≤ RingHom.ker f.hom.toRingHom` for which some `y ⟶ x` lies over
`ArtinianLocalAlgCat.quotientFactor f J hJ`. -/
def liftIdeals (p : F ⥤ ArtinianLocalAlgCat Λ k) {B A : ArtinianLocalAlgCat Λ k}
    (f : B ⟶ A) {x : F} (_hx : p.obj x = A) : Set (Ideal B.carrier) :=
  {J | ∃ (hJ : J ≤ RingHom.ker f.hom.toRingHom) (y : F) (φ : y ⟶ x),
      p.IsHomLift (quotientFactor f J hJ) φ}

/-- Membership in `liftIdeals` from a homogeneous lift over `quotientFactor`. -/
theorem mem_liftIdeals (p : F ⥤ ArtinianLocalAlgCat Λ k)
    {B A : ArtinianLocalAlgCat Λ k} (f : B ⟶ A) {x : F} (hx : p.obj x = A)
    {J : Ideal B.carrier} (hJ : J ≤ RingHom.ker f.hom.toRingHom)
    {y : F} {φ : y ⟶ x} (hφ : p.IsHomLift (quotientFactor f J hJ) φ) :
    J ∈ p.liftIdeals f hx := sorry

/-- An ideal lies in `liftIdeals` if and only if it is contained in the kernel and
some morphism `y ⟶ x` lies over the corresponding `quotientFactor`. -/
theorem mem_liftIdeals_iff (p : F ⥤ ArtinianLocalAlgCat Λ k)
    {B A : ArtinianLocalAlgCat Λ k} (f : B ⟶ A) {x : F} (hx : p.obj x = A)
    {J : Ideal B.carrier} :
    J ∈ p.liftIdeals f hx ↔
      ∃ (hJ : J ≤ RingHom.ker f.hom.toRingHom) (y : F) (φ : y ⟶ x),
        p.IsHomLift (quotientFactor f J hJ) φ := sorry

/-- The canonical candidate for a least lift ideal, as the infimum of `liftIdeals`. -/
noncomputable def smallestLiftIdeal (p : F ⥤ ArtinianLocalAlgCat Λ k)
    {B A : ArtinianLocalAlgCat Λ k} (f : B ⟶ A) {x : F} (hx : p.obj x = A) :
    Ideal B.carrier :=
  sInf (p.liftIdeals f hx)

/-- `smallestLiftIdeal` is the infimum of `liftIdeals`. -/
theorem smallestLiftIdeal_eq_sInf (p : F ⥤ ArtinianLocalAlgCat Λ k)
    {B A : ArtinianLocalAlgCat Λ k} (f : B ⟶ A) {x : F} (hx : p.obj x = A) :
    p.smallestLiftIdeal f hx = sInf (p.liftIdeals f hx) := sorry

end CategoryTheory.Functor
