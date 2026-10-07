module

public import stacks_project.Chap90.Definition_90_19_1_InfinitesimalAut

/-!
# Infinitesimal automorphisms of a morphism in a category cofibered in groupoids
-/

@[expose] public section

open CategoryTheory Functor.Fiber

universe u v w

variable {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]
variable {F : Type v} [Category.{w} F]

/-- Definition 90.19.1: let `p : F ⥤ ArtinianLocalAlgCat Λ k` be a category cofibered in
groupoids, and let `φ` be a morphism in `F` from `x'` to `x` lying over `f : A' ⟶ A`.
The group `Inf(x'/x)` of infinitesimal automorphisms of `x'` over `x` is
`Ker(Aut (x') → Aut (x))`, formed in the fibres of `p` over `A'` and `A`. -/
@[stacks 06JP]
noncomputable abbrev infinitesimalAut (p : F ⥤ ArtinianLocalAlgCat Λ k)
    [Functor.IsFibered.InGroupoids p.op] {A' A : ArtinianLocalAlgCat Λ k} (f : A' ⟶ A)
    {x' : p.Fiber A'} {x : p.Fiber A}
    (φ : fiberInclusion.obj x' ⟶ fiberInclusion.obj x) [p.IsHomLift f φ] :
    Subgroup (Aut x') :=
  Functor.infinitesimalAut p f φ

/-- Membership in `infinitesimalAut` is the equalizer condition that a fibre automorphism
of `x'` becomes the identity after composing with `φ`. -/
theorem mem_infinitesimalAut (p : F ⥤ ArtinianLocalAlgCat Λ k)
    [Functor.IsFibered.InGroupoids p.op] {A' A : ArtinianLocalAlgCat Λ k} (f : A' ⟶ A)
    {x' : p.Fiber A'} {x : p.Fiber A}
    (φ : fiberInclusion.obj x' ⟶ fiberInclusion.obj x) [p.IsHomLift f φ]
    (α : Aut x') :
    α ∈ infinitesimalAut p f φ ↔ fiberInclusion.map α.hom ≫ φ = φ := sorry
