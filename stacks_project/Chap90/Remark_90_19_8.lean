module

public import stacks_project.Chap90.Definition_90_19_2
import StacksCheckRecall

/-!
# Infinitesimal automorphisms as identity lifts and Aut tangent spaces

In a category cofibered in groupoids over `ArtinianLocalAlgCat Λ k`, the group
`infinitesimalAut p f φ` equals the group of lifts of `id_x` as an object of
`Aut x'`, realized as `(fiberAutHom p f φ).ker`. Specializing to the unique
retraction of a dual-number pushforward identifies `Inf_{x0}(F)` with
`T_id Aut(x0)`.
-/

@[expose] public section

open CategoryTheory ArtinianLocalAlgCat

universe u v w

variable {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]
variable {F : Type v} [Category.{w} F]

namespace CategoryTheory.Functor

open Fiber

section
variable (p : F ⥤ ArtinianLocalAlgCat Λ k) [IsFibered.InGroupoids p.op]
variable {A' A : ArtinianLocalAlgCat Λ k} (f : A' ⟶ A)
variable {x' : p.Fiber A'} {x : p.Fiber A}
variable (φ : fiberInclusion.obj x' ⟶ fiberInclusion.obj x)
variable [p.IsHomLift f φ] [p.IsCocartesian f φ]

/- Remark 90.19.8 (1): Inf(x'/x) equals Lift(id_x, A') as an Aut(x')-object,
realized as the kernel of `fiberAutHom`. -/
@[stacks 06JW] #check (infinitesimalAut_eq_ker p f φ :
    infinitesimalAut p f φ = (fiberAutHom p f φ).ker)
end

/-- The tangent space of `Aut x0` at the identity, as the kernel of fibre-automorphism
restriction along the unique retraction of a dual-number pushforward. This is the
source group `T_id Aut(x0)`, equally the group of lifts of `id_{x0}` as an object of
`Aut x0'`. -/
noncomputable abbrev idAutTangentSpace
    (p : F ⥤ ArtinianLocalAlgCat Λ k) [IsFibered.InGroupoids p.op]
    (x0 : p.Fiber (residue Λ k)) (x0' : p.Fiber (dualNumber Λ k))
    (φ : fiberInclusion.obj x0 ⟶ fiberInclusion.obj x0')
    [p.IsStronglyCocartesian (residueToDualNumber Λ k) φ] :
    Subgroup (Aut x0') :=
  (fiberAutHom p (dualNumberToResidue Λ k) (retraction p φ)).ker

/-- Membership in `idAutTangentSpace` is the kernel condition for `fiberAutHom`
along the unique retraction of the chosen dual-number pushforward. -/
theorem mem_idAutTangentSpace
    (p : F ⥤ ArtinianLocalAlgCat Λ k) [IsFibered.InGroupoids p.op]
    (x0 : p.Fiber (residue Λ k)) (x0' : p.Fiber (dualNumber Λ k))
    (φ : fiberInclusion.obj x0 ⟶ fiberInclusion.obj x0')
    [p.IsStronglyCocartesian (residueToDualNumber Λ k) φ] (α : Aut x0') :
    α ∈ idAutTangentSpace p x0 x0' φ ↔
      fiberAutHom p (dualNumberToResidue Λ k) (retraction p φ) α = 1 := sorry

/-- Remark 90.19.8 (2): Inf_{x0}(F) = Lift(id_{x0}, k[ε]) = T_id Aut(x0),
where Lift(id_{x0}, k[ε]) is the kernel of `fiberAutHom` along the unique
retraction of the chosen dual-number pushforward, not an object-lift of F. -/
@[stacks 06JW]
theorem infinitesimalAutomorphismsAt_eq_idAutTangentSpace
    (p : F ⥤ ArtinianLocalAlgCat Λ k) [IsFibered.InGroupoids p.op]
    (x0 : p.Fiber (residue Λ k)) (x0' : p.Fiber (dualNumber Λ k))
    (φ : fiberInclusion.obj x0 ⟶ fiberInclusion.obj x0')
    [p.IsStronglyCocartesian (residueToDualNumber Λ k) φ] :
    infinitesimalAutomorphismsAt p x0 x0' φ = idAutTangentSpace p x0 x0' φ := sorry

end CategoryTheory.Functor
