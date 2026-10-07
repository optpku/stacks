module

public import stacks_project.Chap90.Remark_90_6_4
public import stacks_project.Chap93.Example_93_5_1_Representations_of_a_group_Category

/-!
# Deformation category of a group representation

The residue-fibre slice `Def_{V, ρ0} = F_{x0}` of `GroupRepCat` at a
finite-dimensional `k`-representation `(V, ρ0)`.
-/

@[expose] public section

open CategoryTheory
open Functor

universe u

namespace GroupRepCat

variable (Γ Λ k : Type u) [Group Γ] [CommRing Λ] [IsNoetherianRing Λ] [Field k]
  [Algebra Λ k] [Module.Finite Λ k]
variable {V : Type u} [AddCommGroup V] [Module k V] [Module.Finite k V]

/-- Example 93.5.1 (Representations of a group)
Let `Γ` be a group. The category `GroupRepCat Γ Λ k` has objects triples
`(A, M, ρ)` consisting of an object `A` of `ArtinianLocalAlgCat Λ k`, a finite
projective `A`-module `M`, and a homomorphism
`ρ : Γ →* LinearMap.GeneralLinearGroup A.carrier M`. A morphism `(f, g)` from
`(B, N, τ)` to `(A, M, ρ)` consists of a morphism `f : B ⟶ A` in
`ArtinianLocalAlgCat Λ k` together with a map `g : N → M` which is `f`-linear
and `Γ`-equivariant and induces an isomorphism `N ⊗[B, f] A ≃ M`. The functor
`GroupRepCat.forget` sends `(A, M, ρ)` to `A` and `(f, g)` to `f`, and is
cofibered in groupoids. Given a finite-dimensional `k`-vector space `V` and a
representation `ρ0 : Γ →* LinearMap.GeneralLinearGroup k V`, the object
`x0 = (k, V, ρ0)` is `ofResidue ρ0`, and `deformation ρ0` is the residue-fibre
slice `F_{x0} = Over (Fiber.fiberInclusion.obj (residueObj Γ Λ k ρ0))`. -/
@[stacks 0D3J]
abbrev deformation (ρ0 : Γ →* LinearMap.GeneralLinearGroup k V) :=
  Over (Fiber.fiberInclusion.obj (residueObj Γ Λ k ρ0))

/-- `deformation ρ0` is the Over-slice of the residue-fibre object `x0 = (k, V, ρ0)`. -/
theorem deformation_spec (ρ0 : Γ →* LinearMap.GeneralLinearGroup k V) :
    deformation Γ Λ k ρ0 = Over (Fiber.fiberInclusion.obj (residueObj Γ Λ k ρ0)) := sorry

end GroupRepCat
