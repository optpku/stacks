module

public import Mathlib.Algebra.Group.Subgroup.Basic
public import Mathlib.Algebra.Module.Basic
public import stacks_project.Chap90.Definition_90_19_2_DualNumber
public import stacks_project.Chap90.Lemma_90_10_7_Pullback
public import stacks_project.Chap90.Lemma_90_12_2_SquareZero
public import stacks_project.Chap90.Lemma_90_19_6

public import ReasLib.AlgebraicGeometry.FormalDeformation.InfinitesimalAutomorphisms.TangentSpace

/-!
# Identity-tangent spaces of automorphism functors

Typed compatibility checks for the identity-restriction subgroup and its
canonical vector-space operations.
-/

@[expose] public section

open CategoryTheory hiding Linear
open CategoryTheory.Functor
open ArtinianLocalAlgCat

universe u v w

variable {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]
variable {F : Type v} [Category.{w} F]

#check (CategoryTheory.Functor.idTangentSpace :
  ∀ (p : F ⥤ ArtinianLocalAlgCat Λ k) [Functor.IsFibered.InGroupoids p.op] (x : F),
    Subgroup (Aut (idTangentSpaceObj p x)))

#check (CategoryTheory.Functor.idTangentSpaceAdd_spec :
  ∀ (p : F ⥤ ArtinianLocalAlgCat Λ k) [HasRimSchlessinger p] {x : F}
    (α β : idTangentSpace p x),
    (idTangentSpaceAdd p α β).val =
      (autFunctor p x).map (dualNumberSumUnder (p.obj x))
        ((idTangentSpaceAddEquiv p x).symm (idTangentSpaceAddPair p α β)))

#check (CategoryTheory.Functor.idTangentSpaceSMul_spec :
  ∀ (p : F ⥤ ArtinianLocalAlgCat Λ k) [Functor.IsFibered.InGroupoids p.op] {x : F}
    (r : k) (α : idTangentSpace p x),
    (idTangentSpaceSMul p r α).val =
      (autFunctor p x).map (dualNumberSMulUnder (p.obj x) r) α.val)

#check (CategoryTheory.Functor.idTangentSpace_add_eq_mul :
  ∀ (p : F ⥤ ArtinianLocalAlgCat Λ k) [HasRimSchlessinger p] {x : F}
    (α β : idTangentSpace p x), α + β = α * β)

#check (CategoryTheory.Functor.idTangentSpace_mul_comm :
  ∀ (p : F ⥤ ArtinianLocalAlgCat Λ k) [HasRimSchlessinger p] {x : F}
    (α β : idTangentSpace p x), α * β = β * α)
