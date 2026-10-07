module

public import stacks_project.Chap93.Example_93_6_1_Representations_of_a_topological_group_Category
public import stacks_project.Chap93.Example_93_6_1_Representations_of_a_topological_group_Deformation
import StacksCheckRecall

/-!
# Representations of a topological group

Source-facing labeled entries for the category `F` of discrete-continuous
finite projective representations over `ArtinianLocalAlgCat`, the cofibered
projection `p`, and the deformation category `Def_{V, ρ0} = F_{x0}`.
-/

@[expose] public section

open CategoryTheory
open ContinuousRep

universe u

variable (Γ Λ k : Type u) [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
  [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k] [Module.Finite Λ k]

/- Example 93.6.1 (Representations of a topological group) (1)
Let Γ be a topological group. The category F is ContinuousRep Γ Λ k: an object
is a triple (A, M, ρ) consisting of an object A of ArtinianLocalAlgCat Λ k, a
finite projective A-module M, and a continuous homomorphism
ρ : Γ →* LinearMap.GeneralLinearGroup A.carrier M, where GL is given the
discrete topology. A morphism (f, g) : (B, N, τ) ⟶ (A, M, ρ) consists of a
morphism f : B ⟶ A in ArtinianLocalAlgCat Λ k together with an f-linear
Γ-equivariant map g : N → M inducing N ⊗[B, f] A ≅ M. The functor
p = ContinuousRep.forget sends (A, M, ρ) to A and (f, g) to f. -/
@[stacks 0D3K]
#check ContinuousRep

/- Example 93.6.1 (Representations of a topological group) (2)
The functor p : ContinuousRep Γ Λ k ⥤ ArtinianLocalAlgCat Λ k is cofibered in
groupoids. -/
@[stacks 0D3K]
#check (instIsCofiberedInGroupoids Γ Λ k :
  Functor.IsFibered.InGroupoids (forget Γ Λ k).op)

/- Example 93.6.1 (Representations of a topological group) (3)
Given a finite-dimensional k-vector space V and a continuous representation
ρ0 : Γ →* LinearMap.GeneralLinearGroup k V, the object x0 = (k, V, ρ0) is
ofResidue V ρ0, and Def_{V, ρ0} is deformationCategory V ρ0 = F_{x0}. -/
@[stacks 0D3K]
#check deformationCategory
