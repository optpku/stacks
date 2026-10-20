module

public import ReasLib.AlgebraicGeometry.FormalDeformation.GroupRepresentation.Tangent
public import ReasLib.RepresentationTheory.Homological.GroupCohomology.Ext
public import ReasLib.RepresentationTheory.Homological.GroupCohomology.FiniteDimensional
import StacksCheckRecall

/-! # Tangent space and infinitesimal automorphisms of a group representation -/

@[expose] public section

open CategoryTheory Functor

universe u

variable (Γ Λ k : Type u) [Group Γ] [CommRing Λ] [IsNoetherianRing Λ] [Field k]
  [Algebra Λ k] [Module.Finite Λ k]
variable {V : Type u} [AddCommGroup V] [Module k V] [Module.Finite k V]
variable (ρ0 : Γ →* LinearMap.GeneralLinearGroup k V)

/- Lemma 93.5.3
For a finite-dimensional representation, the tangent space is linearly equivalent to
self-Ext and first cohomology with endomorphism coefficients. Infinitesimal automorphisms
are linearly equivalent to degree-zero cohomology and form a finite-dimensional space.
The tangent space is finite-dimensional when the group is finitely generated. The tangent
comparison sends every extension-induced deformation to its canonical extension class. -/
@[stacks 0DVT] #check (GroupRepCat.exists_tangentSpace_ext_equiv Γ Λ k ρ0 :
  ∃ e : GroupRepCat.tangentSpace Γ Λ k ρ0 ≃ₗ[k] Abelian.Ext.{u + 1}
      (Rep.of (GroupRepCat.residueRepresentation Γ Λ k ρ0)) (Rep.of (GroupRepCat.residueRepresentation Γ Λ k ρ0)) 1,
    ∀ (E : Rep.{u} k Γ) (f : Rep.of (GroupRepCat.residueRepresentation Γ Λ k ρ0) ⟶ E)
      (g : E ⟶ Rep.of (GroupRepCat.residueRepresentation Γ Λ k ρ0)) (w : f ≫ g = 0)
      (h : (ShortComplex.mk f g w).ShortExact),
      e (GroupRepCat.ofExtension Γ Λ k ρ0 E f g w h) = h.extClass)

#check (GroupRepCat.infAutOfInvariants_bijective Γ Λ k ρ0 :
  Function.Bijective (GroupRepCat.infAutOfInvariants Γ Λ k ρ0))

#check (groupCohomology.nonempty_extIsoH1
    (Rep.of (GroupRepCat.residueRepresentation Γ Λ k ρ0)) (Rep.of (GroupRepCat.residueRepresentation Γ Λ k ρ0)) :
  Nonempty ((Abelian.Ext.{u + 1} (Rep.of (GroupRepCat.residueRepresentation Γ Λ k ρ0))
    (Rep.of (GroupRepCat.residueRepresentation Γ Λ k ρ0)) 1) ≃ₗ[k]
    groupCohomology.H1 (Rep.of (GroupRepCat.endRepresentation Γ Λ k ρ0))))

#check (GroupRepCat.h0EquivInfinitesimal Γ Λ k ρ0 :
  groupCohomology.H0 (Rep.of (GroupRepCat.endRepresentation Γ Λ k ρ0)) ≃ₗ[k]
    GroupRepCat.infinitesimalSpace Γ Λ k ρ0)

#check (GroupRepCat.instFiniteDimensionalInfinitesimalSpace Γ Λ k ρ0 :
  FiniteDimensional k (GroupRepCat.infinitesimalSpace Γ Λ k ρ0))

variable [Group.FG Γ]

#check (GroupRepCat.instFiniteDimensionalTangentSpace Γ Λ k ρ0 :
  FiniteDimensional k (GroupRepCat.tangentSpace Γ Λ k ρ0))
