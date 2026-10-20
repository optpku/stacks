module

public import ReasLib.AlgebraicGeometry.FormalDeformation.Groupoid.Deformation
import StacksCheckRecall

/-!
# Deformation invariants of a smooth groupoid quotient

A smooth groupoid whose object and arrow functors are deformation functors has a
deformation-category quotient, tangent space the cokernel of `ds - dt`, and
infinitesimal automorphism space the kernel of `ds ⊕ dt`.
-/

@[expose] public section

open CategoryTheory ArtinianLocalAlgCat

universe u w

variable {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]

/- Lemma 90.24.2: a smooth groupoid of deformation functors has a deformation-category
quotient, tangent space `Coker(ds - dt)`, and infinitesimal automorphism space
`Ker(ds ⊕ dt)`. -/
@[stacks 06KU] #check (CategoryTheory.GroupoidInFunctors.instIsDeformationCategory_quotient :
  ∀ (G : GroupoidInFunctors.{u + 1, u, w} (ArtinianLocalAlgCat Λ k))
    [GroupoidInFunctors.IsSmooth G.s G.t]
    [Functor.IsDeformationCategory (CategoryOfElements.π G.U)]
    [Functor.IsDeformationCategory (CategoryOfElements.π G.R)],
    Functor.IsDeformationCategory G.quotient.p)

#check (CategoryTheory.GroupoidInFunctors.tangentSpace_quotient :
  ∀ (G : GroupoidInFunctors.{u + 1, u, w} (ArtinianLocalAlgCat Λ k))
    [GroupoidInFunctors.IsSmooth G.s G.t]
    [Functor.IsDeformationCategory (CategoryOfElements.π G.U)]
    [Functor.IsDeformationCategory (CategoryOfElements.π G.R)],
    (G.U.obj (dualNumber Λ k) ⧸ LinearMap.range
      (GroupoidInFunctors.tangentSource G - GroupoidInFunctors.tangentTarget G)) ≃ₗ[k]
        Functor.tangentSpace G.quotient.p)

#check (CategoryTheory.GroupoidInFunctors.infinitesimalAutomorphisms_quotient :
  ∀ (G : GroupoidInFunctors.{u + 1, u, w} (ArtinianLocalAlgCat Λ k))
    [GroupoidInFunctors.IsSmooth G.s G.t]
    [Functor.IsDeformationCategory (CategoryOfElements.π G.U)]
    [Functor.IsDeformationCategory (CategoryOfElements.π G.R)]
    (residuePoint : G.U.obj (residue Λ k)),
    GroupoidInFunctors.infAutQuotient G residuePoint ≃ₗ[k]
      LinearMap.ker ((GroupoidInFunctors.tangentSource G).prod
        (GroupoidInFunctors.tangentTarget G)))
