module

public import ReasLib.AlgebraicGeometry.FormalDeformation.FiniteProjective.RimSchlessinger
import StacksCheckRecall

/-!
# Rim-Schlessinger condition for finite projective modules

Example 93.4.1 satisfies (RS), so each residue-fibre slice `Def_V` is a deformation
category.
-/

@[expose] public section

open CategoryTheory Functor

universe u

/- Lemma 93.4.2 (1): the category `F` of finite projective modules from Example 93.4.1
satisfies the Rim-Schlessinger condition (RS). -/
@[stacks 0DVP] #check (ArtinianLocalAlgCat.FiniteProjective.instHasRimSchlessinger :
  ∀ {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
    [Module.Finite Λ k],
    HasRimSchlessinger (ArtinianLocalAlgCat.FiniteProjective.groupoids Λ k).p)

/- Lemma 93.4.2 (2): in particular, `Def_V` is a deformation category for any
finite-dimensional vector space `V` over `k`. -/
@[stacks 0DVP] #check (ArtinianLocalAlgCat.FiniteProjective.instIsDeformationCategory_deformation :
  ∀ {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
    [Module.Finite Λ k]
    (V : Type u) [AddCommGroup V] [Module k V] [FiniteDimensional k V],
    IsDeformationCategory
      (ArtinianLocalAlgCat.FiniteProjective.deformation V :
          CofiberedCategoryOver.Groupoids.{u + 1, u, u + 1, u}
            (ArtinianLocalAlgCat Λ k)).p)
