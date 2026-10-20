module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Simplicial.RingedComparison
import StacksCheckRecall

/-!
# Lemma 85.34.1

For a scheme `S`, an algebraic space `X` over `S`, a simplicial algebraic space
`U` over `S`, and an augmentation `a : U ⟶ X`, the unringed fppf–étale comparison
square of Lemma 85.33.1 upgrades to a commutative square of ringed topoi
`(Sh((Spaces/U)_{fppf,total}), 𝒪_big,total) ⟶ (Sh(U_étale), 𝒪_U)` over
`(Sh((Spaces/X)_fppf), 𝒪_big) ⟶ (Sh(X_étale), 𝒪_X)`. The left vertical arrow
is the Section 85.22/85.21 slice-augmentation; the right vertical arrow is the
Section 85.32 étale augmentation.
-/

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace.Simplicial
open CategoryTheory.SimplicialObject

/- Lemma 85.34.1
Let S be a scheme. Let X be an algebraic space over S. Let U be a simplicial
algebraic space over S. Let a : U ⟶ X be an augmentation. There is a commutative
diagram of ringed topoi with edges h, a_fppf, a and h₋₁. -/
@[stacks 0DHC] #check
  (AlgebraicGeometry.AlgebraicSpace.Simplicial.fppfEtaleRingedCommSq :
    ∀ {S : Scheme.{u}} (U : SimplicialObject (AlgebraicSpace S))
      {X : AlgebraicSpace S} (a : U ⟶ (Functor.const SimplexCategoryᵒᵖ).obj X),
      RingedSite.ToposHom.CommSquare (fppfTotalRingedSite U) (etaleTotalRingedSite U)
        (AlgebraicSpace.Fppf.overFppfRingedSite X) (AlgebraicSpace.spacesRingedSite X))
