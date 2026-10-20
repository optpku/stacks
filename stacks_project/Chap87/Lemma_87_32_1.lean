module

public import ReasLib.AlgebraicGeometry.FormalAlgebraicSpace.Fpqc
import StacksCheckRecall

/-!
# Formal algebraic spaces as fpqc sheaves

A formal algebraic space over a scheme `S` is defined as an fppf sheaf on
schemes over `S`. This lemma upgrades that to sheafness for the induced fpqc
topology on `Over S`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.FormalAlgebraicSpace

/- Lemma 87.32.1. Let `S` be a scheme and let `X` be a formal algebraic space
over `S`. Then `X` is a sheaf for `Scheme.fpqcTopology.over S` on the big site
of schemes over `S`. -/
@[stacks 0AQD] #check (AlgebraicGeometry.FormalAlgebraicSpace.isSheaf_fpqc :
    ∀ {S : Scheme.{u}} (X : (Over S)ᵒᵖ ⥤ Type u) [IsFormalAlgebraicSpace X],
      Presheaf.IsSheaf (Scheme.fpqcTopology.over S) X)

/- The functor of points of a formal algebraic space satisfies the singleton
sheaf condition for every faithfully flat morphism of affine schemes over `S`. -/
#check (AlgebraicGeometry.FormalAlgebraicSpace.isSheafFor_affineFaithfullyFlat :
    ∀ {S : Scheme.{u}} {X : (Over S)ᵒᵖ ⥤ Type u} [IsFormalAlgebraicSpace X]
      {T T' : Over S} (f : T' ⟶ T)
      [IsAffine T.left] [IsAffine T'.left] [Flat f.left] [Surjective f.left],
        Presieve.IsSheafFor X (Presieve.singleton f))

end AlgebraicGeometry.FormalAlgebraicSpace
