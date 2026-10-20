module

public import ReasLib.AlgebraicTopology.SimplicialObject.Augmented.AlternatingFace
public import ReasLib.AlgebraicTopology.SimplicialObject.DoldKan.UnderlyingHomotopyEquivalence.ModuleCat

/-!
# Alternating-face augmentations of simplicial modules

This is the thin module-valued specialization of the generic augmented alternating-face API.
-/

@[expose] public section

open CategoryTheory HomologicalComplex
open AlgebraicTopology

universe u v x y

namespace AlgebraicTopology.AlternatingFaceMapComplex.ModuleCat

/-- An augmented simplicial module whose underlying augmentation is a simplicial-set homotopy
equivalence has a quasi-isomorphic alternating-face augmentation. -/
@[stacks 08P2 "underlying contraction gives an augmented module quasi-isomorphism"]
theorem quasiIso_ε_of_underlying (R : Type u) [Ring R]
    (X : SimplicialObject.Augmented (ModuleCat.{v} R))
    (hX : SimplicialObject.ModuleCat.underlying.homotopyEquivalences R X.hom) :
    QuasiIso (ε.app X) := sorry

/-- A functorial family of augmented simplicial modules whose underlying augmentations are
simplicial-set homotopy equivalences has a pointwise quasi-isomorphic canonical augmentation
natural transformation. -/
@[stacks 08P2 "functorial underlying-homotopy criterion for augmented modules"]
theorem quasiIso_ε_functorCategory_of_underlying
    (R : Type u) [Ring R] {C : Type x} [Category.{y} C]
    (X : C ⥤ SimplicialObject.Augmented (ModuleCat.{v} R))
    (hX : ∀ c, SimplicialObject.ModuleCat.underlying.homotopyEquivalences R
      (X.obj c).hom) :
    (HomologicalComplex.quasiIso (ModuleCat.{v} R)
      (ComplexShape.down ℕ)).functorCategory C
      (Functor.whiskerLeft X ε) := sorry

end AlgebraicTopology.AlternatingFaceMapComplex.ModuleCat
