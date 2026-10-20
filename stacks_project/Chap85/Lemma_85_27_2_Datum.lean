module

public import ReasLib.AlgebraicTopology.SimplicialObject.Descent

open CategoryTheory CategoryTheory.Limits
open CategoryTheory.SimplicialObject
open scoped Simplicial

universe v u

variable {C : Type u} [Category.{v} C] [HasPullbacks C] (X : SimplicialObject C)

/- A degree-zero object and a face isomorphism with degeneracy and cocycle laws
construct explicit simplicial descent data. -/
#check (CartesianDatum.ofPullbackIso :
  ∀ (V : Over (X _⦋0⦌))
    (e : (Over.pullback (X.δ (1 : Fin 2))).obj V ≅
      (Over.pullback (X.δ (0 : Fin 2))).obj V),
    degeneracyPullback X e = 𝟙 V →
      cocycleLeft X e = cocycleRight X e → CartesianDatum X)

/- Descent data reconstruct to cartesian simplicial objects over the base. -/
#check (CartesianDatum.ofDatum : CartesianDatum X ⥤ CartesianOver X)

/- Cartesian simplicial objects yield their canonical degree-zero descent data. -/
#check (CartesianDatum.toDatum : CartesianOver X ⥤ CartesianDatum X)
