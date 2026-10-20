module

public import ReasLib.AlgebraicGeometry.GroupoidScheme.AffineNorm
import StacksCheckRecall

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.GroupoidScheme

/- Lemma 39.23.2: for an affine presentation of a groupoid scheme whose source and target
are finite locally free, the norm along the source of the target pullback of `f` is invariant. -/
@[stacks 03BH]
#check (AlgebraicGeometry.GroupoidScheme.norm_target_mem_eqLocus :
  ∀ {S : Scheme.{u}} (G : GroupoidScheme S)
    {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
    [Module.FiniteLocallyFree A B] (tSharp : A →+* B)
    (eU : Spec (CommRingCat.of A) ≅ G.U.left) (eR : Spec (CommRingCat.of B) ≅ G.R.left)
    (h_source : eR.hom ≫ G.s.left =
      Spec.map (CommRingCat.ofHom (algebraMap A B)) ≫ eU.hom)
    (h_target : eR.hom ≫ G.t.left = Spec.map (CommRingCat.ofHom tSharp) ≫ eU.hom)
    [IsFiniteLocallyFree G.s.left] [IsFiniteLocallyFree G.t.left] (f : A),
    LinearMap.projectiveDet (Algebra.lmul A B (tSharp f)) ∈
      tSharp.eqLocus (algebraMap A B))

end AlgebraicGeometry.GroupoidScheme
