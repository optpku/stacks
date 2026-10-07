module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Flat.Cover
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 29.25.2

This chapter entry recalls the neutral open-cover API for relative flatness of
quasi-coherent scheme modules.
-/

open scoped AlgebraicGeometry

universe u v w

namespace AlgebraicGeometry.Scheme.Modules

variable {X S : Scheme.{u}} (ℱ : X.Modules) [ℱ.IsQuasicoherent] (f : X ⟶ S)

/- Lemma 29.25.2: relative flatness of a quasi-coherent module is equivalent to its affine
section and open-cover criteria, and is preserved under restriction to compatible opens. -/
@[stacks 01U4] #check
  (flatOver_iff_affineOpenSectionsFlatOver ℱ f :
    flatOver ℱ f ↔ affineOpenSectionsFlatOver ℱ f)

#check
  (flatOver_iff_hasFlatOpenCover ℱ f :
    flatOver ℱ f ↔ Nonempty (FlatOpenCover.{u, v, w} ℱ f))

#check
  (flatOver_iff_hasFlatAffineOpenCover ℱ f :
    flatOver ℱ f ↔ Nonempty (FlatAffineOpenCover.{u, v, w} ℱ f))

variable (hflat : flatOver ℱ f) {U : X.Opens} {V : S.Opens} (e : U ≤ f ⁻¹ᵁ V)

#check
  (flatOver_resLE_of_flatOver ℱ hflat e :
    flatOver (ℱ.restrict U.ι) (f.resLE V U e))

end AlgebraicGeometry.Scheme.Modules
