module

public import ReasLib.AlgebraicGeometry.GeneralLinear.Two
public import ReasLib.AlgebraicGeometry.ProjectiveSpace.Line.Immersion
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry

universe u

variable (k : Type u) [Field k]

/- Example 26.21.17 (1): `GL₂,k` and its first-row morphism to the punctured affine plane are
explicit objects indexed by matrix positions. -/
@[stacks 01KX] #check GLTwo.coordinateRing k
@[stacks 01KX] #check GLTwo.det_eq_ad_sub_bc k
@[stacks 01KX] #check GLTwo.localizedDeterminant_eq_ad_sub_bc k
@[stacks 01KX] #check GLTwo.localizedDeterminant_isUnit k
@[stacks 01KX] #check GLTwo.scheme k
#synth IsAffine (GLTwo.scheme k)
@[stacks 01KX] #check GLTwo.toAffinePlaneComap k
@[stacks 01KX] #check GLTwo.toAffinePlaneComap_x k
@[stacks 01KX] #check GLTwo.toAffinePlaneComap_y k
@[stacks 01KX] #check GLTwo.toAffinePlane k
@[stacks 01KX] #check GLTwo.toPuncturedAffinePlane k
@[stacks 01KX] #check GLTwo.toPuncturedAffinePlane_ι k
@[stacks 01KX "punctured-plane affine/polynomial-spectrum comparison"]
#check PuncturedAffineSpace.coordinateModelIso (ULift.{u} (Fin 2)) k
@[stacks 01KX "punctured-plane comparison"]
#check PuncturedAffineSpace.coordinateModelIso.preimage_puncturedOpen
  (ULift.{u} (Fin 2)) k
@[stacks 01KX "first-row map to the punctured affine plane is surjective"]
#check (inferInstance : Surjective (GLTwo.toPuncturedAffinePlane k))
#check PuncturedAffineSpace.existsUnique_projectivization k 1
@[stacks 01KX] #check PuncturedAffineSpace.toProjectiveSpace k 1

/- Example 26.21.17 (2): the image is not contained in any affine open of the punctured affine
plane. -/
@[stacks 01KX] #check
  Surjective.not_range_subset_affineOpen
    (f := GLTwo.toPuncturedAffinePlane k) (PuncturedAffinePlane.not_isAffine k)

/- Example 26.21.17 (3): projectivizing the first row gives a canonical surjection from `GL₂,k`
onto the projective line. -/
@[stacks 01KX] #check GLTwo.toProjectiveLine k
@[stacks 01KX] #check GLTwo.toProjectiveLine_toBase k
@[stacks 01KX "first-row map to the projective line is surjective"]
#check (inferInstance : Surjective (GLTwo.toProjectiveLine k))

/- Example 26.21.17 (4): the projective line has no immersion into an affine scheme. -/
@[stacks 01KX] #check ProjectiveLine.no_immersion_to_affine k
