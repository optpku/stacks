/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.ProjectiveSpace.Coordinate
public import ReasLib.AlgebraicGeometry.PuncturedAffineSpace.CoordinateCover
public import Mathlib.AlgebraicGeometry.Gluing
import Mathlib.Tactic.CrossRefAttribute

/-!
# Projectivization of punctured affine space

This file owns the canonical projectivization map obtained by gluing the compatible ratio-coordinate
charts on the standard coordinate cover, together with a predicate recognizing that map from its
restrictions to that cover.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.PuncturedAffineSpace

variable (k : Type u) [CommRing k] (n : ℕ)

/-- The universe-lifted coordinate index used by the relative affine-space model. -/
@[stacks 01KX "projectivization coordinate index"]
abbrev projectiveIndex (n : ℕ) : Type u := ULift.{u} (Fin (n + 1))

namespace Projectivization

/-- The homogeneous coordinate-ring map to global sections on punctured affine
`(n + 1)`-space. -/
@[stacks 01KX "homogeneous coordinates on punctured affine space"]
noncomputable abbrev coordinateMap :
    CommRingCat.of (coordinateRing (Fin (n + 1)) k) ⟶
      Scheme.Γ.obj (op (puncturedOpen (projectiveIndex n) k).toScheme) :=
  CommRingCat.ofHom
      ((MvPolynomial.renameEquiv k
        (Equiv.ulift : projectiveIndex n ≃ Fin (n + 1))).symm.toRingEquiv.toRingHom) ≫
    globalSectionsComparison (projectiveIndex n) k

/-- The coordinate map sends a projective variable to the corresponding lifted punctured
coordinate section. -/
@[simp, stacks 01KX "projectivization coordinate map on variables"]
theorem coordinateMap_coordinate (i : Fin (n + 1)) :
    (coordinateMap k n).hom (MvPolynomial.X i) =
      coordinateOnPuncture (projectiveIndex n) k (ULift.up i) := sorry

/-- On the `i`-th coordinate open, projectivization is the ratio-coordinate map into
`D₊(X_i)`. -/
@[stacks 01KX "projectivization coordinate chart"]
noncomputable def chartMap (i : Fin (n + 1)) :
    (coordinateOpen (projectiveIndex n) k (ULift.up i)).toScheme ⟶
      ProjectiveSpace.scheme k n :=
  Proj.toBasicOpenOfGlobalSections (ProjectiveSpace.grading k n)
      (coordinateMap k n).hom
      (coordinateMap_coordinate k n i)
      (Nat.succ_pos 0)
      (MvPolynomial.isHomogeneous_X k i) ≫
    (ProjectiveSpace.basicOpen (R := k) n (MvPolynomial.X i)).ι

/-- The ratio-coordinate maps agree on pairwise intersections of coordinate opens. -/
@[stacks 01KX "compatibility of projectivization charts"]
theorem chartMap_compatible (i j : Fin (n + 1)) :
    pullback.fst ((coordinateOpenCover (projectiveIndex n) k).f (ULift.up i))
        ((coordinateOpenCover (projectiveIndex n) k).f (ULift.up j)) ≫
        chartMap k n i =
      pullback.snd ((coordinateOpenCover (projectiveIndex n) k).f (ULift.up i))
          ((coordinateOpenCover (projectiveIndex n) k).f (ULift.up j)) ≫
        chartMap k n j := sorry

end Projectivization

/-- The canonical projectivization morphism from punctured affine `(n + 1)`-space to projective
`n`-space, obtained by gluing the compatible ratio-coordinate maps. -/
@[stacks 01KX "projectivization of punctured affine space"]
noncomputable def toProjectiveSpace :
    (puncturedOpen (projectiveIndex n) k).toScheme ⟶ ProjectiveSpace.scheme k n :=
  (coordinateOpenCover (projectiveIndex n) k).glueMorphisms
    (fun i => Projectivization.chartMap k n i.down)
    (fun i j => Projectivization.chartMap_compatible k n i.down j.down)

/-- A morphism from punctured affine `(n + 1)`-space is the standard projectivization when its
restriction to every coordinate open is the corresponding ratio-coordinate map. -/
@[stacks 01KX "projectivization of punctured affine space"]
def IsProjectivization
    {k : Type u} [CommRing k] {n : ℕ}
    (q : (puncturedOpen (projectiveIndex n) k).toScheme ⟶ ProjectiveSpace.scheme k n) : Prop :=
  ∀ i : Fin (n + 1),
    (coordinateOpenCover (projectiveIndex n) k).f (ULift.up i) ≫ q =
      Projectivization.chartMap k n i

/-- The canonical projectivization has the standard ratio-coordinate restrictions. -/
@[stacks 01KX "canonical projectivization chart specification"]
theorem IsProjectivization.canonical :
    IsProjectivization (toProjectiveSpace k n) := sorry

/-- A projectivization restricts on each coordinate open to the corresponding ratio-coordinate
map. -/
@[stacks 01KX "projectivization chart readout"]
abbrev IsProjectivization.chartMap
    {q : (puncturedOpen (projectiveIndex n) k).toScheme ⟶ ProjectiveSpace.scheme k n}
    (hq : IsProjectivization q) (i : Fin (n + 1)) :
    (coordinateOpenCover (projectiveIndex n) k).f (ULift.up i) ≫ q =
      Projectivization.chartMap k n i :=
  hq i

/-- Two standard projectivizations of punctured affine space are equal. -/
@[stacks 01KX "uniqueness of projectivization"]
theorem IsProjectivization.eq
    {q q' : (puncturedOpen (projectiveIndex n) k).toScheme ⟶ ProjectiveSpace.scheme k n}
    (hq : IsProjectivization q) (hq' : IsProjectivization q') :
    q = q' := sorry

/-- The coordinate ratio maps glue to a unique projectivization of punctured affine space. -/
@[stacks 01KX "unique projectivization of punctured affine space"]
theorem existsUnique_projectivization :
    ∃! q : (puncturedOpen (projectiveIndex n) k).toScheme ⟶ ProjectiveSpace.scheme k n,
      IsProjectivization q := sorry

/-- Under a projectivization, the inverse image of a standard projective basic open is the basic
open of the corresponding coordinate on punctured affine space. -/
@[simp, stacks 01KX "projectivization coordinate-open preimage"]
theorem IsProjectivization.preimage_basicOpen
    {q : (puncturedOpen (projectiveIndex n) k).toScheme ⟶ ProjectiveSpace.scheme k n}
    (hq : IsProjectivization q) (i : Fin (n + 1)) :
      q ⁻¹ᵁ Proj.basicOpen (ProjectiveSpace.grading k n) (MvPolynomial.X i) =
      (puncturedOpen (projectiveIndex n) k).toScheme.basicOpen
        (coordinateOnPuncture (projectiveIndex n) k (ULift.up i)) := sorry

/-- Every projectivization commutes with the structure morphisms to `Spec(k)`. -/
@[reassoc, stacks 01KX "projectivization structure map"]
theorem IsProjectivization.toBase
    {q : (puncturedOpen (projectiveIndex n) k).toScheme ⟶ ProjectiveSpace.scheme k n}
    (hq : IsProjectivization q) :
    q ≫ ProjectiveSpace.toSpec k n =
      (puncturedOpen (projectiveIndex n) k).ι ≫ toBase (projectiveIndex n) k := sorry

/-- Every projectivization of punctured affine space is surjective. -/
@[stacks 01KX "projectivization is surjective"]
theorem IsProjectivization.surjective
    {q : (puncturedOpen (projectiveIndex n) k).toScheme ⟶ ProjectiveSpace.scheme k n}
    (hq : IsProjectivization q) : Surjective q := sorry

/-- The canonical projectivization restricts to the ratio-coordinate map on every coordinate
open. -/
@[reassoc (attr := simp), stacks 01KX "canonical projectivization charts"]
theorem toProjectiveSpace_chartMap (i : Fin (n + 1)) :
    (coordinateOpenCover (projectiveIndex n) k).f (ULift.up i) ≫ toProjectiveSpace k n =
      Projectivization.chartMap k n i := sorry

/-- The inverse image of a standard projective basic open under the canonical projectivization is
the corresponding coordinate open in punctured affine space. -/
@[simp, stacks 01KX "canonical projectivization coordinate-open preimage"]
theorem toProjectiveSpace_preimage_basicOpen (i : Fin (n + 1)) :
    toProjectiveSpace k n ⁻¹ᵁ
        Proj.basicOpen (ProjectiveSpace.grading k n) (MvPolynomial.X i) =
      (puncturedOpen (projectiveIndex n) k).toScheme.basicOpen
        (coordinateOnPuncture (projectiveIndex n) k (ULift.up i)) := sorry

/-- The canonical projectivization commutes with the structure morphisms to `Spec(k)`. -/
@[reassoc, stacks 01KX "canonical projectivization structure map"]
theorem toProjectiveSpace_toBase :
    toProjectiveSpace k n ≫ ProjectiveSpace.toSpec k n =
      (puncturedOpen (projectiveIndex n) k).ι ≫ toBase (projectiveIndex n) k := sorry

/-- The canonical projectivization of punctured affine space is surjective. -/
@[stacks 01KX, instance]
theorem toProjectiveSpace_surjective : Surjective (toProjectiveSpace k n) := sorry

end AlgebraicGeometry.PuncturedAffineSpace
