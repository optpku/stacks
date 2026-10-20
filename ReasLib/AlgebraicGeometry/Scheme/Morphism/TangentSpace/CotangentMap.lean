/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Fiber.StalkMap
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.ResidueField
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.TangentSpace.Cotangent
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.TangentSpace.Map

/-!
# Maps on fibre cotangent spaces

This leaf owns the cotangent map induced by a triangle of scheme morphisms
and its compatibility with the relative tangent map.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Hom

/-- The fibre-cotangent map induced by the local-ring morphism of a triangle,
with the target scalar action restricted along the residue-field map. -/
noncomputable def relativeFiberCotangentMapAt {X Y S : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ S) (x : X)
    (hκ : Function.Bijective (f.residueFieldMap x).hom) :
    let eκ := RingEquiv.ofBijective (f.residueFieldMap x).hom hκ
    let _ : Module (Y.residueField (f x))
        (IsLocalRing.CotangentSpace (fiberStalkAt (f ≫ g) x)) :=
      Module.compHom _ eκ.toRingHom
    IsLocalRing.CotangentSpace (fiberStalkAt g (f x)) →ₗ[Y.residueField (f x)]
      IsLocalRing.CotangentSpace (fiberStalkAt (f ≫ g) x) :=
  let eκ := RingEquiv.ofBijective (f.residueFieldMap x).hom hκ
  -- Local declaration justification (defeq pin): restrict the target cotangent
  -- action along the explicit residue-field equivalence selected by `hκ`.
  let _ : Module (Y.residueField (f x))
      (IsLocalRing.CotangentSpace (fiberStalkAt (f ≫ g) x)) :=
    Module.compHom _ eκ.toRingHom
  let A := fiberStalkAt g (f x)
  let B := fiberStalkAt (f ≫ g) x
  let φ : A →+* B := (relativeFiberStalkMapAt f g x).hom
  -- Local declaration justification (defeq pin): use the algebra induced by
  -- the selected stalk morphism so `Ideal.mapCotangent` has its intended source.
  let _ : Algebra A B := φ.toAlgebra
  let h : IsLocalRing.maximalIdeal A ≤
      (IsLocalRing.maximalIdeal B).comap (Algebra.ofId A B) :=
    le_of_eq (IsLocalRing.maximalIdeal_comap φ).symm
  let ψ :=
    Ideal.mapCotangent (IsLocalRing.maximalIdeal A) (IsLocalRing.maximalIdeal B)
      (Algebra.ofId A B) h
  { toFun := ψ
    map_add' := ψ.map_add
    map_smul' := sorry }

/-- The fibre-cotangent map sends a maximal-ideal class to the class of its
image under the induced map of fibre stalks. -/
theorem relativeFiberCotangentMapAt_apply {X Y S : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ S) (x : X)
    (hκ : Function.Bijective (f.residueFieldMap x).hom)
    (a : IsLocalRing.maximalIdeal (fiberStalkAt g (f x))) :
    relativeFiberCotangentMapAt f g x hκ (Ideal.toCotangent _ a) =
      Ideal.toCotangent (IsLocalRing.maximalIdeal (fiberStalkAt (f ≫ g) x))
        ⟨(relativeFiberStalkMapAt f g x).hom a,
          (le_of_eq (IsLocalRing.maximalIdeal_comap
              (relativeFiberStalkMapAt f g x).hom).symm) a.2⟩ := sorry

/-- The relative tangent map is the dual of the fibre-cotangent map after
transporting the value field along the inverse residue-field equivalence. -/
theorem relativeTangentMapAt_cotangentLinearDual {X Y S : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ S) (x : X)
    (hκ : Function.Bijective (f.residueFieldMap x).hom)
    (hκs : Function.Bijective ((f ≫ g).residueFieldMap x).hom)
    (D : tangentSpaceAt (f ≫ g) x)
    (v : IsLocalRing.CotangentSpace (fiberStalkAt g (f x))) :
    relativeTangentSpaceToCotangentLinearDual g (f x)
        (residueFieldMap_bijective_of_triangle f g x hκ hκs)
        (relativeTangentMapAt f g x hκ D) v =
      (RingEquiv.ofBijective (f.residueFieldMap x).hom hκ).symm
        (relativeTangentSpaceToCotangentLinearDual (f ≫ g) x hκs D
          (relativeFiberCotangentMapAt f g x hκ v)) := sorry

end AlgebraicGeometry.Scheme.Hom
