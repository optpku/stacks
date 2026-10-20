module

public import Mathlib.Algebra.Ring.ULift
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtaleSite.IntegerModules
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.RingedSite.CommRing

/-!
# The integer scalar map to the structure sheaf

The canonical integer casts define a morphism from the constant integer sheaf
to the universe-lifted structure sheaf on the small étale site.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry CategoryTheory.Limits Opposite
open SheafOfModules.RingedSite

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

variable {S : Scheme.{u}}

/-- The constant integer presheaf maps to the universe-lifted structure sheaf by
the unique ring homomorphisms `ULift ℤ →+* 𝒪(V)`. -/
noncomputable def integerToStructurePresheaf (X : AlgebraicSpace S) :
    (Functor.const (smallEtaleSite X)ᵒᵖ).obj (CommRingCat.of (ULift.{u + 1} ℤ)) ⟶
      (commStructureSheafLift X).obj where
  app V :=
    CommRingCat.ofHom
      ((Int.castRingHom ((commStructureSheafLift X).obj.obj V)).comp
        (ULift.ringEquiv : ULift.{u + 1} ℤ ≃+* ℤ).toRingHom)
  naturality := sorry

/-- On each étale object, `integerToStructurePresheaf` is the composite of
`ULift.ringEquiv` with `Int.castRingHom`. -/
theorem integerToStructurePresheaf_app (X : AlgebraicSpace S)
    (V : (smallEtaleSite X)ᵒᵖ) :
    (integerToStructurePresheaf X).app V =
      CommRingCat.ofHom
        ((Int.castRingHom ((commStructureSheafLift X).obj.obj V)).comp
          (ULift.ringEquiv : ULift.{u + 1} ℤ ≃+* ℤ).toRingHom) :=
  sorry

/-- The canonical morphism of commutative ring sheaves `ℤ̲ ⟶ 𝒪_X` on the small
étale site, obtained by sheafifying `integerToStructurePresheaf`. -/
noncomputable def integerToStructureSheaf (X : AlgebraicSpace S) :
    constantIntegerRingSheaf X ⟶ commStructureSheafLift X :=
  ((sheafificationAdjunction (smallEtaleTopology X) CommRingCat.{u + 1}).homEquiv
      ((Functor.const (smallEtaleSite X)ᵒᵖ).obj (CommRingCat.of (ULift.{u + 1} ℤ)))
      (commStructureSheafLift X)).symm
    (integerToStructurePresheaf X)

/-- `integerToStructureSheaf` is the sheafification adjunct of
`integerToStructurePresheaf`. -/
theorem integerToStructureSheaf_adjunct (X : AlgebraicSpace S) :
    integerToStructureSheaf X =
      ((sheafificationAdjunction (smallEtaleTopology X) CommRingCat.{u + 1}).homEquiv
          ((Functor.const (smallEtaleSite X)ᵒᵖ).obj (CommRingCat.of (ULift.{u + 1} ℤ)))
          (commStructureSheafLift X)).symm
        (integerToStructurePresheaf X) :=
  sorry

/-- The underlying morphism of ring sheaves associated to `integerToStructureSheaf`. -/
noncomputable def integerToStructureRingSheafMap (X : AlgebraicSpace S) :
    CategoryTheory.Sheaf.ringSheafOfComm.{u + 1, u + 1, u}
        (constantIntegerRingSheaf X) ⟶ (commRingedSiteLift X).structureSheaf :=
  ringSheafMap.{u + 1, u, u + 1} (integerToStructureSheaf X)

/-- `integerToStructureRingSheafMap` is `ringSheafMap` of `integerToStructureSheaf`. -/
theorem integerToStructureRingSheafMap_def (X : AlgebraicSpace S) :
    integerToStructureRingSheafMap X =
      ringSheafMap.{u + 1, u, u + 1} (integerToStructureSheaf X) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
