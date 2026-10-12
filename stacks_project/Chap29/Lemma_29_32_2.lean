/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.MorphismDifferentials
public import Mathlib.AlgebraicGeometry.Scheme
import StacksCheckRecall

@[expose] public section

namespace AlgebraicGeometry

universe u

variable {X S : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ S)

/- Lemma 29.32.2: for a morphism of schemes `f : X ⟶ S`, morphisms from the sheaf of
relative differentials are naturally isomorphic to `S`-derivations of `𝒪_X`. -/
@[stacks 01UR] #check
  (AlgebraicGeometry.RingedSpace.Hom.representingIso f.toShHom :
    CategoryTheory.coyoneda.obj
        (Opposite.op (AlgebraicGeometry.RingedSpace.Hom.differentials f.toShHom)) ≅
      AlgebraicGeometry.RingedSpace.Hom.derivationsFunctor f.toShHom)

variable (F : AlgebraicGeometry.RingedSpace.Modules X.toSheafedSpace)
  (α : AlgebraicGeometry.RingedSpace.Hom.differentials f.toShHom ⟶ F)

/- The forward component sends `α` to its composite with the universal derivation. -/
#check
  (SheafOfModules.RingedSite.RelativeDifferentials.representingIso_hom_app
      (AlgebraicGeometry.RingedSpace.Hom.inverseImageStructureSheafHomComm f.toShHom) F α :
    (AlgebraicGeometry.RingedSpace.Hom.representingIso f.toShHom).hom.app F α =
      (AlgebraicGeometry.RingedSpace.Hom.universalDerivation f.toShHom).postcomp α.val)

end AlgebraicGeometry
