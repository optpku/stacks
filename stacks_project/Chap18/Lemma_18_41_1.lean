/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.RingedSite.Module.LowerShriek
import StacksCheckRecall

/-!
# Lemma 18.41.1

Compatibility facade for module lower shriek along a continuous and cocontinuous functor of
sites.  The reusable functor, adjunction, and Hom equivalence are owned by ReasLib.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u₁ u₂ v₁ v₂ w z

namespace RingedSite.Cocontinuous

variable {C : Type u₁} [Category.{v₁} C]
variable {D : Type u₂} [Category.{v₂} D]
variable {J : GrothendieckTopology C} {K : GrothendieckTopology D}
variable (f : C ⥤ D) [f.IsContinuous J K] [f.IsCocontinuous J K]
variable (R : Sheaf K RingCat.{w})

/- Lemma 18.41.1 (0797): module inverse image over `f⁻¹R` admits a left adjoint. -/
@[stacks 0797 "existence"]
#check (inferInstance :
  (moduleInverseImage (J := J) (K := K) f R :
    SheafOfModules.{z} R ⥤
      SheafOfModules.{z} (inverseImageRingSheaf (J := J) (K := K) f R)).IsRightAdjoint)

/- Lemma 18.41.1 (0797): `moduleLowerShriek f R` is the chosen left adjoint. -/
@[stacks 0797 "lower shriek"]
#check (moduleLowerShriek (J := J) (K := K) f R :
  SheafOfModules.{z} (inverseImageRingSheaf (J := J) (K := K) f R) ⥤
    SheafOfModules.{z} R)

/- Lemma 18.41.1 (0797): the canonical lower-shriek/inverse-image adjunction. -/
@[stacks 0797 "adjunction"]
#check (moduleLowerShriek.adjunction (J := J) (K := K) f R :
  (moduleLowerShriek (J := J) (K := K) f R :
      SheafOfModules.{z} (inverseImageRingSheaf (J := J) (K := K) f R) ⥤
        SheafOfModules.{z} R) ⊣
    moduleInverseImage (J := J) (K := K) f R)

end RingedSite.Cocontinuous
