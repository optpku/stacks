/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Amitsur.Complex
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Cech
public import ReasLib.CategoryTheory.Limits.FormalCoproduct.Singleton.Over

/-!
# Amitsur complexes for finite families on ringed sites

This module constructs the restriction homomorphism from a covered object to the
coproduct of a finite family and its ordinary Amitsur complex with coefficients.
-/

@[expose] public section

open CategoryTheory Opposite
open CategoryTheory.Limits

noncomputable section

universe w v u

namespace SheafOfModules.RingedSite.Cech

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}

/-- The restriction homomorphism from sections on the covered object to sections on the
coproduct of a finite family. -/
def coproductSectionsMap (𝒪 : Cᵒᵖ ⥤ CommRingCat.{w}) (U : C) {n : ℕ}
    (family : Fin n → Over U) [HasCoproduct (fun i ↦ (family i).left)] :
    𝒪.obj (op U) →+*
      𝒪.obj (op ((FormalCoproduct.Over.coproductSingleton
        (FormalCoproduct.mk (Fin n) family)).obj PUnit.unit).left) :=
  CommRingCat.Hom.hom (𝒪.map
    ((FormalCoproduct.Over.coproductSingleton
      (FormalCoproduct.mk (Fin n) family)).obj PUnit.unit).hom.op)

/-- `coproductSectionsMap` is the restriction map along the unique coproduct arrow to the
covered object. -/
theorem coproductSectionsMap_def (𝒪 : Cᵒᵖ ⥤ CommRingCat.{w}) (U : C) {n : ℕ}
    (family : Fin n → Over U) [HasCoproduct (fun i ↦ (family i).left)] :
    coproductSectionsMap 𝒪 U family =
      CommRingCat.Hom.hom (𝒪.map
        ((FormalCoproduct.Over.coproductSingleton
          (FormalCoproduct.mk (Fin n) family)).obj PUnit.unit).hom.op) := sorry

/-- The ordinary Amitsur complex for the coproduct restriction map, with coefficients in the
module of sections over the covered object. -/
def amitsurComplex (𝒪 : Cᵒᵖ ⥤ CommRingCat.{w}) (U : C) {n : ℕ}
    (family : Fin n → Over U) [HasCoproduct (fun i ↦ (family i).left)]
    (M : PresheafOfModules.{w} (𝒪 ⋙ forget₂ CommRingCat RingCat)) :
    CochainComplex (ModuleCat.{w} (𝒪.obj (op U))) ℕ :=
  @Algebra.Amitsur.complex (𝒪.obj (op U))
    (𝒪.obj (op ((FormalCoproduct.Over.coproductSingleton
      (FormalCoproduct.mk (Fin n) family)).obj PUnit.unit).left)) (M.obj (op U))
    _ _ (coproductSectionsMap 𝒪 U family).toAlgebra _ _

/-- `amitsurComplex` is the ordinary Amitsur complex of the explicit coproduct sections map. -/
theorem amitsurComplex_def (𝒪 : Cᵒᵖ ⥤ CommRingCat.{w}) (U : C) {n : ℕ}
    (family : Fin n → Over U) [HasCoproduct (fun i ↦ (family i).left)]
    (M : PresheafOfModules.{w} (𝒪 ⋙ forget₂ CommRingCat RingCat)) :
    amitsurComplex 𝒪 U family M =
      @Algebra.Amitsur.complex (𝒪.obj (op U))
        (𝒪.obj (op ((FormalCoproduct.Over.coproductSingleton
          (FormalCoproduct.mk (Fin n) family)).obj PUnit.unit).left)) (M.obj (op U))
        _ _ (coproductSectionsMap 𝒪 U family).toAlgebra _ _ := sorry

end SheafOfModules.RingedSite.Cech
