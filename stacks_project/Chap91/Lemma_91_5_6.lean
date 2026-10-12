/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap91.Lemma_91_4_3
public import stacks_project.Chap91.Lemma_91_5_6_Lift
import Mathlib.Tactic.CrossRefAttribute

/-!
# Isomorphism classes of flat lifts along a strict morphism of first-order thickenings

In Situation 91.3.1, if `(f, f')` is strict and `F` is flat over `S`, and if there exists
a pair `(F', α)` with `F'` flat over `S'` and `α : i^* F' ≅ F`, then isomorphism classes
of such pairs are principal homogeneous under `Ext¹_{𝒪_X}(F, ℐ ⊗ F)`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.MonoidalCategory
open AlgebraicGeometry.RingedSpace
open AlgebraicGeometry.RingedSpace (Modules)
open AlgebraicGeometry.RingedSpace.Hom
open AlgebraicGeometry.RingedSpace.Modules
open AlgebraicGeometry.RingedSpace.Modules.InfinitesimalExtension
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace.Thickening
namespace Hom
namespace FlatLift

variable {T U : Thickening.{u}} [IsFirstOrderThickening T.hom] [IsFirstOrderThickening U.hom]
variable {g : T ⟶ U} {F : T.left.Modules}

/-- Lemma 91.5.6: Let `(f, f')` be a morphism of first-order thickenings as in
Situation 91.3.1. Let `F` be an `𝒪_X`-module. Assume `(f, f')` is a strict morphism of
thickenings and `F` is flat over `S`. If there exists a pair `(F', α)` consisting of an
`𝒪_{X'}`-module `F'` flat over `S'` and an isomorphism `α : i^* F' ≅ F`, then the
isomorphism classes of such pairs are principal homogeneous under
`Ext¹_{𝒪_X}(F, ℐ ⊗ F)`. The acting group is `ExtensionClass (ℐ ⊗ F) F`, identified
with `Ext F (ℐ ⊗ F) 1` by `ExtensionClass.toExt`; the existence hypothesis is the
basepoint `L0`, transported to the 08L4 sequence with infinitesimal map `c = 1`. -/
@[stacks 08LM]
def isoClassEquiv (hg : IsStrict g) [SheafOfModules.IsFlatOver F g.left]
    (L0 : FlatLift g F) :
    ExtensionClass (idealModule T.hom ⊗ F) F ≃
      IsoClass T.hom F (idealModule T.hom ⊗ F) (infMapId T.hom F) :=
  InfinitesimalExtension.isoClassEquiv (toInfinitesimalExtension hg L0)

/-- The based chart sends an `𝒪_X`-extension class `ξ` to the translate of the basepoint. -/
theorem isoClassEquiv_apply (hg : IsStrict g) [SheafOfModules.IsFlatOver F g.left]
    (L0 : FlatLift g F) (ξ : ExtensionClass (idealModule T.hom ⊗ F) F) :
    isoClassEquiv hg L0 ξ = ξ +ᵥ IsoClass.mk (toInfinitesimalExtension hg L0) :=
  sorry

/-- The zero extension class is sent to the class of the associated 08L4 extension. -/
theorem isoClassEquiv_zero (hg : IsStrict g) [SheafOfModules.IsFlatOver F g.left]
    (L0 : FlatLift g F) :
    isoClassEquiv hg L0 0 = IsoClass.mk (toInfinitesimalExtension hg L0) :=
  sorry

/-- The inverse chart is torsor subtraction against the basepoint. -/
theorem isoClassEquiv_symm_apply (hg : IsStrict g) [SheafOfModules.IsFlatOver F g.left]
    (L0 : FlatLift g F) (p : IsoClass T.hom F (idealModule T.hom ⊗ F) (infMapId T.hom F)) :
    (isoClassEquiv hg L0).symm p = p -ᵥ IsoClass.mk (toInfinitesimalExtension hg L0) :=
  sorry

/-- Once one flat lift exists, every 08L4 extension with infinitesimal map `c = 1` is
flat over `S'`. -/
theorem isFlatOver_of_infMapId (hg : IsStrict g) [SheafOfModules.IsFlatOver F g.left]
    (L0 : FlatLift g F)
    (E : InfinitesimalExtension T.hom F (idealModule T.hom ⊗ F) (infMapId T.hom F)) :
    SheafOfModules.IsFlatOver E.module g.right :=
  sorry

end FlatLift
end Hom
end AlgebraicGeometry.RingedSpace.Thickening
