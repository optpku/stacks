/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap91.Lemma_91_4_3_Torsor
import Mathlib.Tactic.CrossRefAttribute

/-!
# Isomorphism classes of 08L4 extensions

If a first-order thickening admits at least one 08L4 extension with a prescribed
infinitesimal map, then isomorphism classes of such extensions are a principal
homogeneous space under `𝒪_X`-extension classes, hence under `Ext¹_{𝒪_X}(ℱ, 𝒦)`
via `ExtensionClass.toExt`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.MonoidalCategory
open AlgebraicGeometry.RingedSpace
open AlgebraicGeometry.RingedSpace.Hom
open AlgebraicGeometry.RingedSpace.Modules
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace.Modules
namespace InfinitesimalExtension

variable {X X' : RingedSpace.{u}}
variable {i : X ⟶ X'} [IsFirstOrderThickening i]
variable {F K : X.Modules}
variable {c : kernelIdealSheaf i ⊗ (i _*).obj F ⟶ (i _*).obj K}

/-- Lemma 91.4.3: Let `i : (X, 𝒪_X) ⟶ (X', 𝒪_{X'})` be a first-order thickening of
ringed spaces. Given `𝒪_X`-modules `ℱ`, `𝒦` and an `𝒪_X`-linear map
`c : ℐ ⊗ ℱ ⟶ 𝒦`, if there exists an 08L4 sequence with infinitesimal map `c`, then
the set of isomorphism classes of these extensions is principal homogeneous under
`Ext¹_{𝒪_X}(ℱ, 𝒦)`. The acting group is `ExtensionClass 𝒦 ℱ`, identified with
`Ext ℱ 𝒦 1` by `ExtensionClass.toExt`; the existence hypothesis is the basepoint
`E0`. The difference of two such sequences is an `𝒪_X`-extension because its middle
term is annihilated by `ℐ`. -/
@[stacks 08L7]
def isoClassEquiv (E0 : InfinitesimalExtension i F K c) :
    ExtensionClass K F ≃ IsoClass i F K c where
  toFun ξ := ξ +ᵥ IsoClass.mk E0
  invFun p := p -ᵥ IsoClass.mk E0
  left_inv := sorry
  right_inv := sorry

/-- The based chart sends an `𝒪_X`-extension class `ξ` to the translate of the basepoint. -/
theorem isoClassEquiv_apply (E0 : InfinitesimalExtension i F K c) (ξ : ExtensionClass K F) :
    isoClassEquiv E0 ξ = ξ +ᵥ IsoClass.mk E0 := sorry

/-- The zero extension class is sent to the class of the basepoint. -/
theorem isoClassEquiv_zero (E0 : InfinitesimalExtension i F K c) :
    isoClassEquiv E0 0 = IsoClass.mk E0 := sorry

/-- The inverse chart is torsor subtraction against the basepoint. -/
theorem isoClassEquiv_symm_apply (E0 : InfinitesimalExtension i F K c)
    (p : IsoClass i F K c) :
    (isoClassEquiv E0).symm p = p -ᵥ IsoClass.mk E0 := sorry

end InfinitesimalExtension
end AlgebraicGeometry.RingedSpace.Modules
