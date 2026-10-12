/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.HasExt
public import ReasLib.CategoryTheory.Abelian.Extension.Ext
public import stacks_project.Chap91.Remark_91_4_6_Class
public import stacks_project.Chap91.Remark_91_4_6_Trivial
import Mathlib.Tactic.CrossRefAttribute

/-!
# Trivial 08L4 extensions and their Ext¹ classes

A chosen trivialization of a first-order thickening of ringed spaces supplies a split origin
for 08L4 extensions with a prescribed infinitesimal map, and identifies isomorphism classes
of such extensions with `Ext¹_{𝒪_X}(ℱ, 𝒦)`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.MonoidalCategory
open CategoryTheory.Abelian (Ext)
open AlgebraicGeometry.RingedSpace
open AlgebraicGeometry.RingedSpace.Hom
open AlgebraicGeometry.RingedSpace.IsFirstOrderThickening
open AlgebraicGeometry.RingedSpace.Modules
open AlgebraicGeometry.RingedSpace.Modules.InfinitesimalExtension
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace.Modules
namespace InfinitesimalExtension

variable {X X' : RingedSpace.{u}} {i : X ⟶ X'} [IsFirstOrderThickening i]

/-- Remark 91.4.6 (1) Let `i : (X, 𝒪_X) ⟶ (X', 𝒪_{X'})` be a trivial first-order thickening of
ringed spaces and let `π : (X', 𝒪_{X'}) ⟶ (X, 𝒪_X)` be a trivialization. Given a pair of
`𝒪_X`-modules `ℱ`, `𝒦` and a map `c : ℐ ⊗_{𝒪_X} ℱ ⟶ 𝒦`, the trivial extension
`ℱ'_{c,triv} = ℱ ⊕ 𝒦` is the 08L4 sequence whose middle `𝒪_{X'}`-module is the product of
`i_* ℱ` and `i_* 𝒦` with action from the splitting 91.4.5.1 associated to `π` and the
mixed-scalar form of `c`. -/
@[stacks 08LB]
abbrev trivial (τ : Trivialization i) {F K : X.Modules}
    (c : kernelIdealSheaf i ⊗ (i _*).obj F ⟶ (i _*).obj K) :
    InfinitesimalExtension i F K c :=
  trivialExtension τ c

/-- The trivial 08L4 sequence is short exact. -/
theorem trivial_isShortExact (τ : Trivialization i) {F K : X.Modules}
    (c : kernelIdealSheaf i ⊗ (i _*).obj F ⟶ (i _*).obj K) :
    (ShortComplex.mk (trivial τ c).ι (trivial τ c).π (trivial τ c).w).ShortExact := sorry

/-- The infinitesimal map of the trivial extension equals the prescribed mixed-scalar `c`. -/
theorem trivial_infMap (τ : Trivialization i) {F K : X.Modules}
    (c : kernelIdealSheaf i ⊗ (i _*).obj F ⟶ (i _*).obj K) :
    infinitesimalMap i (trivial τ c).ι (trivial τ c).π (trivial τ c).w
      (trivial τ c).shortExact = c := sorry

/-- Remark 91.4.6 (2) Given any 08L4 extension `ℱ'` with infinitesimal map `c`, the
trivialization `π` supplies `π^♯ : 𝒪_X ⟶ 𝒪_{X'}` and the pushforward `π_* ℱ'` is an
`𝒪_X`-module extension of `ℱ` by `𝒦`, hence a class `ξ_{ℱ'}` in `Ext ℱ 𝒦 1`. -/
@[stacks 08LB]
def extClass [HasExt.{u} X.Modules] (τ : Trivialization i) {F K : X.Modules}
    {c : kernelIdealSheaf i ⊗ (i _*).obj F ⟶ (i _*).obj K}
    (E : InfinitesimalExtension i F K c) : Ext F K 1 :=
  (restrictExtension τ E).extClass

/-- Morphisms of 08L4 extensions preserve the `Ext¹` class attached to a trivialization. -/
theorem extClass_hom [HasExt.{u} X.Modules] (τ : Trivialization i) {F K : X.Modules}
    {c : kernelIdealSheaf i ⊗ (i _*).obj F ⟶ (i _*).obj K}
    {E₁ E₂ : InfinitesimalExtension i F K c} (φ : Hom E₁ E₂) :
    extClass τ E₁ = extClass τ E₂ := sorry

/-- The class `ξ_{ℱ'}` is the image of the restricted `𝒪_X`-extension under `toExt`. -/
theorem extClass_eq_toExt_restrict [HasExt.{u} X.Modules] (τ : Trivialization i)
    {F K : X.Modules} {c : kernelIdealSheaf i ⊗ (i _*).obj F ⟶ (i _*).obj K}
    (E : InfinitesimalExtension i F K c) :
    extClass τ E = ExtensionClass.toExt ⟦restrictExtension τ E⟧ := sorry

/-- The map on isomorphism classes induced by `ξ_{ℱ'}`. -/
def extClassOnIsoClass [HasExt.{u} X.Modules] (τ : Trivialization i) {F K : X.Modules}
    (c : kernelIdealSheaf i ⊗ (i _*).obj F ⟶ (i _*).obj K) :
    IsoClass i F K c → Ext F K 1 :=
  Quotient.lift (fun E ↦ extClass τ E) fun E₁ E₂ h ↦
    extClass_hom τ (Classical.choice (h : Nonempty (Hom E₁ E₂)))

/-- The induced map on isomorphism classes evaluates on a representative. -/
theorem extClassOnIsoClass_mk [HasExt.{u} X.Modules] (τ : Trivialization i)
    {F K : X.Modules} {c : kernelIdealSheaf i ⊗ (i _*).obj F ⟶ (i _*).obj K}
    (E : InfinitesimalExtension i F K c) :
    extClassOnIsoClass τ c (IsoClass.mk E) = extClass τ E := sorry

/-- Remark 91.4.6 (3) Lemma 91.4.3 implies that `ℱ' ↦ ξ_{ℱ'}` induces a bijection from
isomorphism classes of 08L4 extensions with infinitesimal map `c` to
`Ext¹_{𝒪_X}(ℱ, 𝒦)`. -/
@[stacks 08LB]
theorem extClass_bijective [HasExt.{u} X.Modules] (τ : Trivialization i) {F K : X.Modules}
    (c : kernelIdealSheaf i ⊗ (i _*).obj F ⟶ (i _*).obj K) :
    Function.Bijective (extClassOnIsoClass τ c) := sorry

/-- Remark 91.4.6 (4) The trivial extension `ℱ'_{c,triv}` maps to the zero class in
`Ext¹_{𝒪_X}(ℱ, 𝒦)`. -/
@[stacks 08LB]
theorem extClass_trivial [HasExt.{u} X.Modules] (τ : Trivialization i) {F K : X.Modules}
    (c : kernelIdealSheaf i ⊗ (i _*).obj F ⟶ (i _*).obj K) :
    extClass τ (trivial τ c) = 0 := sorry

end InfinitesimalExtension
end AlgebraicGeometry.RingedSpace.Modules
