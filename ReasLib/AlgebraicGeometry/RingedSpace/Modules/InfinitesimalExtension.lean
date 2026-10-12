/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.Grothendieck
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Ideal.Action
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Pullback.Monoidal
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.TensorUnit
public import ReasLib.AlgebraicGeometry.RingedSpace.FirstOrderThickening

/-!
# Infinitesimal extensions of modules on first-order thickenings

An infinitesimal extension of an `𝒪_X`-module `ℱ` by `𝒦` along a first-order thickening
`i : X ⟶ X'` is a short exact sequence `0 ⟶ i_* 𝒦 ⟶ ℱ' ⟶ i_* ℱ ⟶ 0` of
`𝒪_{X'}`-modules whose infinitesimal map equals a prescribed `c : ℐ ⊗ ℱ ⟶ 𝒦`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open AlgebraicGeometry.RingedSpace
open AlgebraicGeometry.RingedSpace.Hom
open SheafOfModules.RingedSite.IdealSheaf
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace.Modules

variable {X X' : RingedSpace.{u}}
variable (i : X ⟶ X') [IsFirstOrderThickening i]

/-- Tensoring on the left by a module sheaf preserves zero morphisms. -/
instance instPreservesZeroMorphisms_tensorLeft {Y : RingedSpace.{u}} {M : Y.Modules} :
    (tensorLeft M).PreservesZeroMorphisms := sorry

/-- The kernel-ideal action on the middle term of a sequence of module sheaves is killed by the
quotient map. -/
theorem action_comp_π {F K : X.Modules} {F' : X'.Modules}
    (ι : (i _*).obj K ⟶ F') (π : F' ⟶ (i _*).obj F) :
    action (kernelIdealSubobject i) F' ≫ π = 0 := sorry

/-- The kernel-ideal action on the middle term, lifted through `ι`. -/
noncomputable def actionLift {F K : X.Modules} {F' : X'.Modules}
    (ι : (i _*).obj K ⟶ F') (π : F' ⟶ (i _*).obj F) (w : ι ≫ π = 0)
    (hSE : (ShortComplex.mk ι π w).ShortExact) :
    kernelIdealSheaf i ⊗ F' ⟶ (i _*).obj K :=
  have := hSE.mono_f
  hSE.exact.lift (action (kernelIdealSubobject i) F') (action_comp_π i ι π)

/-- The lifted action vanishes after precomposition with `ℐ ⊗ ι`. -/
theorem tensorι_comp_actionLift {F K : X.Modules} {F' : X'.Modules}
    (ι : (i _*).obj K ⟶ F') (π : F' ⟶ (i _*).obj F) (w : ι ≫ π = 0)
    (hSE : (ShortComplex.mk ι π w).ShortExact) :
    (tensorLeft (kernelIdealSheaf i)).map ι ≫ actionLift i ι π w hSE = 0 := sorry

/-- Tensoring the quotient map with the kernel ideal yields an epimorphism. -/
theorem tensor_π_epi {F K : X.Modules} {F' : X'.Modules}
    (ι : (i _*).obj K ⟶ F') (π : F' ⟶ (i _*).obj F) (w : ι ≫ π = 0)
    (hSE : (ShortComplex.mk ι π w).ShortExact) :
    Epi ((ShortComplex.mk ι π w).map (tensorLeft (kernelIdealSheaf i))).g := sorry

/-- The tensored sequence `ℐ ⊗ i_* 𝒦 ⟶ ℐ ⊗ ℱ' ⟶ ℐ ⊗ i_* ℱ` is exact. -/
theorem tensorSequence_exact {F K : X.Modules} {F' : X'.Modules}
    (ι : (i _*).obj K ⟶ F') (π : F' ⟶ (i _*).obj F) (w : ι ≫ π = 0)
    (hSE : (ShortComplex.mk ι π w).ShortExact) :
    ((ShortComplex.mk ι π w).map (tensorLeft (kernelIdealSheaf i))).Exact := sorry

/-- The `𝒪_{X'}`-linear infinitesimal comparison `ℐ ⊗ i_* ℱ ⟶ i_* 𝒦`. -/
noncomputable def infMapPushforward {F K : X.Modules} {F' : X'.Modules}
    (ι : (i _*).obj K ⟶ F') (π : F' ⟶ (i _*).obj F) (w : ι ≫ π = 0)
    (hSE : (ShortComplex.mk ι π w).ShortExact) :
    kernelIdealSheaf i ⊗ (i _*).obj F ⟶ (i _*).obj K :=
  have := tensor_π_epi i ι π w hSE
  (tensorSequence_exact i ι π w hSE).desc
    (actionLift i ι π w hSE) (tensorι_comp_actionLift i ι π w hSE)

/-- The canonical infinitesimal map `c_{ℱ'} : ℐ ⊗ ℱ ⟶ 𝒦` of a short exact sequence, as a morphism
of `𝒪_{X'}`-modules after pushing `ℱ` and `𝒦` forward along `i`. Identifying underlying
spaces recovers the `𝒪_X`-module map. -/
noncomputable def infinitesimalMap {F K : X.Modules} {F' : X'.Modules}
    (ι : (i _*).obj K ⟶ F') (π : F' ⟶ (i _*).obj F) (w : ι ≫ π = 0)
    (hSE : (ShortComplex.mk ι π w).ShortExact) :
    kernelIdealSheaf i ⊗ (i _*).obj F ⟶ (i _*).obj K :=
  infMapPushforward i ι π w hSE

/-- Inverse image of the infinitesimal map, landing in `𝒦` after the pullback-pushforward
counit. -/
noncomputable def infinitesimalMap_pullback {F K : X.Modules} {F' : X'.Modules}
    (ι : (i _*).obj K ⟶ F') (π : F' ⟶ (i _*).obj F) (w : ι ≫ π = 0)
    (hSE : (ShortComplex.mk ι π w).ShortExact) :
    idealModule i ⊗ (i ^*).obj ((i _*).obj F) ⟶ K :=
  (Functor.Monoidal.μIso (pullback i) (kernelIdealSheaf i) ((i _*).obj F)).hom ≫
    (i ^*).map (infinitesimalMap i ι π w hSE) ≫
      (pullbackPushforwardAdjunction i).counit.app K

/-- The infinitesimal comparison as an `𝒪_X`-module map `ℐ ⊗ ℱ ⟶ 𝒦`. -/
noncomputable def infinitesimalMap_restrict {F K : X.Modules}
    (c : kernelIdealSheaf i ⊗ (i _*).obj F ⟶ (i _*).obj K) :
    idealModule i ⊗ F ⟶ K :=
  tensorHom (𝟙 (idealModule i))
      (asIso ((pullbackPushforwardAdjunction i).counit.app F)).inv ≫
    (Functor.Monoidal.μIso (pullback i) (kernelIdealSheaf i) ((i _*).obj F)).hom ≫
      (i ^*).map c ≫ (pullbackPushforwardAdjunction i).counit.app K

/-- A short exact extension of `i_* ℱ` by `i_* 𝒦` along a first-order thickening, with
prescribed infinitesimal map `c`. -/
structure InfinitesimalExtension (F K : X.Modules) (c : kernelIdealSheaf i ⊗ (i _*).obj F ⟶ (i _*).obj K) where
  /-- The middle `𝒪_{X'}`-module `ℱ'`. -/
  module : X'.Modules
  /-- The inclusion `i_* 𝒦 ⟶ ℱ'`. -/
  ι : (i _*).obj K ⟶ module
  /-- The projection `ℱ' ⟶ i_* ℱ`. -/
  π : module ⟶ (i _*).obj F
  /-- The two maps compose to zero. -/
  w : ι ≫ π = 0
  /-- The sequence `i_* 𝒦 ⟶ ℱ' ⟶ i_* ℱ` is short exact. -/
  shortExact : (ShortComplex.mk ι π w).ShortExact
  /-- The infinitesimal map of the sequence equals the prescribed `c`. -/
  infMap_eq : infinitesimalMap i ι π w shortExact = c

namespace InfinitesimalExtension

variable {i}
variable {F K : X.Modules} {c : kernelIdealSheaf i ⊗ (i _*).obj F ⟶ (i _*).obj K}

/-- Assemble an infinitesimal extension from a short exact sequence of `𝒪_{X'}`-modules whose
infinitesimal map equals `c`. -/
noncomputable def of (F' : X'.Modules) (ι : (i _*).obj K ⟶ F')
    (π : F' ⟶ (i _*).obj F) (w : ι ≫ π = 0)
    (shortExact : (ShortComplex.mk ι π w).ShortExact)
    (infMap_eq : infinitesimalMap i ι π w shortExact = c) :
    InfinitesimalExtension i F K c where
  module := F'
  ι := ι
  π := π
  w := w
  shortExact := shortExact
  infMap_eq := infMap_eq

/-- An infinitesimal extension is a short exact sequence whose infinitesimal map equals `c`. -/
theorem spec (E : InfinitesimalExtension i F K c) :
    (ShortComplex.mk E.ι E.π E.w).ShortExact ∧
      infinitesimalMap i E.ι E.π E.w E.shortExact = c := sorry

/-- Morphisms of short exact extensions inducing the identity on the kernel and quotient. -/
structure Hom (E₁ E₂ : InfinitesimalExtension i F K c) where
  /-- The underlying morphism of middle `𝒪_{X'}`-modules. -/
  hom : E₁.module ⟶ E₂.module
  /-- Compatibility with the inclusions of `i_* 𝒦`. -/
  comm_ι : E₁.ι ≫ hom = E₂.ι
  /-- Compatibility with the projections onto `i_* ℱ`. -/
  comm_π : hom ≫ E₂.π = E₁.π

namespace Hom

/-- The identity morphism of an infinitesimal extension. -/
noncomputable def id (E : InfinitesimalExtension i F K c) : Hom E E where
  hom := 𝟙 E.module
  comm_ι := sorry
  comm_π := sorry

/-- Composition of morphisms of infinitesimal extensions. -/
noncomputable def comp {E₁ E₂ E₃ : InfinitesimalExtension i F K c}
    (φ : Hom E₁ E₂) (ψ : Hom E₂ E₃) : Hom E₁ E₃ where
  hom := φ.hom ≫ ψ.hom
  comm_ι := sorry
  comm_π := sorry

end Hom

/-- The infinitesimal map recovered from an infinitesimal extension equals the prescribed `c`. -/
theorem infMap_eq_c (E : InfinitesimalExtension i F K c) :
    infinitesimalMap i E.ι E.π E.w E.shortExact = c := sorry

end InfinitesimalExtension

end AlgebraicGeometry.RingedSpace.Modules
