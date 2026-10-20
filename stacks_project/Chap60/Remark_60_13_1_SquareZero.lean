/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import stacks_project.Chap60.Situation_60_7_5
public import stacks_project.Chap60.«60_8_1_2_CrystallineObject»
public import stacks_project.Chap60.Lemma_60_3_1_SquareZero
public import stacks_project.Chap60.Lemma_60_12_3_Differentials
public import stacks_project.Chap60.«60_9_1_1_Site»
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.MorphismDifferentials
public import ReasLib.AlgebraicGeometry.Scheme.IdealSubobject
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Thickening.SquareZeroExtension
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.SquareZeroExtension
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Derivation.InverseImage
import Mathlib.Tactic.CrossRefAttribute

open AlgebraicGeometry CategoryTheory TopologicalSpace
open AlgebraicGeometry.IsFirstOrderThickening
open CrystallineObject
open SheafOfModules.RingedSite
open SheafOfModules.RingedSite.SquareZeroExtension
open scoped AlgebraicGeometry RelativeDerivation

@[expose] public section

open AlgebraicGeometry.Scheme.Crystalline

noncomputable section

universe u

namespace CrystallineObject.FirstOrderThickening

/-- The opposite involution sends one to one in a commutative ring. -/
theorem unop_one (R : Type u) [CommRing R] :
    MulOpposite.unop (1 : Rᵐᵒᵖ) = 1 := sorry

/-- The opposite involution is multiplicative after commuting factors. -/
theorem unop_mul (R : Type u) [CommRing R] (x y : Rᵐᵒᵖ) :
    MulOpposite.unop (x * y) = MulOpposite.unop x * MulOpposite.unop y := sorry

/-- The opposite involution sends zero to zero. -/
theorem unop_zero (R : Type u) [CommRing R] :
    MulOpposite.unop (0 : Rᵐᵒᵖ) = 0 := sorry

/-- The opposite involution preserves addition. -/
theorem unop_add (R : Type u) [CommRing R] (x y : Rᵐᵒᵖ) :
    MulOpposite.unop (x + y) = MulOpposite.unop x + MulOpposite.unop y := sorry

/-- The opposite action used in the explicit commutative square-zero rings. -/
abbrev oppositeModule (R : Type u) [CommRing R]
    (M : Type u) [AddCommGroup M] [Module R M] : Module Rᵐᵒᵖ M :=
  Module.compHom M
    { toFun := MulOpposite.unop
      map_one' := unop_one R
      map_mul' := unop_mul R
      map_zero' := unop_zero R
      map_add' := unop_add R }

/-- The centrality law for the opposite action used in the square-zero model. -/
theorem oppositeModule_isCentral (R : Type u) [CommRing R]
    (M : Type u) [AddCommGroup M] [Module R M] [Module Rᵐᵒᵖ M] :
    IsCentralScalar R M := sorry

/-- The ring of square-zero sections over one open set. -/
def ring (R : CommRingCat.{u})
    (M : ModuleCat.{u} R) : CommRingCat.{u} :=
  -- Local instance justification (instance diamond): induced opposite action for multiplication.
  letI : Module Rᵐᵒᵖ M := oppositeModule R M
  -- Local instance justification (proof-local temporary data): centrality assembles this ring.
  letI : IsCentralScalar R M := oppositeModule_isCentral R M
  CommRingCat.of (TrivSqZeroExt R M)

/-- The function on square-zero sections induced by a restriction map. -/
def mapFun
    {S : Scheme.{u}} {I : S.IdealSheafData}
    {γ : ∀ V : S.affineOpens, DividedPowers (I.ideal V)}
    {h_compatible :
      ∀ (V : S.affineOpens) (f : Γ(S, V)),
        (γ V).IsDPMorphism (γ (S.affineBasicOpen f))
          (S.presheaf.map (homOfLE (S.basicOpen_le f)).op).hom}
    {X : Scheme.{u}} {x₀ : X ⟶ I.subscheme}
    (T : smallCrystallineSite S I γ h_compatible X x₀)
    {U V : (Opens T.obj.1.thickening.toTopCat)ᵒᵖ} (rho : U ⟶ V) :
    ring (T.obj.1.thickening.presheaf.obj U)
        ((Ω[T.obj.1.thickeningToBase.toShHom]).val.obj U) →
      ring (T.obj.1.thickening.presheaf.obj V)
        ((Ω[T.obj.1.thickeningToBase.toShHom]).val.obj V) :=
  fun z ↦ (T.obj.1.thickening.presheaf.map rho z.1,
    (Ω[T.obj.1.thickeningToBase.toShHom]).val.map rho z.2)

/-- The restriction function for the square-zero model preserves zero. -/
theorem mapFun_zero
    {S : Scheme.{u}} {I : S.IdealSheafData}
    {γ : ∀ V : S.affineOpens, DividedPowers (I.ideal V)}
    {h_compatible :
      ∀ (V : S.affineOpens) (f : Γ(S, V)),
        (γ V).IsDPMorphism (γ (S.affineBasicOpen f))
          (S.presheaf.map (homOfLE (S.basicOpen_le f)).op).hom}
    {X : Scheme.{u}} {x₀ : X ⟶ I.subscheme}
    (T : smallCrystallineSite S I γ h_compatible X x₀)
    {U V : (Opens T.obj.1.thickening.toTopCat)ᵒᵖ} (rho : U ⟶ V) :
    mapFun T rho 0 = 0 := sorry

/-- The restriction function for the square-zero model preserves one. -/
theorem mapFun_one
    {S : Scheme.{u}} {I : S.IdealSheafData}
    {γ : ∀ V : S.affineOpens, DividedPowers (I.ideal V)}
    {h_compatible :
      ∀ (V : S.affineOpens) (f : Γ(S, V)),
        (γ V).IsDPMorphism (γ (S.affineBasicOpen f))
          (S.presheaf.map (homOfLE (S.basicOpen_le f)).op).hom}
    {X : Scheme.{u}} {x₀ : X ⟶ I.subscheme}
    (T : smallCrystallineSite S I γ h_compatible X x₀)
    {U V : (Opens T.obj.1.thickening.toTopCat)ᵒᵖ} (rho : U ⟶ V) :
    mapFun T rho 1 = 1 := sorry

/-- The restriction function for the square-zero model preserves addition. -/
theorem mapFun_add
    {S : Scheme.{u}} {I : S.IdealSheafData}
    {γ : ∀ V : S.affineOpens, DividedPowers (I.ideal V)}
    {h_compatible :
      ∀ (V : S.affineOpens) (f : Γ(S, V)),
        (γ V).IsDPMorphism (γ (S.affineBasicOpen f))
          (S.presheaf.map (homOfLE (S.basicOpen_le f)).op).hom}
    {X : Scheme.{u}} {x₀ : X ⟶ I.subscheme}
    (T : smallCrystallineSite S I γ h_compatible X x₀)
    {U V : (Opens T.obj.1.thickening.toTopCat)ᵒᵖ} (rho : U ⟶ V)
    [Module (T.obj.1.thickening.presheaf.obj U)ᵐᵒᵖ
      ((Ω[T.obj.1.thickeningToBase.toShHom]).val.obj U)]
    [IsCentralScalar (T.obj.1.thickening.presheaf.obj U)
      ((Ω[T.obj.1.thickeningToBase.toShHom]).val.obj U)]
    [Module (T.obj.1.thickening.presheaf.obj V)ᵐᵒᵖ
      ((Ω[T.obj.1.thickeningToBase.toShHom]).val.obj V)]
    [IsCentralScalar (T.obj.1.thickening.presheaf.obj V)
      ((Ω[T.obj.1.thickeningToBase.toShHom]).val.obj V)]
    (x y : ring (T.obj.1.thickening.presheaf.obj U)
      ((Ω[T.obj.1.thickeningToBase.toShHom]).val.obj U)) :
    mapFun T rho (x + y) =
      mapFun T rho x + mapFun T rho y := sorry

/-- The restriction function for the square-zero model preserves multiplication. -/
theorem mapFun_mul
    {S : Scheme.{u}} {I : S.IdealSheafData}
    {γ : ∀ V : S.affineOpens, DividedPowers (I.ideal V)}
    {h_compatible :
      ∀ (V : S.affineOpens) (f : Γ(S, V)),
        (γ V).IsDPMorphism (γ (S.affineBasicOpen f))
          (S.presheaf.map (homOfLE (S.basicOpen_le f)).op).hom}
    {X : Scheme.{u}} {x₀ : X ⟶ I.subscheme}
    (T : smallCrystallineSite S I γ h_compatible X x₀)
    {U V : (Opens T.obj.1.thickening.toTopCat)ᵒᵖ} (rho : U ⟶ V)
    (x y : ring (T.obj.1.thickening.presheaf.obj U)
      ((Ω[T.obj.1.thickeningToBase.toShHom]).val.obj U)) :
    mapFun T rho (x * y) =
      mapFun T rho x * mapFun T rho y := sorry

/-- The restriction morphism for the explicit square-zero presheaf. -/
def map
    {S : Scheme.{u}} {I : S.IdealSheafData}
    {γ : ∀ V : S.affineOpens, DividedPowers (I.ideal V)}
    {h_compatible :
      ∀ (V : S.affineOpens) (f : Γ(S, V)),
        (γ V).IsDPMorphism (γ (S.affineBasicOpen f))
          (S.presheaf.map (homOfLE (S.basicOpen_le f)).op).hom}
    {X : Scheme.{u}} {x₀ : X ⟶ I.subscheme}
    (T : smallCrystallineSite S I γ h_compatible X x₀)
    {U V : (Opens T.obj.1.thickening.toTopCat)ᵒᵖ} (rho : U ⟶ V) :
    ring (T.obj.1.thickening.presheaf.obj U)
        ((Ω[T.obj.1.thickeningToBase.toShHom]).val.obj U) ⟶
      ring (T.obj.1.thickening.presheaf.obj V)
        ((Ω[T.obj.1.thickeningToBase.toShHom]).val.obj V) :=
  -- Local instance justification (instance diamond): induced source opposite action.
  letI : Module (T.obj.1.thickening.presheaf.obj U)ᵐᵒᵖ
      ((Ω[T.obj.1.thickeningToBase.toShHom]).val.obj U) := oppositeModule _ _
  -- Local instance justification (proof-local temporary data): source centrality law.
  letI : IsCentralScalar (T.obj.1.thickening.presheaf.obj U)
      ((Ω[T.obj.1.thickeningToBase.toShHom]).val.obj U) :=
    oppositeModule_isCentral _ _
  -- Local instance justification (instance diamond): induced target opposite action.
  letI : Module (T.obj.1.thickening.presheaf.obj V)ᵐᵒᵖ
      ((Ω[T.obj.1.thickeningToBase.toShHom]).val.obj V) := oppositeModule _ _
  -- Local instance justification (proof-local temporary data): target centrality law.
  letI : IsCentralScalar (T.obj.1.thickening.presheaf.obj V)
      ((Ω[T.obj.1.thickeningToBase.toShHom]).val.obj V) :=
    oppositeModule_isCentral _ _
  CommRingCat.ofHom
    { toFun := mapFun T rho
      map_zero' := mapFun_zero T rho
      map_one' := mapFun_one T rho
      map_add' := mapFun_add T rho
      map_mul' := mapFun_mul T rho }

/-- Identity restrictions act identically on the explicit square-zero presheaf. -/
theorem map_id
    {S : Scheme.{u}} {I : S.IdealSheafData}
    {γ : ∀ V : S.affineOpens, DividedPowers (I.ideal V)}
    {h_compatible :
      ∀ (V : S.affineOpens) (f : Γ(S, V)),
        (γ V).IsDPMorphism (γ (S.affineBasicOpen f))
          (S.presheaf.map (homOfLE (S.basicOpen_le f)).op).hom}
    {X : Scheme.{u}} {x₀ : X ⟶ I.subscheme}
    (T : smallCrystallineSite S I γ h_compatible X x₀)
    (U : (Opens T.obj.1.thickening.toTopCat)ᵒᵖ) :
    map T (𝟙 U) = 𝟙 _ := sorry

/-- Composite restrictions act compositionally on the explicit square-zero presheaf. -/
theorem map_comp
    {S : Scheme.{u}} {I : S.IdealSheafData}
    {γ : ∀ V : S.affineOpens, DividedPowers (I.ideal V)}
    {h_compatible :
      ∀ (V : S.affineOpens) (f : Γ(S, V)),
        (γ V).IsDPMorphism (γ (S.affineBasicOpen f))
          (S.presheaf.map (homOfLE (S.basicOpen_le f)).op).hom}
    {X : Scheme.{u}} {x₀ : X ⟶ I.subscheme}
    (T : smallCrystallineSite S I γ h_compatible X x₀)
    {U V W : (Opens T.obj.1.thickening.toTopCat)ᵒᵖ}
    (rho : U ⟶ V) (sigma : V ⟶ W) :
    map T (rho ≫ sigma) =
      map T rho ≫ map T sigma := sorry

/-- The explicit presheaf `𝒪_T ⊕ Ω[T/S]` with square-zero multiplication. -/
def presheaf
    {S : Scheme.{u}} {I : S.IdealSheafData}
    {γ : ∀ V : S.affineOpens, DividedPowers (I.ideal V)}
    {h_compatible :
      ∀ (V : S.affineOpens) (f : Γ(S, V)),
        (γ V).IsDPMorphism (γ (S.affineBasicOpen f))
          (S.presheaf.map (homOfLE (S.basicOpen_le f)).op).hom}
    {X : Scheme.{u}} {x₀ : X ⟶ I.subscheme}
    (T : smallCrystallineSite S I γ h_compatible X x₀) :
    (Opens T.obj.1.thickening.toTopCat)ᵒᵖ ⥤ CommRingCat.{u} where
  obj U := ring (T.obj.1.thickening.presheaf.obj U)
    ((Ω[T.obj.1.thickeningToBase.toShHom]).val.obj U)
  map rho := map T rho
  map_id := map_id T
  map_comp := map_comp T

/-- The explicit square-zero presheaf satisfies the sheaf condition. -/
theorem presheaf_isSheaf
    {S : Scheme.{u}} {I : S.IdealSheafData}
    {γ : ∀ V : S.affineOpens, DividedPowers (I.ideal V)}
    {h_compatible :
      ∀ (V : S.affineOpens) (f : Γ(S, V)),
        (γ V).IsDPMorphism (γ (S.affineBasicOpen f))
          (S.presheaf.map (homOfLE (S.basicOpen_le f)).op).hom}
    {X : Scheme.{u}} {x₀ : X ⟶ I.subscheme}
    (T : smallCrystallineSite S I γ h_compatible X x₀) :
    Presheaf.IsSheaf (Opens.grothendieckTopology T.obj.1.thickening)
      (presheaf T) := sorry

/-- The concrete square-zero sheaf `𝒪_T ⊕ Ω[T/S]`. -/
def sheaf
    {S : Scheme.{u}} {I : S.IdealSheafData}
    {γ : ∀ V : S.affineOpens, DividedPowers (I.ideal V)}
    {h_compatible :
      ∀ (V : S.affineOpens) (f : Γ(S, V)),
        (γ V).IsDPMorphism (γ (S.affineBasicOpen f))
          (S.presheaf.map (homOfLE (S.basicOpen_le f)).op).hom}
    {X : Scheme.{u}} {x₀ : X ⟶ I.subscheme}
    (T : smallCrystallineSite S I γ h_compatible X x₀) :
    TopCat.Sheaf CommRingCat.{u} T.obj.1.thickening.toTopCat :=
  ⟨presheaf T, presheaf_isSheaf T⟩

set_option backward.isDefEq.respectTransparency false in
/-- The projection component of the canonical square-zero sheaf. -/
noncomputable def projectionApp
    {S : Scheme.{u}} {I : S.IdealSheafData}
    {γ : ∀ V : S.affineOpens, DividedPowers (I.ideal V)}
    {h_compatible :
      ∀ (V : S.affineOpens) (f : Γ(S, V)),
        (γ V).IsDPMorphism (γ (S.affineBasicOpen f))
          (S.presheaf.map (homOfLE (S.basicOpen_le f)).op).hom}
    {X : Scheme.{u}} {x₀ : X ⟶ I.subscheme}
    (T : smallCrystallineSite S I γ h_compatible X x₀)
    (V : (Opens T.obj.1.thickening.toTopCat)ᵒᵖ) :
    (sheaf T).obj.obj V ⟶ T.obj.1.thickening.presheaf.obj V :=
  -- Local instance justification (instance diamond): induced square-zero opposite action.
  letI : Module (T.obj.1.thickening.presheaf.obj V)ᵐᵒᵖ
      ((Ω[T.obj.1.thickeningToBase.toShHom]).val.obj V) :=
    oppositeModule _ _
  -- Local instance justification (proof-local temporary data): centrality selects this ring.
  letI : IsCentralScalar (T.obj.1.thickening.presheaf.obj V)
      ((Ω[T.obj.1.thickeningToBase.toShHom]).val.obj V) :=
    oppositeModule_isCentral _ _
  CommRingCat.ofHom (TrivSqZeroExt.fstHom
      (T.obj.1.thickening.presheaf.obj V)
      (T.obj.1.thickening.presheaf.obj V)
      ((Ω[T.obj.1.thickeningToBase.toShHom]).val.obj V)).toRingHom

/-- Naturality of the canonical square-zero projection. -/
theorem projection_naturality
    {S : Scheme.{u}} {I : S.IdealSheafData}
    {γ : ∀ V : S.affineOpens, DividedPowers (I.ideal V)}
    {h_compatible :
      ∀ (V : S.affineOpens) (f : Γ(S, V)),
        (γ V).IsDPMorphism (γ (S.affineBasicOpen f))
          (S.presheaf.map (homOfLE (S.basicOpen_le f)).op).hom}
    {X : Scheme.{u}} {x₀ : X ⟶ I.subscheme}
    (T : smallCrystallineSite S I γ h_compatible X x₀)
    {U V : (Opens T.obj.1.thickening.toTopCat)ᵒᵖ} (f : U ⟶ V) :
    (sheaf T).obj.map f ≫ projectionApp T V =
      projectionApp T U ≫ T.obj.1.thickening.presheaf.map f := sorry

/-- The canonical projection from the square-zero sheaf to the structure sheaf. -/
noncomputable def projection
    {S : Scheme.{u}} {I : S.IdealSheafData}
    {γ : ∀ V : S.affineOpens, DividedPowers (I.ideal V)}
    {h_compatible :
      ∀ (V : S.affineOpens) (f : Γ(S, V)),
        (γ V).IsDPMorphism (γ (S.affineBasicOpen f))
          (S.presheaf.map (homOfLE (S.basicOpen_le f)).op).hom}
    {X : Scheme.{u}} {x₀ : X ⟶ I.subscheme}
    (T : smallCrystallineSite S I γ h_compatible X x₀) :
    sheaf T ⟶ T.obj.1.thickening.sheaf :=
  ObjectProperty.homMk
    { app := projectionApp T
      naturality := fun {_ _} f ↦ projection_naturality T f }

/-- The canonical square-zero projection is locally surjective. -/
instance projection_isLocallySurjective
    {S : Scheme.{u}} {I : S.IdealSheafData}
    {γ : ∀ V : S.affineOpens, DividedPowers (I.ideal V)}
    {h_compatible :
      ∀ (V : S.affineOpens) (f : Γ(S, V)),
        (γ V).IsDPMorphism (γ (S.affineBasicOpen f))
          (S.presheaf.map (homOfLE (S.basicOpen_le f)).op).hom}
    {X : Scheme.{u}} {x₀ : X ⟶ I.subscheme}
    (T : smallCrystallineSite S I γ h_compatible X x₀) :
    CategoryTheory.Sheaf.IsLocallySurjective (projection T) := sorry

/-- The kernel of the canonical square-zero projection squares to zero. -/
theorem projection_isSquareZero
    {S : Scheme.{u}} {I : S.IdealSheafData}
    {γ : ∀ V : S.affineOpens, DividedPowers (I.ideal V)}
    {h_compatible :
      ∀ (V : S.affineOpens) (f : Γ(S, V)),
        (γ V).IsDPMorphism (γ (S.affineBasicOpen f))
          (S.presheaf.map (homOfLE (S.basicOpen_le f)).op).hom}
    {X : Scheme.{u}} {x₀ : X ⟶ I.subscheme}
    (T : smallCrystallineSite S I γ h_compatible X x₀) :
    KernelIdeal.IsSquareZero (projection T) := sorry

/-- The kernel module of the canonical square-zero projection is quasicoherent. -/
instance projection_kernel_isQuasicoherent
    {S : Scheme.{u}} {I : S.IdealSheafData}
    {γ : ∀ V : S.affineOpens, DividedPowers (I.ideal V)}
    {h_compatible :
      ∀ (V : S.affineOpens) (f : Γ(S, V)),
        (γ V).IsDPMorphism (γ (S.affineBasicOpen f))
          (S.presheaf.map (homOfLE (S.basicOpen_le f)).op).hom}
    {X : Scheme.{u}} {x₀ : X ⟶ I.subscheme}
    (T : smallCrystallineSite S I γ h_compatible X x₀) :
    (Scheme.SquareZeroExtension.kernelModule (sheaf T)
      (projection T) (projection_isSquareZero T)).IsQuasicoherent := sorry

/-- The scheme with structure sheaf `𝒪_T ⊕ Ω[T/S]`. -/
def scheme
    {S : Scheme.{u}} {I : S.IdealSheafData}
    {γ : ∀ V : S.affineOpens, DividedPowers (I.ideal V)}
    {h_compatible :
      ∀ (V : S.affineOpens) (f : Γ(S, V)),
        (γ V).IsDPMorphism (γ (S.affineBasicOpen f))
          (S.presheaf.map (homOfLE (S.basicOpen_le f)).op).hom}
    {X : Scheme.{u}} {x₀ : X ⟶ I.subscheme}
    (T : smallCrystallineSite S I γ h_compatible X x₀) : Scheme.{u} :=
  Scheme.SquareZeroExtension.scheme (sheaf T)
    (projection T) (projection_isSquareZero T)

/-- The canonical inclusion `T ⟶ T'` for the explicit square-zero scheme. -/
def schemeInclusion
    {S : Scheme.{u}} {I : S.IdealSheafData}
    {γ : ∀ V : S.affineOpens, DividedPowers (I.ideal V)}
    {h_compatible :
      ∀ (V : S.affineOpens) (f : Γ(S, V)),
        (γ V).IsDPMorphism (γ (S.affineBasicOpen f))
          (S.presheaf.map (homOfLE (S.basicOpen_le f)).op).hom}
    {X : Scheme.{u}} {x₀ : X ⟶ I.subscheme}
    (T : smallCrystallineSite S I γ h_compatible X x₀) :
    T.obj.1.thickening ⟶ scheme T :=
  Scheme.SquareZeroExtension.ι (sheaf T)
    (projection T) (projection_isSquareZero T)

/-- The zero-section component `f ↦ (f, 0)` of the first lift. -/
def zeroLiftApp
    {S : Scheme.{u}} {I : S.IdealSheafData}
    {γ : ∀ V : S.affineOpens, DividedPowers (I.ideal V)}
    {h_compatible :
      ∀ (V : S.affineOpens) (f : Γ(S, V)),
        (γ V).IsDPMorphism (γ (S.affineBasicOpen f))
          (S.presheaf.map (homOfLE (S.basicOpen_le f)).op).hom}
    {X : Scheme.{u}} {x₀ : X ⟶ I.subscheme}
    (T : smallCrystallineSite S I γ h_compatible X x₀)
    (V : (Opens T.obj.1.thickening.toTopCat)ᵒᵖ) :
    T.obj.1.thickening.presheaf.obj V ⟶ (sheaf T).obj.obj V :=
  -- Local instance justification (instance diamond): induced target opposite action.
  letI : Module (T.obj.1.thickening.presheaf.obj V)ᵐᵒᵖ
      ((Ω[T.obj.1.thickeningToBase.toShHom]).val.obj V) := oppositeModule _ _
  -- Local instance justification (proof-local temporary data): target centrality law.
  letI : IsCentralScalar (T.obj.1.thickening.presheaf.obj V)
      ((Ω[T.obj.1.thickeningToBase.toShHom]).val.obj V) :=
    oppositeModule_isCentral _ _
  CommRingCat.ofHom (TrivSqZeroExt.inlHom
    (T.obj.1.thickening.presheaf.obj V)
    ((Ω[T.obj.1.thickeningToBase.toShHom]).val.obj V) :
    T.obj.1.thickening.presheaf.obj V →+*
      TrivSqZeroExt (T.obj.1.thickening.presheaf.obj V)
        ((Ω[T.obj.1.thickeningToBase.toShHom]).val.obj V))

/-- Naturality of the zero-section lift. -/
theorem zeroLift_naturality
    {S : Scheme.{u}} {I : S.IdealSheafData}
    {γ : ∀ V : S.affineOpens, DividedPowers (I.ideal V)}
    {h_compatible :
      ∀ (V : S.affineOpens) (f : Γ(S, V)),
        (γ V).IsDPMorphism (γ (S.affineBasicOpen f))
          (S.presheaf.map (homOfLE (S.basicOpen_le f)).op).hom}
    {X : Scheme.{u}} {x₀ : X ⟶ I.subscheme}
    (T : smallCrystallineSite S I γ h_compatible X x₀)
    {U V : (Opens T.obj.1.thickening.toTopCat)ᵒᵖ} (f : U ⟶ V) :
    T.obj.1.thickening.presheaf.map f ≫ zeroLiftApp T V =
      zeroLiftApp T U ≫ (sheaf T).obj.map f := sorry

/-- The sheaf morphism `f ↦ (f, 0)`. -/
def zeroLift
    {S : Scheme.{u}} {I : S.IdealSheafData}
    {γ : ∀ V : S.affineOpens, DividedPowers (I.ideal V)}
    {h_compatible :
      ∀ (V : S.affineOpens) (f : Γ(S, V)),
        (γ V).IsDPMorphism (γ (S.affineBasicOpen f))
          (S.presheaf.map (homOfLE (S.basicOpen_le f)).op).hom}
    {X : Scheme.{u}} {x₀ : X ⟶ I.subscheme}
    (T : smallCrystallineSite S I γ h_compatible X x₀) :
    T.obj.1.thickening.sheaf ⟶ sheaf T :=
  ObjectProperty.homMk
    { app := zeroLiftApp T
      naturality := fun {_ _} f ↦ zeroLift_naturality T f }

/-- The section function `f ↦ (f, d[T/S](f))` of the second lift. -/
def differentialLiftFun
    {S : Scheme.{u}} {I : S.IdealSheafData}
    {γ : ∀ V : S.affineOpens, DividedPowers (I.ideal V)}
    {h_compatible :
      ∀ (V : S.affineOpens) (f : Γ(S, V)),
        (γ V).IsDPMorphism (γ (S.affineBasicOpen f))
          (S.presheaf.map (homOfLE (S.basicOpen_le f)).op).hom}
    {X : Scheme.{u}} {x₀ : X ⟶ I.subscheme}
    (T : smallCrystallineSite S I γ h_compatible X x₀)
    (V : (Opens T.obj.1.thickening.toTopCat)ᵒᵖ) :
    T.obj.1.thickening.presheaf.obj V →
      ring (T.obj.1.thickening.presheaf.obj V)
        ((Ω[T.obj.1.thickeningToBase.toShHom]).val.obj V) :=
  fun f ↦ (f, (d[T.obj.1.thickeningToBase.toShHom]).d f)

/-- The differential lift preserves zero. -/
theorem differentialLiftFun_zero
    {S : Scheme.{u}} {I : S.IdealSheafData}
    {γ : ∀ V : S.affineOpens, DividedPowers (I.ideal V)}
    {h_compatible :
      ∀ (V : S.affineOpens) (f : Γ(S, V)),
        (γ V).IsDPMorphism (γ (S.affineBasicOpen f))
          (S.presheaf.map (homOfLE (S.basicOpen_le f)).op).hom}
    {X : Scheme.{u}} {x₀ : X ⟶ I.subscheme}
    (T : smallCrystallineSite S I γ h_compatible X x₀)
    (V : (Opens T.obj.1.thickening.toTopCat)ᵒᵖ) :
    differentialLiftFun T V 0 = 0 := sorry

/-- The differential lift preserves one. -/
theorem differentialLiftFun_one
    {S : Scheme.{u}} {I : S.IdealSheafData}
    {γ : ∀ V : S.affineOpens, DividedPowers (I.ideal V)}
    {h_compatible :
      ∀ (V : S.affineOpens) (f : Γ(S, V)),
        (γ V).IsDPMorphism (γ (S.affineBasicOpen f))
          (S.presheaf.map (homOfLE (S.basicOpen_le f)).op).hom}
    {X : Scheme.{u}} {x₀ : X ⟶ I.subscheme}
    (T : smallCrystallineSite S I γ h_compatible X x₀)
    (V : (Opens T.obj.1.thickening.toTopCat)ᵒᵖ) :
    differentialLiftFun T V 1 = 1 := sorry

/-- The differential lift preserves addition. -/
theorem differentialLiftFun_add
    {S : Scheme.{u}} {I : S.IdealSheafData}
    {γ : ∀ V : S.affineOpens, DividedPowers (I.ideal V)}
    {h_compatible :
      ∀ (V : S.affineOpens) (f : Γ(S, V)),
        (γ V).IsDPMorphism (γ (S.affineBasicOpen f))
          (S.presheaf.map (homOfLE (S.basicOpen_le f)).op).hom}
    {X : Scheme.{u}} {x₀ : X ⟶ I.subscheme}
    (T : smallCrystallineSite S I γ h_compatible X x₀)
    (V : (Opens T.obj.1.thickening.toTopCat)ᵒᵖ)
    (x y : T.obj.1.thickening.presheaf.obj V) :
    differentialLiftFun T V (x + y) =
      differentialLiftFun T V x + differentialLiftFun T V y := sorry

/-- The differential lift preserves multiplication. -/
theorem differentialLiftFun_mul
    {S : Scheme.{u}} {I : S.IdealSheafData}
    {γ : ∀ V : S.affineOpens, DividedPowers (I.ideal V)}
    {h_compatible :
      ∀ (V : S.affineOpens) (f : Γ(S, V)),
        (γ V).IsDPMorphism (γ (S.affineBasicOpen f))
          (S.presheaf.map (homOfLE (S.basicOpen_le f)).op).hom}
    {X : Scheme.{u}} {x₀ : X ⟶ I.subscheme}
    (T : smallCrystallineSite S I γ h_compatible X x₀)
    (V : (Opens T.obj.1.thickening.toTopCat)ᵒᵖ)
    [Module (T.obj.1.thickening.presheaf.obj V)ᵐᵒᵖ
      ((Ω[T.obj.1.thickeningToBase.toShHom]).val.obj V)]
    [IsCentralScalar (T.obj.1.thickening.presheaf.obj V)
      ((Ω[T.obj.1.thickeningToBase.toShHom]).val.obj V)]
    (x y : T.obj.1.thickening.presheaf.obj V) :
    differentialLiftFun T V (x * y) =
      differentialLiftFun T V x * differentialLiftFun T V y := sorry

/-- The component ring homomorphism of the universal-differential lift. -/
def differentialLiftApp
    {S : Scheme.{u}} {I : S.IdealSheafData}
    {γ : ∀ V : S.affineOpens, DividedPowers (I.ideal V)}
    {h_compatible :
      ∀ (V : S.affineOpens) (f : Γ(S, V)),
        (γ V).IsDPMorphism (γ (S.affineBasicOpen f))
          (S.presheaf.map (homOfLE (S.basicOpen_le f)).op).hom}
    {X : Scheme.{u}} {x₀ : X ⟶ I.subscheme}
    (T : smallCrystallineSite S I γ h_compatible X x₀)
    (V : (Opens T.obj.1.thickening.toTopCat)ᵒᵖ) :
    T.obj.1.thickening.presheaf.obj V ⟶ (sheaf T).obj.obj V :=
  -- Local instance justification (instance diamond): induced target opposite action.
  letI : Module (T.obj.1.thickening.presheaf.obj V)ᵐᵒᵖ
      ((Ω[T.obj.1.thickeningToBase.toShHom]).val.obj V) := oppositeModule _ _
  -- Local instance justification (proof-local temporary data): target centrality law.
  letI : IsCentralScalar (T.obj.1.thickening.presheaf.obj V)
      ((Ω[T.obj.1.thickeningToBase.toShHom]).val.obj V) :=
    oppositeModule_isCentral _ _
  CommRingCat.ofHom
    { toFun := differentialLiftFun T V
      map_zero' := differentialLiftFun_zero T V
      map_one' := differentialLiftFun_one T V
      map_add' := differentialLiftFun_add T V
      map_mul' := differentialLiftFun_mul T V }

/-- Naturality of the universal-differential lift. -/
theorem differentialLift_naturality
    {S : Scheme.{u}} {I : S.IdealSheafData}
    {γ : ∀ V : S.affineOpens, DividedPowers (I.ideal V)}
    {h_compatible :
      ∀ (V : S.affineOpens) (f : Γ(S, V)),
        (γ V).IsDPMorphism (γ (S.affineBasicOpen f))
          (S.presheaf.map (homOfLE (S.basicOpen_le f)).op).hom}
    {X : Scheme.{u}} {x₀ : X ⟶ I.subscheme}
    (T : smallCrystallineSite S I γ h_compatible X x₀)
    {U V : (Opens T.obj.1.thickening.toTopCat)ᵒᵖ} (f : U ⟶ V) :
    T.obj.1.thickening.presheaf.map f ≫ differentialLiftApp T V =
      differentialLiftApp T U ≫ (sheaf T).obj.map f := sorry

/-- The sheaf morphism `f ↦ (f, d[T/S](f))`. -/
def differentialLift
    {S : Scheme.{u}} {I : S.IdealSheafData}
    {γ : ∀ V : S.affineOpens, DividedPowers (I.ideal V)}
    {h_compatible :
      ∀ (V : S.affineOpens) (f : Γ(S, V)),
        (γ V).IsDPMorphism (γ (S.affineBasicOpen f))
          (S.presheaf.map (homOfLE (S.basicOpen_le f)).op).hom}
    {X : Scheme.{u}} {x₀ : X ⟶ I.subscheme}
    (T : smallCrystallineSite S I γ h_compatible X x₀) :
    T.obj.1.thickening.sheaf ⟶ sheaf T :=
  ObjectProperty.homMk
    { app := differentialLiftApp T
      naturality := fun {_ _} f ↦ differentialLift_naturality T f }

/-- The presheafed-space retraction induced by a lift into the square-zero sheaf. -/
def retractionToHom
    {S : Scheme.{u}} {I : S.IdealSheafData}
    {γ : ∀ V : S.affineOpens, DividedPowers (I.ideal V)}
    {h_compatible :
      ∀ (V : S.affineOpens) (f : Γ(S, V)),
        (γ V).IsDPMorphism (γ (S.affineBasicOpen f))
          (S.presheaf.map (homOfLE (S.basicOpen_le f)).op).hom}
    {X : Scheme.{u}} {x₀ : X ⟶ I.subscheme}
    (T : smallCrystallineSite S I γ h_compatible X x₀)
    (lift : T.obj.1.thickening.sheaf ⟶ sheaf T) :
    (scheme T).toPresheafedSpace ⟶
      T.obj.1.thickening.toPresheafedSpace where
  base := 𝟙 T.obj.1.thickening.toTopCat
  c := lift.hom

/-- A square-zero lift induces local homomorphisms on stalks. -/
theorem retractionToHom_isLocalHom
    {S : Scheme.{u}} {I : S.IdealSheafData}
    {γ : ∀ V : S.affineOpens, DividedPowers (I.ideal V)}
    {h_compatible :
      ∀ (V : S.affineOpens) (f : Γ(S, V)),
        (γ V).IsDPMorphism (γ (S.affineBasicOpen f))
          (S.presheaf.map (homOfLE (S.basicOpen_le f)).op).hom}
    {X : Scheme.{u}} {x₀ : X ⟶ I.subscheme}
    (T : smallCrystallineSite S I γ h_compatible X x₀)
    (lift : T.obj.1.thickening.sheaf ⟶ sheaf T)
    (x : scheme T) :
    IsLocalHom ((retractionToHom T lift).stalkMap x).hom := sorry

/-- The locally ringed-space retraction induced by a square-zero lift. -/
def retractionLRSHom
    {S : Scheme.{u}} {I : S.IdealSheafData}
    {γ : ∀ V : S.affineOpens, DividedPowers (I.ideal V)}
    {h_compatible :
      ∀ (V : S.affineOpens) (f : Γ(S, V)),
        (γ V).IsDPMorphism (γ (S.affineBasicOpen f))
          (S.presheaf.map (homOfLE (S.basicOpen_le f)).op).hom}
    {X : Scheme.{u}} {x₀ : X ⟶ I.subscheme}
    (T : smallCrystallineSite S I γ h_compatible X x₀)
    (lift : T.obj.1.thickening.sheaf ⟶ sheaf T) :
    (scheme T).toLocallyRingedSpace ⟶
      T.obj.1.thickening.toLocallyRingedSpace where
  toHom := retractionToHom T lift
  prop := retractionToHom_isLocalHom T lift

/-- The scheme retraction induced by a square-zero lift. -/
def retraction
    {S : Scheme.{u}} {I : S.IdealSheafData}
    {γ : ∀ V : S.affineOpens, DividedPowers (I.ideal V)}
    {h_compatible :
      ∀ (V : S.affineOpens) (f : Γ(S, V)),
        (γ V).IsDPMorphism (γ (S.affineBasicOpen f))
          (S.presheaf.map (homOfLE (S.basicOpen_le f)).op).hom}
    {X : Scheme.{u}} {x₀ : X ⟶ I.subscheme}
    (T : smallCrystallineSite S I γ h_compatible X x₀)
    (lift : T.obj.1.thickening.sheaf ⟶ sheaf T) :
    scheme T ⟶ T.obj.1.thickening :=
  ⟨retractionLRSHom T lift⟩

/-- The first scheme retraction induced by `f ↦ (f, 0)`. -/
def p₀Scheme
    {S : Scheme.{u}} {I : S.IdealSheafData}
    {γ : ∀ V : S.affineOpens, DividedPowers (I.ideal V)}
    {h_compatible :
      ∀ (V : S.affineOpens) (f : Γ(S, V)),
        (γ V).IsDPMorphism (γ (S.affineBasicOpen f))
          (S.presheaf.map (homOfLE (S.basicOpen_le f)).op).hom}
    {X : Scheme.{u}} {x₀ : X ⟶ I.subscheme}
    (T : smallCrystallineSite S I γ h_compatible X x₀) :
    scheme T ⟶ T.obj.1.thickening :=
  retraction T (zeroLift T)

/-- The second scheme retraction induced by `f ↦ (f, d[T/S](f))`. -/
def p₁Scheme
    {S : Scheme.{u}} {I : S.IdealSheafData}
    {γ : ∀ V : S.affineOpens, DividedPowers (I.ideal V)}
    {h_compatible :
      ∀ (V : S.affineOpens) (f : Γ(S, V)),
        (γ V).IsDPMorphism (γ (S.affineBasicOpen f))
          (S.presheaf.map (homOfLE (S.basicOpen_le f)).op).hom}
    {X : Scheme.{u}} {x₀ : X ⟶ I.subscheme}
    (T : smallCrystallineSite S I γ h_compatible X x₀) :
    scheme T ⟶ T.obj.1.thickening :=
  retraction T (differentialLift T)

end CrystallineObject.FirstOrderThickening
