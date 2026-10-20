module

public import stacks_project.Chap60.Situation_60_7_5
public import stacks_project.Chap60.Remark_60_13_1_SquareZero
public import stacks_project.Chap60.Lemma_60_12_3_Differentials
public import stacks_project.Chap60.Lemma_60_3_2_BilinearExtension
public import Mathlib.Algebra.Category.ModuleCat.ExteriorPower
public import Mathlib.LinearAlgebra.ExteriorPower.Basic
public import ReasLib.LinearAlgebra.ExteriorPower.LeftTensor
public import Mathlib.Algebra.Ring.MinimalAxioms
import Mathlib.Tactic.CrossRefAttribute

open AlgebraicGeometry CategoryTheory TopologicalSpace
open CrystallineObject
open SheafOfModules.RingedSite
open scoped AlgebraicGeometry RelativeDerivation
open exteriorPower

@[expose] public section

open AlgebraicGeometry.Scheme.Crystalline

noncomputable section

universe u

namespace CrystallineObject.SecondOrderThickening

/-- The explicit 4-tuple carrier `R × Ω × Ω × ⋀[R]^2 Ω`. -/
def RingCarrier (R : Type u) (Ω : Type u) [CommRing R] [AddCommGroup Ω] [Module R Ω] : Type u :=
  R × Ω × Ω × ⋀[R]^2 Ω

/-- The wedge product of two 1-forms as a 2-form. -/
def wedge {R : Type u} [CommRing R] {Ω : Type u} [AddCommGroup Ω] [Module R Ω]
    (x y : Ω) : ⋀[R]^2 Ω :=
  ιMulti (R := R) (n := 2) (fun i : Fin 2 => if i = 0 then x else y)

/-- The de Rham differential `dΩ : Ω → ⋀²Ω` associated to a derivation `d : R → Ω`,
defined on a chosen presentation `ω = ∑ f_i • d g_i` by `∑ d f_i ∧ d g_i`. -/
noncomputable def dΩ {R : Type u} [CommRing R] {Ω : Type u}
    [AddCommGroup Ω] [Module R Ω] (d : R → Ω) (ω : Ω) : ⋀[R]^2 Ω :=
  let p := Classical.epsilon fun q : Σ n : ℕ, (Fin n → R) × (Fin n → R) =>
    ω = ∑ i : Fin q.1, q.2.1 i • d (q.2.2 i)
  ∑ i : Fin p.1, wedge (d (p.2.1 i)) (d (p.2.2 i))

/-- On presented 1-forms, `dΩ(∑ f_i • d g_i) = ∑ d f_i ∧ d g_i`. -/
theorem d2_sum {R : Type u} [CommRing R] {Ω : Type u}
    [AddCommGroup Ω] [Module R Ω] (d : R → Ω) {n : ℕ}
    (f g : Fin n → R) :
    dΩ d (∑ i : Fin n, f i • d (g i)) =
      ∑ i : Fin n, wedge (d (f i)) (d (g i)) := sorry

/-- Zero in the 4-tuple carrier. -/
instance instZero (R : Type u) (Ω : Type u) [CommRing R] [AddCommGroup Ω] [Module R Ω] :
    Zero (RingCarrier R Ω) where
  zero := (0, 0, 0, 0)

/-- One in the 4-tuple carrier. -/
instance instOne (R : Type u) (Ω : Type u) [CommRing R] [AddCommGroup Ω] [Module R Ω] :
    One (RingCarrier R Ω) where
  one := (1, 0, 0, 0)

/-- Componentwise addition of 4-tuples. -/
instance instAdd (R : Type u) (Ω : Type u) [CommRing R] [AddCommGroup Ω] [Module R Ω] :
    Add (RingCarrier R Ω) where
  add x y := (x.1 + y.1, x.2.1 + y.2.1, x.2.2.1 + y.2.2.1, x.2.2.2 + y.2.2.2)

/-- Componentwise negation of 4-tuples. -/
instance instNeg (R : Type u) (Ω : Type u) [CommRing R] [AddCommGroup Ω] [Module R Ω] :
    Neg (RingCarrier R Ω) where
  neg x := (-x.1, -x.2.1, -x.2.2.1, -x.2.2.2)

/-- The source product on `𝒪 ⊕ Ω ⊕ Ω ⊕ Ω²`. -/
def mul {R : Type u} {Ω : Type u} [CommRing R] [AddCommGroup Ω] [Module R Ω]
    (x y : RingCarrier R Ω) : RingCarrier R Ω :=
  (x.1 * y.1,
    x.1 • y.2.1 + y.1 • x.2.1,
    x.1 • y.2.2.1 + y.1 • x.2.2.1,
    x.1 • y.2.2.2 + y.1 • x.2.2.2 + wedge x.2.1 y.2.2.1 + wedge y.2.1 x.2.2.1)

/-- Multiplication instance for the 4-tuple ring. -/
instance instMul (R : Type u) (Ω : Type u) [CommRing R] [AddCommGroup Ω] [Module R Ω] :
    Mul (RingCarrier R Ω) where
  mul := mul

/-- The commutative ring structure on the explicit 4-tuple carrier. -/
instance instCommRing (R : Type u) (Ω : Type u) [CommRing R] [AddCommGroup Ω] [Module R Ω] :
    CommRing (RingCarrier R Ω) :=
  CommRing.ofMinimalAxioms (by sorry) (by sorry) (by sorry) (by sorry) (by sorry) (by sorry)
    (by sorry)

/-- The coordinate formula for the source product. -/
theorem mul_spec {R : Type u} {Ω : Type u} [CommRing R] [AddCommGroup Ω] [Module R Ω]
    (f : R) (ω1 ω2 : Ω) (η : ⋀[R]^2 Ω) (f' : R) (ω1' ω2' : Ω) (η' : ⋀[R]^2 Ω) :
    mul (f, ω1, ω2, η) (f', ω1', ω2', η') =
      (f * f', f • ω1' + f' • ω1, f • ω2' + f' • ω2,
        f • η' + f' • η + wedge ω1 ω2' + wedge ω1' ω2) := sorry

/-- The bundled commutative ring `R ⊕ Ω ⊕ Ω ⊕ ⋀[R]^2 Ω`. -/
def ring (R : CommRingCat.{u}) (Ω : ModuleCat.{u} R) : CommRingCat.{u} :=
  CommRingCat.of (RingCarrier R Ω)

/-- Transport a 2-form along a map of 1-forms, using a chosen wedge presentation. -/
noncomputable def mapTwoForm {R S : Type u} [CommRing R] [CommRing S]
    {M : Type u} [AddCommGroup M] [Module R M]
    {N : Type u} [AddCommGroup N] [Module S N]
    (f : M → N) (η : ⋀[R]^2 M) : ⋀[S]^2 N :=
  let p := Classical.epsilon fun q : Σ n : ℕ, (Fin n → M) × (Fin n → M) =>
    η = ∑ i : Fin q.1, wedge (q.2.1 i) (q.2.2 i)
  ∑ i : Fin p.1, wedge (f (p.2.1 i)) (f (p.2.2 i))

/-- Restriction of 4-tuple sections along an open inclusion. -/
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
  fun z ↦
    (T.obj.1.thickening.presheaf.map rho z.1,
      (Ω[T.obj.1.thickeningToBase.toShHom]).val.map rho z.2.1,
      (Ω[T.obj.1.thickeningToBase.toShHom]).val.map rho z.2.2.1,
      mapTwoForm ((Ω[T.obj.1.thickeningToBase.toShHom]).val.map rho) z.2.2.2)

/-- Restriction preserves zero. -/
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

/-- Restriction preserves one. -/
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

/-- Restriction preserves addition. -/
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
    (x y : ring (T.obj.1.thickening.presheaf.obj U)
      ((Ω[T.obj.1.thickeningToBase.toShHom]).val.obj U)) :
    mapFun T rho (x + y) = mapFun T rho x + mapFun T rho y := sorry

/-- Restriction preserves multiplication. -/
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
    mapFun T rho (x * y) = mapFun T rho x * mapFun T rho y := sorry

/-- The restriction morphism of the explicit 4-tuple presheaf. -/
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
  CommRingCat.ofHom
    { toFun := mapFun T rho
      map_zero' := mapFun_zero T rho
      map_one' := mapFun_one T rho
      map_add' := mapFun_add T rho
      map_mul' := mapFun_mul T rho }

/-- Identity restrictions act identically. -/
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

/-- Composite restrictions act compositionally. -/
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
    map T (rho ≫ sigma) = map T rho ≫ map T sigma := sorry

/-- The explicit presheaf `𝒪_T ⊕ Ω ⊕ Ω ⊕ Ω²`. -/
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

/-- The explicit 4-tuple presheaf is a sheaf. -/
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

/-- The concrete sheaf `𝒪_{T''}`. -/
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

/-- The first-coordinate projection on sections. -/
def projectionApp
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
  CommRingCat.ofHom
    { toFun := fun z => z.1
      map_zero' := sorry
      map_one' := sorry
      map_add' := sorry
      map_mul' := sorry }

/-- Naturality of the 4-tuple projection. -/
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

/-- The canonical projection `𝒪_{T''} ⟶ 𝒪_T`. -/
def projection
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

/-- The 4-tuple projection is locally surjective. -/
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

/-- Stalks of `𝒪_{T''}` are local rings. -/
theorem stalk_isLocalRing
    {S : Scheme.{u}} {I : S.IdealSheafData}
    {γ : ∀ V : S.affineOpens, DividedPowers (I.ideal V)}
    {h_compatible :
      ∀ (V : S.affineOpens) (f : Γ(S, V)),
        (γ V).IsDPMorphism (γ (S.affineBasicOpen f))
          (S.presheaf.map (homOfLE (S.basicOpen_le f)).op).hom}
    {X : Scheme.{u}} {x₀ : X ⟶ I.subscheme}
    (T : smallCrystallineSite S I γ h_compatible X x₀)
    (x : T.obj.1.thickening) :
    IsLocalRing ((sheaf T).presheaf.stalk x) := sorry

/-- The locally ringed space with structure sheaf `𝒪_{T''}`. -/
def locallyRingedSpace
    {S : Scheme.{u}} {I : S.IdealSheafData}
    {γ : ∀ V : S.affineOpens, DividedPowers (I.ideal V)}
    {h_compatible :
      ∀ (V : S.affineOpens) (f : Γ(S, V)),
        (γ V).IsDPMorphism (γ (S.affineBasicOpen f))
          (S.presheaf.map (homOfLE (S.basicOpen_le f)).op).hom}
    {X : Scheme.{u}} {x₀ : X ⟶ I.subscheme}
    (T : smallCrystallineSite S I γ h_compatible X x₀) :
    LocallyRingedSpace.{u} where
  toSheafedSpace :=
    { carrier := T.obj.1.thickening.toTopCat
      presheaf := (sheaf T).presheaf
      IsSheaf := (sheaf T).2 }
  isLocalRing := stalk_isLocalRing T

/-- Affine neighbourhoods for the 4-tuple locally ringed space. -/
theorem locallyRingedSpace_local_affine
    {S : Scheme.{u}} {I : S.IdealSheafData}
    {γ : ∀ V : S.affineOpens, DividedPowers (I.ideal V)}
    {h_compatible :
      ∀ (V : S.affineOpens) (f : Γ(S, V)),
        (γ V).IsDPMorphism (γ (S.affineBasicOpen f))
          (S.presheaf.map (homOfLE (S.basicOpen_le f)).op).hom}
    {X : Scheme.{u}} {x₀ : X ⟶ I.subscheme}
    (T : smallCrystallineSite S I γ h_compatible X x₀) :
    ∀ x : locallyRingedSpace T,
      ∃ (U : OpenNhds x) (R : CommRingCat.{u}),
        Nonempty
          ((locallyRingedSpace T).restrict U.isOpenEmbedding ≅
            Spec.toLocallyRingedSpace.obj (Opposite.op R)) := sorry

/-- The scheme `T''` with structure sheaf `𝒪_T ⊕ Ω ⊕ Ω ⊕ Ω²`. -/
def scheme
    {S : Scheme.{u}} {I : S.IdealSheafData}
    {γ : ∀ V : S.affineOpens, DividedPowers (I.ideal V)}
    {h_compatible :
      ∀ (V : S.affineOpens) (f : Γ(S, V)),
        (γ V).IsDPMorphism (γ (S.affineBasicOpen f))
          (S.presheaf.map (homOfLE (S.basicOpen_le f)).op).hom}
    {X : Scheme.{u}} {x₀ : X ⟶ I.subscheme}
    (T : smallCrystallineSite S I γ h_compatible X x₀) : Scheme.{u} where
  toLocallyRingedSpace := locallyRingedSpace T
  local_affine := locallyRingedSpace_local_affine T

/-- The underlying presheafed inclusion `T ⟶ T''`. -/
def schemeInclusionToHom
    {S : Scheme.{u}} {I : S.IdealSheafData}
    {γ : ∀ V : S.affineOpens, DividedPowers (I.ideal V)}
    {h_compatible :
      ∀ (V : S.affineOpens) (f : Γ(S, V)),
        (γ V).IsDPMorphism (γ (S.affineBasicOpen f))
          (S.presheaf.map (homOfLE (S.basicOpen_le f)).op).hom}
    {X : Scheme.{u}} {x₀ : X ⟶ I.subscheme}
    (T : smallCrystallineSite S I γ h_compatible X x₀) :
    T.obj.1.thickening.toPresheafedSpace ⟶ (scheme T).toPresheafedSpace where
  base := 𝟙 T.obj.1.thickening.toTopCat
  c := (projection T).hom

/-- Stalk maps of the inclusion `T ⟶ T''` are local. -/
theorem schemeInclusionToHom_isLocalHom
    {S : Scheme.{u}} {I : S.IdealSheafData}
    {γ : ∀ V : S.affineOpens, DividedPowers (I.ideal V)}
    {h_compatible :
      ∀ (V : S.affineOpens) (f : Γ(S, V)),
        (γ V).IsDPMorphism (γ (S.affineBasicOpen f))
          (S.presheaf.map (homOfLE (S.basicOpen_le f)).op).hom}
    {X : Scheme.{u}} {x₀ : X ⟶ I.subscheme}
    (T : smallCrystallineSite S I γ h_compatible X x₀)
    (x : T.obj.1.thickening) :
    IsLocalHom ((schemeInclusionToHom T).stalkMap x).hom := sorry

/-- The scheme inclusion `T ⟶ T''`. -/
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
  ⟨{ toHom := schemeInclusionToHom T
     prop := schemeInclusionToHom_isLocalHom T }⟩

/-- An affine open of `T''` is affine in `T` on the same underlying open. -/
theorem baseOpen_isAffine
    {S : Scheme.{u}} {I : S.IdealSheafData}
    {γ : ∀ V : S.affineOpens, DividedPowers (I.ideal V)}
    {h_compatible :
      ∀ (V : S.affineOpens) (f : Γ(S, V)),
        (γ V).IsDPMorphism (γ (S.affineBasicOpen f))
          (S.presheaf.map (homOfLE (S.basicOpen_le f)).op).hom}
    {X : Scheme.{u}} {x₀ : X ⟶ I.subscheme}
    (T : smallCrystallineSite S I γ h_compatible X x₀)
    (V : (scheme T).affineOpens) :
    (V.1 : T.obj.1.thickening.Opens) ∈ T.obj.1.thickening.affineOpens := sorry

/-- The affine open of `T` underlying an affine open of `T''`. -/
def baseAffineOpen
    {S : Scheme.{u}} {I : S.IdealSheafData}
    {γ : ∀ V : S.affineOpens, DividedPowers (I.ideal V)}
    {h_compatible :
      ∀ (V : S.affineOpens) (f : Γ(S, V)),
        (γ V).IsDPMorphism (γ (S.affineBasicOpen f))
          (S.presheaf.map (homOfLE (S.basicOpen_le f)).op).hom}
    {X : Scheme.{u}} {x₀ : X ⟶ I.subscheme}
    (T : smallCrystallineSite S I γ h_compatible X x₀)
    (V : (scheme T).affineOpens) : T.obj.1.thickening.affineOpens :=
  ⟨V.1, baseOpen_isAffine T V⟩

/-- Affine 4-tuple sections of `T''` as the explicit 4-tuple ring. -/
abbrev affineSection
    {S : Scheme.{u}} {I : S.IdealSheafData}
    {γ : ∀ V : S.affineOpens, DividedPowers (I.ideal V)}
    {h_compatible :
      ∀ (V : S.affineOpens) (f : Γ(S, V)),
        (γ V).IsDPMorphism (γ (S.affineBasicOpen f))
          (S.presheaf.map (homOfLE (S.basicOpen_le f)).op).hom}
    {X : Scheme.{u}} {x₀ : X ⟶ I.subscheme}
    (T : smallCrystallineSite S I γ h_compatible X x₀)
    (V : (scheme T).affineOpens) : Type u :=
  (presheaf T).obj (Opposite.op (baseAffineOpen T V).1)

/-- Affine sections of `T''` are sections of the explicit 4-tuple presheaf. -/
theorem affineSection_eq
    {S : Scheme.{u}} {I : S.IdealSheafData}
    {γ : ∀ V : S.affineOpens, DividedPowers (I.ideal V)}
    {h_compatible :
      ∀ (V : S.affineOpens) (f : Γ(S, V)),
        (γ V).IsDPMorphism (γ (S.affineBasicOpen f))
          (S.presheaf.map (homOfLE (S.basicOpen_le f)).op).hom}
    {X : Scheme.{u}} {x₀ : X ⟶ I.subscheme}
    (T : smallCrystallineSite S I γ h_compatible X x₀)
    (V : (scheme T).affineOpens) :
    affineSection T V = (presheaf T).obj (Opposite.op (baseAffineOpen T V).1) := sorry

/-- The canonical module structure of `Ω[T/S]` on a second-order affine open. -/
abbrev differentialModule
    {S : Scheme.{u}} {I : S.IdealSheafData}
    {γ : ∀ V : S.affineOpens, DividedPowers (I.ideal V)}
    {h_compatible :
      ∀ (V : S.affineOpens) (f : Γ(S, V)),
        (γ V).IsDPMorphism (γ (S.affineBasicOpen f))
          (S.presheaf.map (homOfLE (S.basicOpen_le f)).op).hom}
    {X : Scheme.{u}} {x₀ : X ⟶ I.subscheme}
    (T : smallCrystallineSite S I γ h_compatible X x₀)
    (V : (scheme T).affineOpens) :
    Module Γ(T.obj.1.thickening, (baseAffineOpen T V).1)
      ((Ω[T.obj.1.thickeningToBase.toShHom]).val.obj (Opposite.op (baseAffineOpen T V).1)) :=
  (Ω[T.obj.1.thickeningToBase.toShHom]).val.obj
    (Opposite.op (baseAffineOpen T V).1) |>.isModule

/-- `differentialModule` is the `ModuleCat` action on affine differentials. -/
theorem differentialModule_eq
    {S : Scheme.{u}} {I : S.IdealSheafData}
    {γ : ∀ V : S.affineOpens, DividedPowers (I.ideal V)}
    {h_compatible :
      ∀ (V : S.affineOpens) (f : Γ(S, V)),
        (γ V).IsDPMorphism (γ (S.affineBasicOpen f))
          (S.presheaf.map (homOfLE (S.basicOpen_le f)).op).hom}
    {X : Scheme.{u}} {x₀ : X ⟶ I.subscheme}
    (T : smallCrystallineSite S I γ h_compatible X x₀)
    (V : (scheme T).affineOpens) :
    differentialModule T V =
      ((Ω[T.obj.1.thickeningToBase.toShHom]).val.obj
        (Opposite.op (baseAffineOpen T V).1)).isModule := sorry

/-- Scalar multiplication of affine differentials by functions of `T`. -/
def formSMul
    {S : Scheme.{u}} {I : S.IdealSheafData}
    {γ : ∀ V : S.affineOpens, DividedPowers (I.ideal V)}
    {h_compatible :
      ∀ (V : S.affineOpens) (f : Γ(S, V)),
        (γ V).IsDPMorphism (γ (S.affineBasicOpen f))
          (S.presheaf.map (homOfLE (S.basicOpen_le f)).op).hom}
    {X : Scheme.{u}} {x₀ : X ⟶ I.subscheme}
    (T : smallCrystallineSite S I γ h_compatible X x₀)
    (V : (scheme T).affineOpens)
    (r : Γ(T.obj.1.thickening, (baseAffineOpen T V).1))
    (ω : (Ω[T.obj.1.thickeningToBase.toShHom]).val.obj
      (Opposite.op (baseAffineOpen T V).1)) :
    (Ω[T.obj.1.thickeningToBase.toShHom]).val.obj
      (Opposite.op (baseAffineOpen T V).1) :=
  SMul.smul (self := (differentialModule T V).toSMul) r ω

/-- `formSMul` is the `Ω[T/S]`-module action. -/
theorem formSMul_apply
    {S : Scheme.{u}} {I : S.IdealSheafData}
    {γ : ∀ V : S.affineOpens, DividedPowers (I.ideal V)}
    {h_compatible :
      ∀ (V : S.affineOpens) (f : Γ(S, V)),
        (γ V).IsDPMorphism (γ (S.affineBasicOpen f))
          (S.presheaf.map (homOfLE (S.basicOpen_le f)).op).hom}
    {X : Scheme.{u}} {x₀ : X ⟶ I.subscheme}
    (T : smallCrystallineSite S I γ h_compatible X x₀)
    (V : (scheme T).affineOpens)
    (r : Γ(T.obj.1.thickening, (baseAffineOpen T V).1))
    (ω : (Ω[T.obj.1.thickeningToBase.toShHom]).val.obj
      (Opposite.op (baseAffineOpen T V).1)) :
    formSMul T V r ω =
      SMul.smul (self := (differentialModule T V).toSMul) r ω := sorry

/-- The wedge of two affine 1-forms as a 2-form of `T/S`. -/
def formWedge
    {S : Scheme.{u}} {I : S.IdealSheafData}
    {γ : ∀ V : S.affineOpens, DividedPowers (I.ideal V)}
    {h_compatible :
      ∀ (V : S.affineOpens) (f : Γ(S, V)),
        (γ V).IsDPMorphism (γ (S.affineBasicOpen f))
          (S.presheaf.map (homOfLE (S.basicOpen_le f)).op).hom}
    {X : Scheme.{u}} {x₀ : X ⟶ I.subscheme}
    (T : smallCrystallineSite S I γ h_compatible X x₀)
    (V : (scheme T).affineOpens)
    (x y : (Ω[T.obj.1.thickeningToBase.toShHom]).val.obj
      (Opposite.op (baseAffineOpen T V).1)) :=
  @wedge (Γ(T.obj.1.thickening, (baseAffineOpen T V).1)) _
    ((Ω[T.obj.1.thickeningToBase.toShHom]).val.obj
      (Opposite.op (baseAffineOpen T V).1)) _ (differentialModule T V) x y

/-- `formWedge` is the source exterior product of 1-forms. -/
theorem formWedge_apply
    {S : Scheme.{u}} {I : S.IdealSheafData}
    {γ : ∀ V : S.affineOpens, DividedPowers (I.ideal V)}
    {h_compatible :
      ∀ (V : S.affineOpens) (f : Γ(S, V)),
        (γ V).IsDPMorphism (γ (S.affineBasicOpen f))
          (S.presheaf.map (homOfLE (S.basicOpen_le f)).op).hom}
    {X : Scheme.{u}} {x₀ : X ⟶ I.subscheme}
    (T : smallCrystallineSite S I γ h_compatible X x₀)
    (V : (scheme T).affineOpens)
    (x y : (Ω[T.obj.1.thickeningToBase.toShHom]).val.obj
      (Opposite.op (baseAffineOpen T V).1)) :
    formWedge T V x y =
      @wedge (Γ(T.obj.1.thickening, (baseAffineOpen T V).1)) _
        ((Ω[T.obj.1.thickeningToBase.toShHom]).val.obj
          (Opposite.op (baseAffineOpen T V).1)) _ (differentialModule T V) x y := sorry

/-- The first-coordinate projection as a ring homomorphism on affine sections. -/
def projectionHom
    {S : Scheme.{u}} {I : S.IdealSheafData}
    {γ : ∀ V : S.affineOpens, DividedPowers (I.ideal V)}
    {h_compatible :
      ∀ (V : S.affineOpens) (f : Γ(S, V)),
        (γ V).IsDPMorphism (γ (S.affineBasicOpen f))
          (S.presheaf.map (homOfLE (S.basicOpen_le f)).op).hom}
    {X : Scheme.{u}} {x₀ : X ⟶ I.subscheme}
    (T : smallCrystallineSite S I γ h_compatible X x₀)
    (V : (scheme T).affineOpens) :
    Γ(scheme T, V) →+* Γ(T.obj.1.thickening, baseAffineOpen T V) :=
  (projectionApp T (Opposite.op V.1)).hom

/-- The affine-section ideal `J''` as the inverse image of `J`. -/
def idealFamily
    {S : Scheme.{u}} {I : S.IdealSheafData}
    {γ : ∀ V : S.affineOpens, DividedPowers (I.ideal V)}
    {h_compatible :
      ∀ (V : S.affineOpens) (f : Γ(S, V)),
        (γ V).IsDPMorphism (γ (S.affineBasicOpen f))
          (S.presheaf.map (homOfLE (S.basicOpen_le f)).op).hom}
    {X : Scheme.{u}} {x₀ : X ⟶ I.subscheme}
    (T : smallCrystallineSite S I γ h_compatible X x₀)
    (V : (scheme T).affineOpens) :
    Ideal Γ(scheme T, V) :=
  (T.obj.1.ideal.ideal (baseAffineOpen T V)).comap (projectionHom T V)

/-- Localization compatibility for `J''`. -/
theorem idealFamily_map_basicOpen
    {S : Scheme.{u}} {I : S.IdealSheafData}
    {γ : ∀ V : S.affineOpens, DividedPowers (I.ideal V)}
    {h_compatible :
      ∀ (V : S.affineOpens) (f : Γ(S, V)),
        (γ V).IsDPMorphism (γ (S.affineBasicOpen f))
          (S.presheaf.map (homOfLE (S.basicOpen_le f)).op).hom}
    {X : Scheme.{u}} {x₀ : X ⟶ I.subscheme}
    (T : smallCrystallineSite S I γ h_compatible X x₀)
    (V : (scheme T).affineOpens)
    (f : Γ(scheme T, V)) :
    (idealFamily T V).map
        ((scheme T).presheaf.map (homOfLE ((scheme T).basicOpen_le f)).op).hom =
      idealFamily T ((scheme T).affineBasicOpen f) := sorry

/-- The ideal sheaf `J''` on `T''`. -/
def ideal
    {S : Scheme.{u}} {I : S.IdealSheafData}
    {γ : ∀ V : S.affineOpens, DividedPowers (I.ideal V)}
    {h_compatible :
      ∀ (V : S.affineOpens) (f : Γ(S, V)),
        (γ V).IsDPMorphism (γ (S.affineBasicOpen f))
          (S.presheaf.map (homOfLE (S.basicOpen_le f)).op).hom}
    {X : Scheme.{u}} {x₀ : X ⟶ I.subscheme}
    (T : smallCrystallineSite S I γ h_compatible X x₀) :
    (scheme T).IdealSheafData where
  ideal := idealFamily T
  map_ideal_basicOpen := idealFamily_map_basicOpen T

/-- Membership in `J''` is first-coordinate membership in `J`. -/
theorem ideal_spec
    {S : Scheme.{u}} {I : S.IdealSheafData}
    {γ : ∀ V : S.affineOpens, DividedPowers (I.ideal V)}
    {h_compatible :
      ∀ (V : S.affineOpens) (f : Γ(S, V)),
        (γ V).IsDPMorphism (γ (S.affineBasicOpen f))
          (S.presheaf.map (homOfLE (S.basicOpen_le f)).op).hom}
    {X : Scheme.{u}} {x₀ : X ⟶ I.subscheme}
    (T : smallCrystallineSite S I γ h_compatible X x₀)
    (V : (scheme T).affineOpens)
    (z : affineSection T V) :
    z ∈ (ideal T).ideal V ↔
      z.1 ∈ T.obj.1.ideal.ideal (baseAffineOpen T V) := sorry

/-- Affine 2-forms of `T/S`. -/
abbrev twoForm
    {S : Scheme.{u}} {I : S.IdealSheafData}
    {γ : ∀ V : S.affineOpens, DividedPowers (I.ideal V)}
    {h_compatible :
      ∀ (V : S.affineOpens) (f : Γ(S, V)),
        (γ V).IsDPMorphism (γ (S.affineBasicOpen f))
          (S.presheaf.map (homOfLE (S.basicOpen_le f)).op).hom}
    {X : Scheme.{u}} {x₀ : X ⟶ I.subscheme}
    (T : smallCrystallineSite S I γ h_compatible X x₀)
    (V : (scheme T).affineOpens) : Type u :=
  ⋀[Γ(T.obj.1.thickening, (baseAffineOpen T V).1)]^2
    ((Ω[T.obj.1.thickeningToBase.toShHom]).val.obj
      (Opposite.op (baseAffineOpen T V).1))

/-- The canonical module structure of `⋀²Ω[T/S]` on a second-order affine open. -/
abbrev twoFormModule
    {S : Scheme.{u}} {I : S.IdealSheafData}
    {γ : ∀ V : S.affineOpens, DividedPowers (I.ideal V)}
    {h_compatible :
      ∀ (V : S.affineOpens) (f : Γ(S, V)),
        (γ V).IsDPMorphism (γ (S.affineBasicOpen f))
          (S.presheaf.map (homOfLE (S.basicOpen_le f)).op).hom}
    {X : Scheme.{u}} {x₀ : X ⟶ I.subscheme}
    (T : smallCrystallineSite S I γ h_compatible X x₀)
    (V : (scheme T).affineOpens) :
    Module Γ(T.obj.1.thickening, (baseAffineOpen T V).1) (twoForm T V) :=
  (inferInstance : Module Γ(T.obj.1.thickening, (baseAffineOpen T V).1) (twoForm T V))

/-- `twoFormModule` is the exterior-power module action. -/
theorem twoFormModule_eq
    {S : Scheme.{u}} {I : S.IdealSheafData}
    {γ : ∀ V : S.affineOpens, DividedPowers (I.ideal V)}
    {h_compatible :
      ∀ (V : S.affineOpens) (f : Γ(S, V)),
        (γ V).IsDPMorphism (γ (S.affineBasicOpen f))
          (S.presheaf.map (homOfLE (S.basicOpen_le f)).op).hom}
    {X : Scheme.{u}} {x₀ : X ⟶ I.subscheme}
    (T : smallCrystallineSite S I γ h_compatible X x₀)
    (V : (scheme T).affineOpens) :
    twoFormModule T V =
      (inferInstance : Module Γ(T.obj.1.thickening, (baseAffineOpen T V).1)
        (twoForm T V)) := sorry

/-- Scalar multiplication of affine 2-forms by functions of `T`. -/
def formTwoSMul
    {S : Scheme.{u}} {I : S.IdealSheafData}
    {γ : ∀ V : S.affineOpens, DividedPowers (I.ideal V)}
    {h_compatible :
      ∀ (V : S.affineOpens) (f : Γ(S, V)),
        (γ V).IsDPMorphism (γ (S.affineBasicOpen f))
          (S.presheaf.map (homOfLE (S.basicOpen_le f)).op).hom}
    {X : Scheme.{u}} {x₀ : X ⟶ I.subscheme}
    (T : smallCrystallineSite S I γ h_compatible X x₀)
    (V : (scheme T).affineOpens)
    (r : Γ(T.obj.1.thickening, (baseAffineOpen T V).1))
    (η : twoForm T V) : twoForm T V :=
  SMul.smul (self := (twoFormModule T V).toSMul) r η

/-- `formTwoSMul` is the `⋀²Ω[T/S]`-module action. -/
theorem formTwoSMul_apply
    {S : Scheme.{u}} {I : S.IdealSheafData}
    {γ : ∀ V : S.affineOpens, DividedPowers (I.ideal V)}
    {h_compatible :
      ∀ (V : S.affineOpens) (f : Γ(S, V)),
        (γ V).IsDPMorphism (γ (S.affineBasicOpen f))
          (S.presheaf.map (homOfLE (S.basicOpen_le f)).op).hom}
    {X : Scheme.{u}} {x₀ : X ⟶ I.subscheme}
    (T : smallCrystallineSite S I γ h_compatible X x₀)
    (V : (scheme T).affineOpens)
    (r : Γ(T.obj.1.thickening, (baseAffineOpen T V).1))
    (η : twoForm T V) :
    formTwoSMul T V r η =
      SMul.smul (self := (twoFormModule T V).toSMul) r η := sorry

/-- First coordinate `δ_n(f)` of the source 4-tuple. -/
def dpowTupleFst
    {S : Scheme.{u}} {I : S.IdealSheafData}
    {γ : ∀ V : S.affineOpens, DividedPowers (I.ideal V)}
    {h_compatible :
      ∀ (V : S.affineOpens) (f : Γ(S, V)),
        (γ V).IsDPMorphism (γ (S.affineBasicOpen f))
          (S.presheaf.map (homOfLE (S.basicOpen_le f)).op).hom}
    {X : Scheme.{u}} {x₀ : X ⟶ I.subscheme}
    (T : smallCrystallineSite S I γ h_compatible X x₀)
    (V : (scheme T).affineOpens) (n : ℕ)
    (z : affineSection T V) :
    Γ(T.obj.1.thickening, (baseAffineOpen T V).1) :=
  (T.obj.1.gamma (baseAffineOpen T V)).dpow n z.1

/-- Second coordinate `δ_{n-1}(f) • ω₁` of the source 4-tuple. -/
def dpowTupleOmega1
    {S : Scheme.{u}} {I : S.IdealSheafData}
    {γ : ∀ V : S.affineOpens, DividedPowers (I.ideal V)}
    {h_compatible :
      ∀ (V : S.affineOpens) (f : Γ(S, V)),
        (γ V).IsDPMorphism (γ (S.affineBasicOpen f))
          (S.presheaf.map (homOfLE (S.basicOpen_le f)).op).hom}
    {X : Scheme.{u}} {x₀ : X ⟶ I.subscheme}
    (T : smallCrystallineSite S I γ h_compatible X x₀)
    (V : (scheme T).affineOpens) (n : ℕ)
    (z : affineSection T V) :
    (Ω[T.obj.1.thickeningToBase.toShHom]).val.obj
      (Opposite.op (baseAffineOpen T V).1) :=
  formSMul T V
    (DividedPowers.BilinearExtension.dpowPred
      (T.obj.1.gamma (baseAffineOpen T V)) n z.1) z.2.1

/-- Third coordinate `δ_{n-1}(f) • ω₂` of the source 4-tuple. -/
def dpowTupleOmega2
    {S : Scheme.{u}} {I : S.IdealSheafData}
    {γ : ∀ V : S.affineOpens, DividedPowers (I.ideal V)}
    {h_compatible :
      ∀ (V : S.affineOpens) (f : Γ(S, V)),
        (γ V).IsDPMorphism (γ (S.affineBasicOpen f))
          (S.presheaf.map (homOfLE (S.basicOpen_le f)).op).hom}
    {X : Scheme.{u}} {x₀ : X ⟶ I.subscheme}
    (T : smallCrystallineSite S I γ h_compatible X x₀)
    (V : (scheme T).affineOpens) (n : ℕ)
    (z : affineSection T V) :
    (Ω[T.obj.1.thickeningToBase.toShHom]).val.obj
      (Opposite.op (baseAffineOpen T V).1) :=
  formSMul T V
    (DividedPowers.BilinearExtension.dpowPred
      (T.obj.1.gamma (baseAffineOpen T V)) n z.1) z.2.2.1

/-- Addition on affine 2-forms of `T/S`. -/
abbrev twoFormAdd
    {S : Scheme.{u}} {I : S.IdealSheafData}
    {γ : ∀ V : S.affineOpens, DividedPowers (I.ideal V)}
    {h_compatible :
      ∀ (V : S.affineOpens) (f : Γ(S, V)),
        (γ V).IsDPMorphism (γ (S.affineBasicOpen f))
          (S.presheaf.map (homOfLE (S.basicOpen_le f)).op).hom}
    {X : Scheme.{u}} {x₀ : X ⟶ I.subscheme}
    (T : smallCrystallineSite S I γ h_compatible X x₀)
    (V : (scheme T).affineOpens) : Add (twoForm T V) :=
  (inferInstance : Add (twoForm T V))

/-- `twoFormAdd` is the additive structure of `twoFormModule`. -/
theorem twoFormAdd_eq
    {S : Scheme.{u}} {I : S.IdealSheafData}
    {γ : ∀ V : S.affineOpens, DividedPowers (I.ideal V)}
    {h_compatible :
      ∀ (V : S.affineOpens) (f : Γ(S, V)),
        (γ V).IsDPMorphism (γ (S.affineBasicOpen f))
          (S.presheaf.map (homOfLE (S.basicOpen_le f)).op).hom}
    {X : Scheme.{u}} {x₀ : X ⟶ I.subscheme}
    (T : smallCrystallineSite S I γ h_compatible X x₀)
    (V : (scheme T).affineOpens) :
    twoFormAdd T V = (inferInstance : Add (twoForm T V)) := sorry

/-- The first 1-form coordinate of a 4-tuple section. -/
def sectionOmega1
    {S : Scheme.{u}} {I : S.IdealSheafData}
    {γ : ∀ V : S.affineOpens, DividedPowers (I.ideal V)}
    {h_compatible :
      ∀ (V : S.affineOpens) (f : Γ(S, V)),
        (γ V).IsDPMorphism (γ (S.affineBasicOpen f))
          (S.presheaf.map (homOfLE (S.basicOpen_le f)).op).hom}
    {X : Scheme.{u}} {x₀ : X ⟶ I.subscheme}
    (T : smallCrystallineSite S I γ h_compatible X x₀)
    (V : (scheme T).affineOpens)
    (z : affineSection T V) :
    (Ω[T.obj.1.thickeningToBase.toShHom]).val.obj
      (Opposite.op (baseAffineOpen T V).1) :=
  z.2.1

/-- The second 1-form coordinate of a 4-tuple section. -/
def sectionOmega2
    {S : Scheme.{u}} {I : S.IdealSheafData}
    {γ : ∀ V : S.affineOpens, DividedPowers (I.ideal V)}
    {h_compatible :
      ∀ (V : S.affineOpens) (f : Γ(S, V)),
        (γ V).IsDPMorphism (γ (S.affineBasicOpen f))
          (S.presheaf.map (homOfLE (S.basicOpen_le f)).op).hom}
    {X : Scheme.{u}} {x₀ : X ⟶ I.subscheme}
    (T : smallCrystallineSite S I γ h_compatible X x₀)
    (V : (scheme T).affineOpens)
    (z : affineSection T V) :
    (Ω[T.obj.1.thickeningToBase.toShHom]).val.obj
      (Opposite.op (baseAffineOpen T V).1) :=
  z.2.2.1

/-- The 2-form coordinate of a 4-tuple section. -/
def sectionTwoForm
    {S : Scheme.{u}} {I : S.IdealSheafData}
    {γ : ∀ V : S.affineOpens, DividedPowers (I.ideal V)}
    {h_compatible :
      ∀ (V : S.affineOpens) (f : Γ(S, V)),
        (γ V).IsDPMorphism (γ (S.affineBasicOpen f))
          (S.presheaf.map (homOfLE (S.basicOpen_le f)).op).hom}
    {X : Scheme.{u}} {x₀ : X ⟶ I.subscheme}
    (T : smallCrystallineSite S I γ h_compatible X x₀)
    (V : (scheme T).affineOpens)
    (z : affineSection T V) :=
  z.2.2.2

/-- `sectionOmega1` is the second 4-tuple coordinate. -/
theorem sectionOmega1_eq
    {S : Scheme.{u}} {I : S.IdealSheafData}
    {γ : ∀ V : S.affineOpens, DividedPowers (I.ideal V)}
    {h_compatible :
      ∀ (V : S.affineOpens) (f : Γ(S, V)),
        (γ V).IsDPMorphism (γ (S.affineBasicOpen f))
          (S.presheaf.map (homOfLE (S.basicOpen_le f)).op).hom}
    {X : Scheme.{u}} {x₀ : X ⟶ I.subscheme}
    (T : smallCrystallineSite S I γ h_compatible X x₀)
    (V : (scheme T).affineOpens)
    (z : affineSection T V) :
    sectionOmega1 T V z = z.2.1 := sorry

/-- `sectionOmega2` is the third 4-tuple coordinate. -/
theorem sectionOmega2_eq
    {S : Scheme.{u}} {I : S.IdealSheafData}
    {γ : ∀ V : S.affineOpens, DividedPowers (I.ideal V)}
    {h_compatible :
      ∀ (V : S.affineOpens) (f : Γ(S, V)),
        (γ V).IsDPMorphism (γ (S.affineBasicOpen f))
          (S.presheaf.map (homOfLE (S.basicOpen_le f)).op).hom}
    {X : Scheme.{u}} {x₀ : X ⟶ I.subscheme}
    (T : smallCrystallineSite S I γ h_compatible X x₀)
    (V : (scheme T).affineOpens)
    (z : affineSection T V) :
    sectionOmega2 T V z = z.2.2.1 := sorry

/-- `sectionTwoForm` is the fourth 4-tuple coordinate. -/
theorem sectionTwoForm_eq
    {S : Scheme.{u}} {I : S.IdealSheafData}
    {γ : ∀ V : S.affineOpens, DividedPowers (I.ideal V)}
    {h_compatible :
      ∀ (V : S.affineOpens) (f : Γ(S, V)),
        (γ V).IsDPMorphism (γ (S.affineBasicOpen f))
          (S.presheaf.map (homOfLE (S.basicOpen_le f)).op).hom}
    {X : Scheme.{u}} {x₀ : X ⟶ I.subscheme}
    (T : smallCrystallineSite S I γ h_compatible X x₀)
    (V : (scheme T).affineOpens)
    (z : affineSection T V) :
    sectionTwoForm T V z = z.2.2.2 := sorry

/-- The source 2-form `ω₁ ∧ ω₂` in the divided-power 4-tuple. -/
def dpowTupleWedge
    {S : Scheme.{u}} {I : S.IdealSheafData}
    {γ : ∀ V : S.affineOpens, DividedPowers (I.ideal V)}
    {h_compatible :
      ∀ (V : S.affineOpens) (f : Γ(S, V)),
        (γ V).IsDPMorphism (γ (S.affineBasicOpen f))
          (S.presheaf.map (homOfLE (S.basicOpen_le f)).op).hom}
    {X : Scheme.{u}} {x₀ : X ⟶ I.subscheme}
    (T : smallCrystallineSite S I γ h_compatible X x₀)
    (V : (scheme T).affineOpens)
    (z : affineSection T V) :=
  formWedge T V (sectionOmega1 T V z) (sectionOmega2 T V z)

/-- The summand `δ_{n-1}(f) • η`. -/
def dpowTupleTwoPred
    {S : Scheme.{u}} {I : S.IdealSheafData}
    {γ : ∀ V : S.affineOpens, DividedPowers (I.ideal V)}
    {h_compatible :
      ∀ (V : S.affineOpens) (f : Γ(S, V)),
        (γ V).IsDPMorphism (γ (S.affineBasicOpen f))
          (S.presheaf.map (homOfLE (S.basicOpen_le f)).op).hom}
    {X : Scheme.{u}} {x₀ : X ⟶ I.subscheme}
    (T : smallCrystallineSite S I γ h_compatible X x₀)
    (V : (scheme T).affineOpens) (n : ℕ)
    (z : affineSection T V) : twoForm T V :=
  formTwoSMul T V
    (DividedPowers.BilinearExtension.dpowPred
      (T.obj.1.gamma (baseAffineOpen T V)) n z.1) (sectionTwoForm T V z)

/-- The summand `δ_{n-2}(f) • ω₁ ∧ ω₂`. -/
def dpowTupleTwoPredTwo
    {S : Scheme.{u}} {I : S.IdealSheafData}
    {γ : ∀ V : S.affineOpens, DividedPowers (I.ideal V)}
    {h_compatible :
      ∀ (V : S.affineOpens) (f : Γ(S, V)),
        (γ V).IsDPMorphism (γ (S.affineBasicOpen f))
          (S.presheaf.map (homOfLE (S.basicOpen_le f)).op).hom}
    {X : Scheme.{u}} {x₀ : X ⟶ I.subscheme}
    (T : smallCrystallineSite S I γ h_compatible X x₀)
    (V : (scheme T).affineOpens) (n : ℕ)
    (z : affineSection T V) : twoForm T V :=
  formTwoSMul T V
    (DividedPowers.BilinearExtension.dpowPredTwo
      (T.obj.1.gamma (baseAffineOpen T V)) n z.1)
    (dpowTupleWedge T V z)

/-- Fourth coordinate `δ_{n-1}(f) • η + δ_{n-2}(f) • ω₁ ∧ ω₂`. -/
def dpowTupleTwo
    {S : Scheme.{u}} {I : S.IdealSheafData}
    {γ : ∀ V : S.affineOpens, DividedPowers (I.ideal V)}
    {h_compatible :
      ∀ (V : S.affineOpens) (f : Γ(S, V)),
        (γ V).IsDPMorphism (γ (S.affineBasicOpen f))
          (S.presheaf.map (homOfLE (S.basicOpen_le f)).op).hom}
    {X : Scheme.{u}} {x₀ : X ⟶ I.subscheme}
    (T : smallCrystallineSite S I γ h_compatible X x₀)
    (V : (scheme T).affineOpens) (n : ℕ)
    (z : affineSection T V) : twoForm T V :=
  Add.add (self := twoFormAdd T V)
    (dpowTupleTwoPred T V n z) (dpowTupleTwoPredTwo T V n z)

/-- The source 4-tuple `δ''_n(f, ω₁, ω₂, η)` before the membership cutoff. -/
def dpowTuple
    {S : Scheme.{u}} {I : S.IdealSheafData}
    {γ : ∀ V : S.affineOpens, DividedPowers (I.ideal V)}
    {h_compatible :
      ∀ (V : S.affineOpens) (f : Γ(S, V)),
        (γ V).IsDPMorphism (γ (S.affineBasicOpen f))
          (S.presheaf.map (homOfLE (S.basicOpen_le f)).op).hom}
    {X : Scheme.{u}} {x₀ : X ⟶ I.subscheme}
    (T : smallCrystallineSite S I γ h_compatible X x₀)
    (V : (scheme T).affineOpens) (n : ℕ)
    (z : affineSection T V) : affineSection T V :=
  (dpowTupleFst T V n z, dpowTupleOmega1 T V n z, dpowTupleOmega2 T V n z,
    dpowTupleTwo T V n z)

/-- The first coordinate of `dpowTuple` is the divided power of `T`. -/
theorem dpowTuple_fst
    {S : Scheme.{u}} {I : S.IdealSheafData}
    {γ : ∀ V : S.affineOpens, DividedPowers (I.ideal V)}
    {h_compatible :
      ∀ (V : S.affineOpens) (f : Γ(S, V)),
        (γ V).IsDPMorphism (γ (S.affineBasicOpen f))
          (S.presheaf.map (homOfLE (S.basicOpen_le f)).op).hom}
    {X : Scheme.{u}} {x₀ : X ⟶ I.subscheme}
    (T : smallCrystallineSite S I γ h_compatible X x₀)
    (V : (scheme T).affineOpens) (n : ℕ) (z : affineSection T V) :
    (dpowTuple T V n z).1 = (T.obj.1.gamma (baseAffineOpen T V)).dpow n z.1 := sorry

/-- The source divided-power operations on `J''`. -/
noncomputable def dividedPowers
    {S : Scheme.{u}} {I : S.IdealSheafData}
    {γ : ∀ V : S.affineOpens, DividedPowers (I.ideal V)}
    {h_compatible :
      ∀ (V : S.affineOpens) (f : Γ(S, V)),
        (γ V).IsDPMorphism (γ (S.affineBasicOpen f))
          (S.presheaf.map (homOfLE (S.basicOpen_le f)).op).hom}
    {X : Scheme.{u}} {x₀ : X ⟶ I.subscheme}
    (T : smallCrystallineSite S I γ h_compatible X x₀)
    (V : (scheme T).affineOpens) :
    DividedPowers ((ideal T).ideal V) := by
  classical
  refine {
    dpow := fun n a =>
      if h : a ∈ (ideal T).ideal V then
        dpowTuple T V n a
      else 0
    dpow_null := by sorry
    dpow_zero := by sorry
    dpow_one := by sorry
    dpow_mem := by sorry
    dpow_add := by sorry
    dpow_mul := by sorry
    mul_dpow := by sorry
    dpow_comp := by sorry
  }

/-- The coordinate `δ_{n-1}(f) • ω` in the second-order divided powers. -/
def dpowPredSMul
    {S : Scheme.{u}} {I : S.IdealSheafData}
    {γ : ∀ V : S.affineOpens, DividedPowers (I.ideal V)}
    {h_compatible :
      ∀ (V : S.affineOpens) (f : Γ(S, V)),
        (γ V).IsDPMorphism (γ (S.affineBasicOpen f))
          (S.presheaf.map (homOfLE (S.basicOpen_le f)).op).hom}
    {X : Scheme.{u}} {x₀ : X ⟶ I.subscheme}
    (T : smallCrystallineSite S I γ h_compatible X x₀)
    (V : (scheme T).affineOpens) (n : ℕ)
    (f : Γ(T.obj.1.thickening, baseAffineOpen T V))
    (ω : (Ω[T.obj.1.thickeningToBase.toShHom]).val.obj
      (Opposite.op (baseAffineOpen T V).1)) :
    (Ω[T.obj.1.thickeningToBase.toShHom]).val.obj
      (Opposite.op (baseAffineOpen T V).1) :=
  (dpowTuple T V n (f, ω, 0, 0)).2.1

/-- The source formula
`δ''_n(f, ω₁, ω₂, η) = (δ_n(f), δ_{n-1}(f) • ω₁, δ_{n-1}(f) • ω₂,
δ_{n-1}(f) • η + δ_{n-2}(f) • ω₁ ∧ ω₂)`. -/
theorem dividedPowers_apply
    {S : Scheme.{u}} {I : S.IdealSheafData}
    {γ : ∀ V : S.affineOpens, DividedPowers (I.ideal V)}
    {h_compatible :
      ∀ (V : S.affineOpens) (f : Γ(S, V)),
        (γ V).IsDPMorphism (γ (S.affineBasicOpen f))
          (S.presheaf.map (homOfLE (S.basicOpen_le f)).op).hom}
    {X : Scheme.{u}} {x₀ : X ⟶ I.subscheme}
    (T : smallCrystallineSite S I γ h_compatible X x₀)
    (V : (scheme T).affineOpens) (n : ℕ)
    (z : (ideal T).ideal V) :
    (dividedPowers T V).dpow n z.1 = dpowTuple T V n z.1 := sorry

/-- Divided powers on `J''` commute with restriction to affine basic opens. -/
theorem dividedPowers_compatible
    {S : Scheme.{u}} {I : S.IdealSheafData}
    {γ : ∀ V : S.affineOpens, DividedPowers (I.ideal V)}
    {h_compatible :
      ∀ (V : S.affineOpens) (f : Γ(S, V)),
        (γ V).IsDPMorphism (γ (S.affineBasicOpen f))
          (S.presheaf.map (homOfLE (S.basicOpen_le f)).op).hom}
    {X : Scheme.{u}} {x₀ : X ⟶ I.subscheme}
    (T : smallCrystallineSite S I γ h_compatible X x₀) :
    ∀ (V : (scheme T).affineOpens) (f : Γ(scheme T, V)),
      (dividedPowers T V).IsDPMorphism
        (dividedPowers T ((scheme T).affineBasicOpen f))
        ((scheme T).presheaf.map (homOfLE ((scheme T).basicOpen_le f)).op).hom := sorry

/-- `J''` defines a divided-power thickening. -/
theorem isDividedPowerThickening
    {S : Scheme.{u}} {I : S.IdealSheafData}
    {γ : ∀ V : S.affineOpens, DividedPowers (I.ideal V)}
    {h_compatible :
      ∀ (V : S.affineOpens) (f : Γ(S, V)),
        (γ V).IsDPMorphism (γ (S.affineBasicOpen f))
          (S.presheaf.map (homOfLE (S.basicOpen_le f)).op).hom}
    {X : Scheme.{u}} {x₀ : X ⟶ I.subscheme}
    (T : smallCrystallineSite S I γ h_compatible X x₀) :
    IsDividedPowerThickening (scheme T) (ideal T)
      (dividedPowers T) (dividedPowers_compatible T) := sorry

/-- The section map `q₀(f) = (f, 0, 0, 0)`. -/
def q0Fun
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
  fun f ↦ (f, 0, 0, 0)

/-- The section map `q₁(f) = (f, d f, 0, 0)`. -/
def q1Fun
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
  fun f ↦ (f, (d[T.obj.1.thickeningToBase.toShHom]).d f, 0, 0)

/-- The section map `q₂(f) = (f, d f, d f, 0)`. -/
def q2Fun
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
  fun f ↦
    (f, (d[T.obj.1.thickeningToBase.toShHom]).d f,
      (d[T.obj.1.thickeningToBase.toShHom]).d f, 0)

/-- The section map `q₀₁(f, ω) = (f, ω, 0, 0)`. -/
def q01Fun
    {S : Scheme.{u}} {I : S.IdealSheafData}
    {γ : ∀ V : S.affineOpens, DividedPowers (I.ideal V)}
    {h_compatible :
      ∀ (V : S.affineOpens) (f : Γ(S, V)),
        (γ V).IsDPMorphism (γ (S.affineBasicOpen f))
          (S.presheaf.map (homOfLE (S.basicOpen_le f)).op).hom}
    {X : Scheme.{u}} {x₀ : X ⟶ I.subscheme}
    (T : smallCrystallineSite S I γ h_compatible X x₀)
    (V : (Opens T.obj.1.thickening.toTopCat)ᵒᵖ) :
    FirstOrderThickening.ring (T.obj.1.thickening.presheaf.obj V)
        ((Ω[T.obj.1.thickeningToBase.toShHom]).val.obj V) →
      ring (T.obj.1.thickening.presheaf.obj V)
        ((Ω[T.obj.1.thickeningToBase.toShHom]).val.obj V) :=
  fun z ↦ (z.1, z.2, 0, 0)

/-- The section map `q₁₂(f, ω) = (f, d f, ω, d ω)`. -/
def q12Fun
    {S : Scheme.{u}} {I : S.IdealSheafData}
    {γ : ∀ V : S.affineOpens, DividedPowers (I.ideal V)}
    {h_compatible :
      ∀ (V : S.affineOpens) (f : Γ(S, V)),
        (γ V).IsDPMorphism (γ (S.affineBasicOpen f))
          (S.presheaf.map (homOfLE (S.basicOpen_le f)).op).hom}
    {X : Scheme.{u}} {x₀ : X ⟶ I.subscheme}
    (T : smallCrystallineSite S I γ h_compatible X x₀)
    (V : (Opens T.obj.1.thickening.toTopCat)ᵒᵖ) :
    FirstOrderThickening.ring (T.obj.1.thickening.presheaf.obj V)
        ((Ω[T.obj.1.thickeningToBase.toShHom]).val.obj V) →
      ring (T.obj.1.thickening.presheaf.obj V)
        ((Ω[T.obj.1.thickeningToBase.toShHom]).val.obj V) :=
  fun z ↦
    (z.1, (d[T.obj.1.thickeningToBase.toShHom]).d z.1, z.2,
      dΩ (d[T.obj.1.thickeningToBase.toShHom]).d z.2)

/-- The section map `q₀₂(f, ω) = (f, ω, ω, 0)`. -/
def q02Fun
    {S : Scheme.{u}} {I : S.IdealSheafData}
    {γ : ∀ V : S.affineOpens, DividedPowers (I.ideal V)}
    {h_compatible :
      ∀ (V : S.affineOpens) (f : Γ(S, V)),
        (γ V).IsDPMorphism (γ (S.affineBasicOpen f))
          (S.presheaf.map (homOfLE (S.basicOpen_le f)).op).hom}
    {X : Scheme.{u}} {x₀ : X ⟶ I.subscheme}
    (T : smallCrystallineSite S I γ h_compatible X x₀)
    (V : (Opens T.obj.1.thickening.toTopCat)ᵒᵖ) :
    FirstOrderThickening.ring (T.obj.1.thickening.presheaf.obj V)
        ((Ω[T.obj.1.thickeningToBase.toShHom]).val.obj V) →
      ring (T.obj.1.thickening.presheaf.obj V)
        ((Ω[T.obj.1.thickeningToBase.toShHom]).val.obj V) :=
  fun z ↦ (z.1, z.2, z.2, 0)

/-- Ring homomorphism component of `q₀`. -/
def q0App
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
  CommRingCat.ofHom
    { toFun := q0Fun T V
      map_zero' := sorry
      map_one' := sorry
      map_add' := sorry
      map_mul' := sorry }

/-- Ring homomorphism component of `q₁`. -/
def q1App
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
  CommRingCat.ofHom
    { toFun := q1Fun T V
      map_zero' := sorry
      map_one' := sorry
      map_add' := sorry
      map_mul' := sorry }

/-- Ring homomorphism component of `q₂`. -/
def q2App
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
  CommRingCat.ofHom
    { toFun := q2Fun T V
      map_zero' := sorry
      map_one' := sorry
      map_add' := sorry
      map_mul' := sorry }

/-- Ring homomorphism component of `q₀₁`. -/
def q01App
    {S : Scheme.{u}} {I : S.IdealSheafData}
    {γ : ∀ V : S.affineOpens, DividedPowers (I.ideal V)}
    {h_compatible :
      ∀ (V : S.affineOpens) (f : Γ(S, V)),
        (γ V).IsDPMorphism (γ (S.affineBasicOpen f))
          (S.presheaf.map (homOfLE (S.basicOpen_le f)).op).hom}
    {X : Scheme.{u}} {x₀ : X ⟶ I.subscheme}
    (T : smallCrystallineSite S I γ h_compatible X x₀)
    (V : (Opens T.obj.1.thickening.toTopCat)ᵒᵖ) :
    (FirstOrderThickening.sheaf T).obj.obj V ⟶ (sheaf T).obj.obj V :=
  -- Local instance justification (instance diamond): induced source opposite action.
  letI : Module (T.obj.1.thickening.presheaf.obj V)ᵐᵒᵖ
      ((Ω[T.obj.1.thickeningToBase.toShHom]).val.obj V) :=
    FirstOrderThickening.oppositeModule _ _
  -- Local instance justification (proof-local temporary data): source centrality law.
  letI : IsCentralScalar (T.obj.1.thickening.presheaf.obj V)
      ((Ω[T.obj.1.thickeningToBase.toShHom]).val.obj V) :=
    FirstOrderThickening.oppositeModule_isCentral _ _
  CommRingCat.ofHom
    { toFun := q01Fun T V
      map_zero' := sorry
      map_one' := sorry
      map_add' := sorry
      map_mul' := sorry }

/-- Ring homomorphism component of `q₁₂`. -/
def q12App
    {S : Scheme.{u}} {I : S.IdealSheafData}
    {γ : ∀ V : S.affineOpens, DividedPowers (I.ideal V)}
    {h_compatible :
      ∀ (V : S.affineOpens) (f : Γ(S, V)),
        (γ V).IsDPMorphism (γ (S.affineBasicOpen f))
          (S.presheaf.map (homOfLE (S.basicOpen_le f)).op).hom}
    {X : Scheme.{u}} {x₀ : X ⟶ I.subscheme}
    (T : smallCrystallineSite S I γ h_compatible X x₀)
    (V : (Opens T.obj.1.thickening.toTopCat)ᵒᵖ) :
    (FirstOrderThickening.sheaf T).obj.obj V ⟶ (sheaf T).obj.obj V :=
  -- Local instance justification (instance diamond): induced source opposite action.
  letI : Module (T.obj.1.thickening.presheaf.obj V)ᵐᵒᵖ
      ((Ω[T.obj.1.thickeningToBase.toShHom]).val.obj V) :=
    FirstOrderThickening.oppositeModule _ _
  -- Local instance justification (proof-local temporary data): source centrality law.
  letI : IsCentralScalar (T.obj.1.thickening.presheaf.obj V)
      ((Ω[T.obj.1.thickeningToBase.toShHom]).val.obj V) :=
    FirstOrderThickening.oppositeModule_isCentral _ _
  CommRingCat.ofHom
    { toFun := q12Fun T V
      map_zero' := sorry
      map_one' := sorry
      map_add' := sorry
      map_mul' := sorry }

/-- Ring homomorphism component of `q₀₂`. -/
def q02App
    {S : Scheme.{u}} {I : S.IdealSheafData}
    {γ : ∀ V : S.affineOpens, DividedPowers (I.ideal V)}
    {h_compatible :
      ∀ (V : S.affineOpens) (f : Γ(S, V)),
        (γ V).IsDPMorphism (γ (S.affineBasicOpen f))
          (S.presheaf.map (homOfLE (S.basicOpen_le f)).op).hom}
    {X : Scheme.{u}} {x₀ : X ⟶ I.subscheme}
    (T : smallCrystallineSite S I γ h_compatible X x₀)
    (V : (Opens T.obj.1.thickening.toTopCat)ᵒᵖ) :
    (FirstOrderThickening.sheaf T).obj.obj V ⟶ (sheaf T).obj.obj V :=
  -- Local instance justification (instance diamond): induced source opposite action.
  letI : Module (T.obj.1.thickening.presheaf.obj V)ᵐᵒᵖ
      ((Ω[T.obj.1.thickeningToBase.toShHom]).val.obj V) :=
    FirstOrderThickening.oppositeModule _ _
  -- Local instance justification (proof-local temporary data): source centrality law.
  letI : IsCentralScalar (T.obj.1.thickening.presheaf.obj V)
      ((Ω[T.obj.1.thickeningToBase.toShHom]).val.obj V) :=
    FirstOrderThickening.oppositeModule_isCentral _ _
  CommRingCat.ofHom
    { toFun := q02Fun T V
      map_zero' := sorry
      map_one' := sorry
      map_add' := sorry
      map_mul' := sorry }

/-- Naturality of `q₀`. -/
theorem q0_naturality
    {S : Scheme.{u}} {I : S.IdealSheafData}
    {γ : ∀ V : S.affineOpens, DividedPowers (I.ideal V)}
    {h_compatible :
      ∀ (V : S.affineOpens) (f : Γ(S, V)),
        (γ V).IsDPMorphism (γ (S.affineBasicOpen f))
          (S.presheaf.map (homOfLE (S.basicOpen_le f)).op).hom}
    {X : Scheme.{u}} {x₀ : X ⟶ I.subscheme}
    (T : smallCrystallineSite S I γ h_compatible X x₀)
    {U V : (Opens T.obj.1.thickening.toTopCat)ᵒᵖ} (f : U ⟶ V) :
    T.obj.1.thickening.presheaf.map f ≫ q0App T V =
      q0App T U ≫ (sheaf T).obj.map f := sorry

/-- Naturality of `q₁`. -/
theorem q1_naturality
    {S : Scheme.{u}} {I : S.IdealSheafData}
    {γ : ∀ V : S.affineOpens, DividedPowers (I.ideal V)}
    {h_compatible :
      ∀ (V : S.affineOpens) (f : Γ(S, V)),
        (γ V).IsDPMorphism (γ (S.affineBasicOpen f))
          (S.presheaf.map (homOfLE (S.basicOpen_le f)).op).hom}
    {X : Scheme.{u}} {x₀ : X ⟶ I.subscheme}
    (T : smallCrystallineSite S I γ h_compatible X x₀)
    {U V : (Opens T.obj.1.thickening.toTopCat)ᵒᵖ} (f : U ⟶ V) :
    T.obj.1.thickening.presheaf.map f ≫ q1App T V =
      q1App T U ≫ (sheaf T).obj.map f := sorry

/-- Naturality of `q₂`. -/
theorem q2_naturality
    {S : Scheme.{u}} {I : S.IdealSheafData}
    {γ : ∀ V : S.affineOpens, DividedPowers (I.ideal V)}
    {h_compatible :
      ∀ (V : S.affineOpens) (f : Γ(S, V)),
        (γ V).IsDPMorphism (γ (S.affineBasicOpen f))
          (S.presheaf.map (homOfLE (S.basicOpen_le f)).op).hom}
    {X : Scheme.{u}} {x₀ : X ⟶ I.subscheme}
    (T : smallCrystallineSite S I γ h_compatible X x₀)
    {U V : (Opens T.obj.1.thickening.toTopCat)ᵒᵖ} (f : U ⟶ V) :
    T.obj.1.thickening.presheaf.map f ≫ q2App T V =
      q2App T U ≫ (sheaf T).obj.map f := sorry

/-- Naturality of `q₀₁`. -/
theorem q01_naturality
    {S : Scheme.{u}} {I : S.IdealSheafData}
    {γ : ∀ V : S.affineOpens, DividedPowers (I.ideal V)}
    {h_compatible :
      ∀ (V : S.affineOpens) (f : Γ(S, V)),
        (γ V).IsDPMorphism (γ (S.affineBasicOpen f))
          (S.presheaf.map (homOfLE (S.basicOpen_le f)).op).hom}
    {X : Scheme.{u}} {x₀ : X ⟶ I.subscheme}
    (T : smallCrystallineSite S I γ h_compatible X x₀)
    {U V : (Opens T.obj.1.thickening.toTopCat)ᵒᵖ} (f : U ⟶ V) :
    (FirstOrderThickening.sheaf T).obj.map f ≫ q01App T V =
      q01App T U ≫ (sheaf T).obj.map f := sorry

/-- Naturality of `q₁₂`. -/
theorem q12_naturality
    {S : Scheme.{u}} {I : S.IdealSheafData}
    {γ : ∀ V : S.affineOpens, DividedPowers (I.ideal V)}
    {h_compatible :
      ∀ (V : S.affineOpens) (f : Γ(S, V)),
        (γ V).IsDPMorphism (γ (S.affineBasicOpen f))
          (S.presheaf.map (homOfLE (S.basicOpen_le f)).op).hom}
    {X : Scheme.{u}} {x₀ : X ⟶ I.subscheme}
    (T : smallCrystallineSite S I γ h_compatible X x₀)
    {U V : (Opens T.obj.1.thickening.toTopCat)ᵒᵖ} (f : U ⟶ V) :
    (FirstOrderThickening.sheaf T).obj.map f ≫ q12App T V =
      q12App T U ≫ (sheaf T).obj.map f := sorry

/-- Naturality of `q₀₂`. -/
theorem q02_naturality
    {S : Scheme.{u}} {I : S.IdealSheafData}
    {γ : ∀ V : S.affineOpens, DividedPowers (I.ideal V)}
    {h_compatible :
      ∀ (V : S.affineOpens) (f : Γ(S, V)),
        (γ V).IsDPMorphism (γ (S.affineBasicOpen f))
          (S.presheaf.map (homOfLE (S.basicOpen_le f)).op).hom}
    {X : Scheme.{u}} {x₀ : X ⟶ I.subscheme}
    (T : smallCrystallineSite S I γ h_compatible X x₀)
    {U V : (Opens T.obj.1.thickening.toTopCat)ᵒᵖ} (f : U ⟶ V) :
    (FirstOrderThickening.sheaf T).obj.map f ≫ q02App T V =
      q02App T U ≫ (sheaf T).obj.map f := sorry

/-- The sheaf morphism `q₀ : 𝒪_T ⟶ 𝒪_{T''}`. -/
def q0
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
    { app := q0App T
      naturality := fun {_ _} f ↦ q0_naturality T f }

/-- The sheaf morphism `q₁ : 𝒪_T ⟶ 𝒪_{T''}`. -/
def q1
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
    { app := q1App T
      naturality := fun {_ _} f ↦ q1_naturality T f }

/-- The sheaf morphism `q₂ : 𝒪_T ⟶ 𝒪_{T''}`. -/
def q2
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
    { app := q2App T
      naturality := fun {_ _} f ↦ q2_naturality T f }

/-- The sheaf morphism `q₀₁ : 𝒪_{T'} ⟶ 𝒪_{T''}`. -/
def q01
    {S : Scheme.{u}} {I : S.IdealSheafData}
    {γ : ∀ V : S.affineOpens, DividedPowers (I.ideal V)}
    {h_compatible :
      ∀ (V : S.affineOpens) (f : Γ(S, V)),
        (γ V).IsDPMorphism (γ (S.affineBasicOpen f))
          (S.presheaf.map (homOfLE (S.basicOpen_le f)).op).hom}
    {X : Scheme.{u}} {x₀ : X ⟶ I.subscheme}
    (T : smallCrystallineSite S I γ h_compatible X x₀) :
    FirstOrderThickening.sheaf T ⟶ sheaf T :=
  ObjectProperty.homMk
    { app := q01App T
      naturality := fun {_ _} f ↦ q01_naturality T f }

/-- The sheaf morphism `q₁₂ : 𝒪_{T'} ⟶ 𝒪_{T''}`. -/
def q12
    {S : Scheme.{u}} {I : S.IdealSheafData}
    {γ : ∀ V : S.affineOpens, DividedPowers (I.ideal V)}
    {h_compatible :
      ∀ (V : S.affineOpens) (f : Γ(S, V)),
        (γ V).IsDPMorphism (γ (S.affineBasicOpen f))
          (S.presheaf.map (homOfLE (S.basicOpen_le f)).op).hom}
    {X : Scheme.{u}} {x₀ : X ⟶ I.subscheme}
    (T : smallCrystallineSite S I γ h_compatible X x₀) :
    FirstOrderThickening.sheaf T ⟶ sheaf T :=
  ObjectProperty.homMk
    { app := q12App T
      naturality := fun {_ _} f ↦ q12_naturality T f }

/-- The sheaf morphism `q₀₂ : 𝒪_{T'} ⟶ 𝒪_{T''}`. -/
def q02
    {S : Scheme.{u}} {I : S.IdealSheafData}
    {γ : ∀ V : S.affineOpens, DividedPowers (I.ideal V)}
    {h_compatible :
      ∀ (V : S.affineOpens) (f : Γ(S, V)),
        (γ V).IsDPMorphism (γ (S.affineBasicOpen f))
          (S.presheaf.map (homOfLE (S.basicOpen_le f)).op).hom}
    {X : Scheme.{u}} {x₀ : X ⟶ I.subscheme}
    (T : smallCrystallineSite S I γ h_compatible X x₀) :
    FirstOrderThickening.sheaf T ⟶ sheaf T :=
  ObjectProperty.homMk
    { app := q02App T
      naturality := fun {_ _} f ↦ q02_naturality T f }

/-- `q₁₂` preserves products on sections. -/
theorem q12_map_mul
    {S : Scheme.{u}} {I : S.IdealSheafData}
    {γ : ∀ V : S.affineOpens, DividedPowers (I.ideal V)}
    {h_compatible :
      ∀ (V : S.affineOpens) (f : Γ(S, V)),
        (γ V).IsDPMorphism (γ (S.affineBasicOpen f))
          (S.presheaf.map (homOfLE (S.basicOpen_le f)).op).hom}
    {X : Scheme.{u}} {x₀ : X ⟶ I.subscheme}
    (T : smallCrystallineSite S I γ h_compatible X x₀)
    (V : (Opens T.obj.1.thickening.toTopCat)ᵒᵖ)
    (x y : (FirstOrderThickening.sheaf T).obj.obj V) :
    q12Fun T V (x * y) = q12Fun T V x * q12Fun T V y := sorry

/-- `q₁₂` preserves divided powers: `δ''_n(q₁₂(f, ω)) = q₁₂(δ'_n(f, ω))`. -/
theorem q12_map_dpow
    {S : Scheme.{u}} {I : S.IdealSheafData}
    {γ : ∀ V : S.affineOpens, DividedPowers (I.ideal V)}
    {h_compatible :
      ∀ (V : S.affineOpens) (f : Γ(S, V)),
        (γ V).IsDPMorphism (γ (S.affineBasicOpen f))
          (S.presheaf.map (homOfLE (S.basicOpen_le f)).op).hom}
    {X : Scheme.{u}} {x₀ : X ⟶ I.subscheme}
    (T : smallCrystallineSite S I γ h_compatible X x₀)
    (V : (scheme T).affineOpens) (n : ℕ)
    (z : FirstOrderThickening.ring (T.obj.1.thickening.presheaf.obj (Opposite.op V.1))
          ((Ω[T.obj.1.thickeningToBase.toShHom]).val.obj (Opposite.op V.1)))
    (hz : z.1 ∈ T.obj.1.ideal.ideal (baseAffineOpen T V))
    (hq : q12Fun T (Opposite.op V.1) z ∈ (ideal T).ideal V) :
    (dividedPowers T V).dpow n (q12Fun T (Opposite.op V.1) z) =
      q12Fun T (Opposite.op V.1)
        ((T.obj.1.gamma (baseAffineOpen T V)).dpow n z.1,
          dpowPredSMul T V n z.1 z.2) := sorry

end CrystallineObject.SecondOrderThickening
