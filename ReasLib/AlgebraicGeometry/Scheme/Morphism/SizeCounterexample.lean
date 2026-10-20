module

public import ReasLib.AlgebraicGeometry.Scheme.Coproduct.FieldSpectra
public import ReasLib.AlgebraicGeometry.Scheme.Size
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.Algebra.Field.ULift
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.Algebra.Ring.ULift
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Order.Filter.Ultrafilter.Basic

@[expose] public section

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open Set Filter
open scoped Cardinal AlgebraicGeometry

namespace AlgebraicGeometry.Scheme.UltrafilterCoprod

/-- The product of countably many copies of the two-element field, lifted to universe `u`. -/
def ring : CommRingCat.{u} := .of (ULift.{u} (ℕ → ZMod 2))

/-- Evaluation of a sequence in the two-element field at an ultrafilter. -/
def residueFn (𝒰 : Ultrafilter ℕ) (a : ℕ → ZMod 2) : ZMod 2 :=
  (Ultrafilter.eq_pure_of_finite (𝒰.map a)).choose

/-- The ultrafilter evaluation map is determined by its finite-valued filter limit. -/
theorem residue_spec (𝒰 : Ultrafilter ℕ) (a : ℕ → ZMod 2) :
    𝒰.map a = pure (residueFn 𝒰 a) := by
  exact (Ultrafilter.eq_pure_of_finite (𝒰.map a)).choose_spec

/-- The residue homomorphism from the product ring associated to an ultrafilter. -/
def residue (𝒰 : Ultrafilter ℕ) : ULift.{u} (ℕ → ZMod 2) →+* ULift.{u} (ZMod 2) := by
  have residueFn_eventually (a : ℕ → ZMod 2) :
      ∀ᶠ n in (𝒰 : Filter ℕ), a n = residueFn 𝒰 a := by
    rw [Filter.eventually_iff]
    change (fun n => a n) ⁻¹' {residueFn 𝒰 a} ∈ (𝒰 : Filter ℕ)
    rw [← Filter.mem_map, ← Ultrafilter.coe_map, residue_spec]
    exact (Filter.mem_pure).2 rfl
  have residueFn_one : residueFn 𝒰 1 = 1 := by
    have h : (pure (residueFn 𝒰 1) : Filter (ZMod 2)) = (pure 1 : Filter (ZMod 2)) := by
      calc
        (pure (residueFn 𝒰 1) : Filter (ZMod 2)) =
            Filter.map (1 : ℕ → ZMod 2) (𝒰 : Filter ℕ) := by
          have hs := congrArg (fun F : Ultrafilter (ZMod 2) => (F : Filter (ZMod 2)))
            (residue_spec 𝒰 1)
          simpa only [Ultrafilter.coe_map, Ultrafilter.coe_pure] using hs.symm
        _ = (pure 1 : Filter (ZMod 2)) := by
          rw [show (1 : ℕ → ZMod 2) = fun _ => 1 by rfl, Filter.map_const]
    exact Filter.pure_injective h
  have residueFn_zero : residueFn 𝒰 0 = 0 := by
    have h : (pure (residueFn 𝒰 0) : Filter (ZMod 2)) = (pure 0 : Filter (ZMod 2)) := by
      calc
        (pure (residueFn 𝒰 0) : Filter (ZMod 2)) =
            Filter.map (0 : ℕ → ZMod 2) (𝒰 : Filter ℕ) := by
          have hs := congrArg (fun F : Ultrafilter (ZMod 2) => (F : Filter (ZMod 2)))
            (residue_spec 𝒰 0)
          simpa only [Ultrafilter.coe_map, Ultrafilter.coe_pure] using hs.symm
        _ = (pure 0 : Filter (ZMod 2)) := by
          rw [show (0 : ℕ → ZMod 2) = fun _ => 0 by rfl, Filter.map_const]
    exact Filter.pure_injective h
  have residueFn_add (a b : ℕ → ZMod 2) :
      residueFn 𝒰 (a + b) = residueFn 𝒰 a + residueFn 𝒰 b := by
    have hab : (a + b) =ᶠ[(𝒰 : Filter ℕ)]
        (fun _ => residueFn 𝒰 a + residueFn 𝒰 b) := by
      filter_upwards [residueFn_eventually a, residueFn_eventually b] with n ha hb
      simp [ha, hb]
    have h : (pure (residueFn 𝒰 (a + b)) : Filter (ZMod 2)) =
        (pure (residueFn 𝒰 a + residueFn 𝒰 b) : Filter (ZMod 2)) := by
      calc
        (pure (residueFn 𝒰 (a + b)) : Filter (ZMod 2)) =
            Filter.map (a + b) (𝒰 : Filter ℕ) := by
          have hs := congrArg (fun F : Ultrafilter (ZMod 2) => (F : Filter (ZMod 2)))
            (residue_spec 𝒰 (a + b))
          simpa only [Ultrafilter.coe_map, Ultrafilter.coe_pure] using hs.symm
        _ = Filter.map (fun _ => residueFn 𝒰 a + residueFn 𝒰 b) (𝒰 : Filter ℕ) :=
          Filter.map_congr hab
        _ = (pure (residueFn 𝒰 a + residueFn 𝒰 b) : Filter (ZMod 2)) := by
          rw [Filter.map_const]
    exact Filter.pure_injective h
  have residueFn_mul (a b : ℕ → ZMod 2) :
      residueFn 𝒰 (a * b) = residueFn 𝒰 a * residueFn 𝒰 b := by
    have hab : (a * b) =ᶠ[(𝒰 : Filter ℕ)]
        (fun _ => residueFn 𝒰 a * residueFn 𝒰 b) := by
      filter_upwards [residueFn_eventually a, residueFn_eventually b] with n ha hb
      simp [ha, hb]
    have h : (pure (residueFn 𝒰 (a * b)) : Filter (ZMod 2)) =
        (pure (residueFn 𝒰 a * residueFn 𝒰 b) : Filter (ZMod 2)) := by
      calc
        (pure (residueFn 𝒰 (a * b)) : Filter (ZMod 2)) =
            Filter.map (a * b) (𝒰 : Filter ℕ) := by
          have hs := congrArg (fun F : Ultrafilter (ZMod 2) => (F : Filter (ZMod 2)))
            (residue_spec 𝒰 (a * b))
          simpa only [Ultrafilter.coe_map, Ultrafilter.coe_pure] using hs.symm
        _ = Filter.map (fun _ => residueFn 𝒰 a * residueFn 𝒰 b) (𝒰 : Filter ℕ) :=
          Filter.map_congr hab
        _ = (pure (residueFn 𝒰 a * residueFn 𝒰 b) : Filter (ZMod 2)) := by
          rw [Filter.map_const]
    exact Filter.pure_injective h
  exact RingHom.ulift.{u, u}
    { toFun := residueFn 𝒰
      map_one' := residueFn_one
      map_mul' := residueFn_mul
      map_zero' := residueFn_zero
      map_add' := residueFn_add }

/-- The lifted residue homomorphism evaluates by its unlifted residue function. -/
theorem residue_apply (𝒰 : Ultrafilter ℕ) (x : ULift.{u} (ℕ → ZMod 2)) :
    (residue.{u} 𝒰 x).down = residueFn 𝒰 x.down := by
  rfl

/-- The source scheme is the coproduct of the residue-field spectra indexed by ultrafilters. -/
def source : Scheme.{u} :=
  Coproduct.FieldSpectra.family (fun _ : ULift.{u} (Ultrafilter ℕ) => ULift.{u} (ZMod 2))

/-- The target scheme is the spectrum of the countable product ring. -/
def target : Scheme.{u} := Spec ring

/-- The canonical morphism from the residue-field coproduct to the product spectrum. -/
def hom : source.{u} ⟶ target.{u} :=
  Sigma.desc fun 𝒰 : ULift.{u} (Ultrafilter ℕ) ↦
    Spec.map (CommRingCat.ofHom (residue.{u} 𝒰.down))

/-- The coproduct component of the canonical morphism is the corresponding residue spectrum map. -/
theorem ι_comp_hom (𝒰 : ULift.{u} (Ultrafilter ℕ)) :
    Sigma.ι (fun _ : ULift.{u} (Ultrafilter ℕ) =>
        Spec (.of (ULift.{u} (ZMod 2)))) 𝒰 ≫ hom.{u} =
      Spec.map (CommRingCat.ofHom (residue.{u} 𝒰.down)) := by
  exact Sigma.ι_desc _ _

/-- The canonical morphism is a monomorphism. -/
instance instMonoHom : Mono hom.{u} := sorry

/-- The canonical morphism is locally of finite type. -/
instance instLocallyOfFiniteTypeHom : LocallyOfFiniteType hom.{u} := sorry

/-- The canonical locally finite type monomorphism violates the scheme-size bound. -/
theorem not_size_le : ¬ source.{u}.size ≤ target.{u}.size := sorry

end AlgebraicGeometry.Scheme.UltrafilterCoprod
