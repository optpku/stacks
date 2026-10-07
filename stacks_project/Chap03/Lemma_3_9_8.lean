module

public import stacks_project.Chap03.Lemma_3_9_4_Size
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.Order.Filter.Ultrafilter.Basic
public import Mathlib.Algebra.Ring.ULift
public import Mathlib.Data.ZMod.Basic

@[expose] public section

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped Cardinal AlgebraicGeometry

namespace AlgebraicGeometry.Scheme

/-- Lemma 3.9.8 (1): a quasi-compact monomorphism of schemes `f : X ⟶ Y` satisfies
`X.size ≤ Y.size`. -/
@[stacks 04VA]
theorem size_le_of_mono_quasiCompact {X Y : Scheme.{u}} (f : X ⟶ Y) [Mono f] [QuasiCompact f] :
    X.size ≤ Y.size := sorry

/-- Lemma 3.9.8 (2): a monomorphism of schemes `f : X ⟶ Y` which is locally of finite presentation
satisfies `X.size ≤ Y.size`. -/
@[stacks 04VA]
theorem size_le_of_mono_locallyOfFinitePresentation {X Y : Scheme.{u}} (f : X ⟶ Y)
    [Mono f] [LocallyOfFinitePresentation f] :
    X.size ≤ Y.size := sorry

/-- If a monomorphism of schemes is quasi-compact or locally of finite presentation, then the size
of the source is at most the size of the target. -/
theorem size_le_of_mono_of_quasiCompact_or_locallyOfFinitePresentation
    {X Y : Scheme.{u}} (f : X ⟶ Y) [Mono f]
    (h : QuasiCompact f ∨ LocallyOfFinitePresentation f) :
    X.size ≤ Y.size := sorry

namespace UltrafilterCoprod

/-- The product ring `∏_{n : ℕ} ZMod 2`, lifted to universe `u`. -/
def ring : CommRingCat.{u} := .of (ULift.{u} (ℕ → ZMod 2))

/-- Evaluation of `a : ℕ → ZMod 2` along an ultrafilter, as the unique point of `𝒰.map a`. -/
def residueFn (𝒰 : Ultrafilter ℕ) (a : ℕ → ZMod 2) : ZMod 2 :=
  (Ultrafilter.eq_pure_of_finite (𝒰.map a)).choose

/-- The residue map of an ultrafilter on `ℕ`, lifted to universe `u`. -/
def residue (𝒰 : Ultrafilter ℕ) : ULift.{u} (ℕ → ZMod 2) →+* ULift.{u} (ZMod 2) :=
  RingHom.ulift.{u, u}
    { toFun := residueFn 𝒰
      map_one' := sorry
      map_mul' := sorry
      map_zero' := sorry
      map_add' := sorry }

/-- Evaluation along `𝒰` is the unique point of the finite ultrafilter `𝒰.map a`. -/
theorem residue_spec (𝒰 : Ultrafilter ℕ) (a : ℕ → ZMod 2) :
    𝒰.map a = pure (residueFn 𝒰 a) := sorry

/-- The lifted residue map evaluates by the unlifted principal-point residue. -/
theorem residue_apply (𝒰 : Ultrafilter ℕ) (x : ULift.{u} (ℕ → ZMod 2)) :
    (residue.{u} 𝒰 x).down = residueFn 𝒰 x.down := sorry

/-- The constant family of residue-field schemes indexed by ultrafilters on `ℕ`. -/
def residueFamily : ULift.{u} (Ultrafilter ℕ) → Scheme.{u} :=
  fun _ ↦ Spec (.of (ULift.{u} (ZMod 2)))

/-- Each component of the ultrafilter family is `Spec` of the lifted field `ZMod 2`. -/
theorem residueFamily_apply (𝒰 : ULift.{u} (Ultrafilter ℕ)) :
    residueFamily.{u} 𝒰 = Spec (.of (ULift.{u} (ZMod 2))) := sorry

/-- The coproduct `∐_𝒰 Spec(ZMod 2)` of residue-field schemes indexed by ultrafilters on `ℕ`. -/
def source : Scheme.{u} := ∐ residueFamily.{u}

/-- The spectrum of the product ring `∏_{n : ℕ} ZMod 2`. -/
def target : Scheme.{u} := Spec ring

/-- The source-specified monomorphism `∐_𝒰 Spec(ZMod 2) ⟶ Spec(∏_{n : ℕ} ZMod 2)`. -/
def hom : source.{u} ⟶ target.{u} :=
  Sigma.desc fun 𝒰 : ULift.{u} (Ultrafilter ℕ) ↦
    Spec.map (CommRingCat.ofHom (residue.{u} 𝒰.down))

/-- The target of the ultrafilter coproduct morphism is `Spec` of the product ring. -/
theorem target_spec : target.{u} = Spec ring.{u} := sorry

/-- On the component indexed by `𝒰`, the coproduct morphism is `Spec` of the residue map. -/
theorem ι_comp_hom (𝒰 : ULift.{u} (Ultrafilter ℕ)) :
    Sigma.ι residueFamily.{u} 𝒰 ≫ hom.{u} =
      Spec.map (CommRingCat.ofHom (residue.{u} 𝒰.down)) := sorry

/-- The ultrafilter coproduct morphism is a monomorphism. -/
instance instMonoHom : Mono hom.{u} := sorry

/-- The ultrafilter coproduct morphism is locally of finite type. -/
instance instLocallyOfFiniteTypeHom : LocallyOfFiniteType hom.{u} := sorry

/-- Lemma 3.9.8 (3): this locally finite type monomorphism does not satisfy the size bound. -/
@[stacks 04VA]
theorem not_size_le : ¬ source.{u}.size ≤ target.{u}.size := sorry

end UltrafilterCoprod

end AlgebraicGeometry.Scheme
