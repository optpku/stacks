/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExactSequences
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.Picard.Cohomology.Equiv
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.KernelIdeal.Exact
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.SquareZeroExtension
public import ReasLib.Algebra.Category.Ring.Sheaf.Units.Map

/-!
# The Picard cohomology sequence of a square-zero extension

This file constructs the units short complex of a square-zero morphism of
commutative-ring sheaves and the finite part of its cohomology sequence in which
degree-one units cohomology is transported to Picard groups.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe u v

namespace SheafOfModules.RingedSite.KernelIdeal

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable {A Q : Sheaf J CommRingCat.{max u v}}
variable [J.HasSheafCompose
  (forget₂ CommRingCat.{max u v} RingCat.{max u v})]
variable [J.HasSheafCompose
  (forget₂ RingCat.{max u v} AddCommGrpCat.{max u v})]

/-- The product `(1 + x) * (1 - x)` is one for a section of a square-zero
kernel ideal. -/
theorem oneAdd_mul_oneSub (π : A ⟶ Q) (hzero : IsSquareZero π)
    (U : Cᵒᵖ) (x : (underlyingAdditive π).1.obj U) :
    (1 + ιApp π U x) * (1 - ιApp π U x) = 1 := sorry

/-- The explicit unit `1 + x` associated to a section `x` of a square-zero
kernel ideal, with inverse `1 - x`. -/
def oneAddUnit (π : A ⟶ Q) (hzero : IsSquareZero π)
    (U : Cᵒᵖ) (x : (underlyingAdditive π).1.obj U) :
    (A.1.obj U)ˣ :=
  Units.mkOfMulEqOne (1 + ιApp π U x) (1 - ιApp π U x)
    (oneAdd_mul_oneSub π hzero U x)

/-- The section `0` is sent to the neutral additive unit. -/
theorem oneAddUnit_zero (π : A ⟶ Q) (hzero : IsSquareZero π) (U : Cᵒᵖ) :
    CategoryTheory.Sheaf.unitsAddSheafSection A
      (oneAddUnit π hzero U 0) = 0 := sorry

/-- The assignment `x ↦ 1 + x` sends addition in a square-zero ideal to
multiplication of units. -/
theorem oneAddUnit_add (π : A ⟶ Q) (hzero : IsSquareZero π)
    (U : Cᵒᵖ) (x y : (underlyingAdditive π).1.obj U) :
    CategoryTheory.Sheaf.unitsAddSheafSection A
        (oneAddUnit π hzero U (x + y)) =
      CategoryTheory.Sheaf.unitsAddSheafSection A (oneAddUnit π hzero U x) +
        CategoryTheory.Sheaf.unitsAddSheafSection A
          (oneAddUnit π hzero U y) := sorry

/-- The additive homomorphism on sections given by `x ↦ 1 + x`. -/
noncomputable def oneAddHom (π : A ⟶ Q) (hzero : IsSquareZero π) (U : Cᵒᵖ) :
    (underlyingAdditive π).1.obj U →+
      (CategoryTheory.Sheaf.unitsAddSheaf A).1.obj U where
  toFun := fun x ↦ CategoryTheory.Sheaf.unitsAddSheafSection A
    (oneAddUnit π hzero U x)
  map_zero' := oneAddUnit_zero π hzero U
  map_add' := oneAddUnit_add π hzero U

/-- The sectionwise maps `x ↦ 1 + x` commute with restriction maps. -/
theorem oneAdd_naturality (π : A ⟶ Q) (hzero : IsSquareZero π)
    {U V : Cᵒᵖ} (i : U ⟶ V) :
    (underlyingAdditive π).1.map i ≫
        AddCommGrpCat.ofHom (oneAddHom π hzero V) =
      AddCommGrpCat.ofHom (oneAddHom π hzero U) ≫
        (CategoryTheory.Sheaf.unitsAddSheaf A).1.map i := sorry

/-- The canonical additive-sheaf morphism from a square-zero kernel ideal to
the units sheaf, sectionwise given by `x ↦ 1 + x`. -/
noncomputable def oneAdd (π : A ⟶ Q) (hzero : IsSquareZero π) :
    underlyingAdditive π ⟶ CategoryTheory.Sheaf.unitsAddSheaf A :=
  ObjectProperty.homMk
    { app := fun U ↦ AddCommGrpCat.ofHom (oneAddHom π hzero U)
      naturality := fun {_ _} i ↦ oneAdd_naturality π hzero i }

/-- The component of `oneAdd π hzero` is the additive homomorphism
`x ↦ 1 + x`. -/
theorem oneAdd_app (π : A ⟶ Q) (hzero : IsSquareZero π) (U : Cᵒᵖ) :
    (oneAdd π hzero).hom.app U =
      AddCommGrpCat.ofHom (oneAddHom π hzero U) := sorry

/-- The one-plus map followed by the induced map on units is zero. -/
theorem oneAdd_comp_unitsAddMap (π : A ⟶ Q) (hzero : IsSquareZero π) :
    oneAdd π hzero ≫ CategoryTheory.Sheaf.unitsAddMap π = 0 := sorry

/-- The short complex `Ker(π) ⟶ Aˣ ⟶ Qˣ` associated to a square-zero
morphism of commutative-ring sheaves. -/
noncomputable def unitsShortComplex (π : A ⟶ Q) (hzero : IsSquareZero π) :
    ShortComplex (Sheaf J AddCommGrpCat.{max u v}) :=
  ShortComplex.mk (oneAdd π hzero) (CategoryTheory.Sheaf.unitsAddMap π)
    (oneAdd_comp_unitsAddMap π hzero)

/-- The first map of the square-zero units short complex is `x ↦ 1 + x`. -/
theorem unitsShortComplex_f (π : A ⟶ Q) (hzero : IsSquareZero π) :
    (unitsShortComplex π hzero).f = oneAdd π hzero := sorry

/-- The second map of the square-zero units short complex is induced by `π`
on units. -/
theorem unitsShortComplex_g (π : A ⟶ Q) (hzero : IsSquareZero π) :
    (unitsShortComplex π hzero).g = CategoryTheory.Sheaf.unitsAddMap π := sorry

/-- Local surjectivity makes the square-zero units short complex short exact. -/
theorem unitsShortComplex_shortExact (π : A ⟶ Q) (hzero : IsSquareZero π)
    [CategoryTheory.Sheaf.IsLocallySurjective π] :
    (unitsShortComplex π hzero).ShortExact := sorry

section Cohomology

variable [HasWeakSheafify J AddCommGrpCat.{max u v}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
variable [HasExt.{max u v + 1} (Sheaf J AddCommGrpCat.{max u v})]

/-- The six-object degree-`n`/degree-`n+1` cohomology window associated to the
square-zero units short complex. -/
noncomputable def unitsCohomologyWindow (π : A ⟶ Q) (hzero : IsSquareZero π)
    (hS : (unitsShortComplex π hzero).ShortExact) (n : ℕ) :
    ComposableArrows AddCommGrpCat.{max u v + 1} 5 :=
  CategoryTheory.Abelian.Ext.covariantSequence
    ((CategoryTheory.constantSheaf J AddCommGrpCat.{max u v}).obj
      (AddCommGrpCat.of (ULift ℤ))) hS n (n + 1) rfl

/-- Every adjacent pair in `unitsCohomologyWindow` is exact. -/
theorem unitsCohomologyWindow_exact (π : A ⟶ Q) (hzero : IsSquareZero π)
    (hS : (unitsShortComplex π hzero).ShortExact) (n : ℕ) :
    (unitsCohomologyWindow π hzero hS n).Exact := sorry

end Cohomology

end SheafOfModules.RingedSite.KernelIdeal

namespace SheafOfModules.RingedSite.KernelIdeal

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable {A Q : Sheaf J CommRingCat.{max u v}}
variable [J.HasSheafCompose
  (forget₂ CommRingCat.{max u v} RingCat.{max u v})]
variable [J.HasSheafCompose
  (forget₂ RingCat.{max u v} AddCommGrpCat.{max u v})]
variable [J.HasSheafCompose (CategoryTheory.forget CommRingCat.{max u v})]
variable [HasWeakSheafify J AddCommGrpCat.{max u v}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
variable [HasExt.{max u v + 1} (Sheaf J AddCommGrpCat.{max u v})]
variable [A.IsLocallyRinged] [Q.IsLocallyRinged]

/-- The map `H¹(Ker(π)) ⟶ Pic(A)` obtained by transporting the one-plus
cohomology map through the Picard comparison. -/
noncomputable def toPicard (π : A ⟶ Q) (hzero : IsSquareZero π)
    (hS : (unitsShortComplex π hzero).ShortExact) :
    AddCommGrpCat.of ((underlyingAdditive π).H 1) ⟶
      AddCommGrpCat.of (PicardGroup J A) :=
  (unitsCohomologyWindow π hzero hS 0).map' 3 4 ≫
    AddCommGrpCat.ofHom (PicardGroup.cohomologyInverse A)

/-- The map `toPicard` commutes with the canonical map from Picard classes to
first units cohomology. -/
theorem toPicard_cohomologyClass (π : A ⟶ Q) (hzero : IsSquareZero π)
    (hS : (unitsShortComplex π hzero).ShortExact) :
    toPicard π hzero hS ≫ AddCommGrpCat.ofHom (PicardGroup.cohomologyClass A) =
      (unitsCohomologyWindow π hzero hS 0).map' 3 4 := sorry

/-- The map `Pic(A) ⟶ Pic(Q)` induced by `π`, defined through the canonical
degree-one units-cohomology comparisons. -/
noncomputable def picardMap (π : A ⟶ Q) (hzero : IsSquareZero π)
    (hS : (unitsShortComplex π hzero).ShortExact) :
    AddCommGrpCat.of (PicardGroup J A) ⟶ AddCommGrpCat.of (PicardGroup J Q) :=
  AddCommGrpCat.ofHom (PicardGroup.cohomologyClass A) ≫
    (unitsCohomologyWindow π hzero hS 0).map' 4 5 ≫
      AddCommGrpCat.ofHom (PicardGroup.cohomologyInverse Q)

/-- The Picard map commutes with the degree-one cohomology map on units. -/
theorem picardMap_cohomologyClass (π : A ⟶ Q) (hzero : IsSquareZero π)
    (hS : (unitsShortComplex π hzero).ShortExact) :
    picardMap π hzero hS ≫ AddCommGrpCat.ofHom (PicardGroup.cohomologyClass Q) =
      AddCommGrpCat.ofHom (PicardGroup.cohomologyClass A) ≫
        (unitsCohomologyWindow π hzero hS 0).map' 4 5 := sorry

/-- The map `Pic(Q) ⟶ H²(Ker(π))`, obtained by applying the next connecting
morphism after the Picard cohomology comparison. -/
noncomputable def fromPicard (π : A ⟶ Q) (hzero : IsSquareZero π)
    (hS : (unitsShortComplex π hzero).ShortExact) :
    AddCommGrpCat.of (PicardGroup J Q) ⟶
      AddCommGrpCat.of ((underlyingAdditive π).H 2) :=
  AddCommGrpCat.ofHom (PicardGroup.cohomologyClass Q) ≫
    (unitsCohomologyWindow π hzero hS 1).map' 2 3

/-- The terminal Picard boundary is the degree-one connecting morphism after
the Picard cohomology comparison. -/
theorem fromPicard_cohomologyClass (π : A ⟶ Q) (hzero : IsSquareZero π)
    (hS : (unitsShortComplex π hzero).ShortExact) :
    fromPicard π hzero hS =
      AddCommGrpCat.ofHom (PicardGroup.cohomologyClass Q) ≫
        (unitsCohomologyWindow π hzero hS 1).map' 2 3 := sorry

/-- The eight-object Picard cohomology row
`0 ⟶ H⁰(I) ⟶ H⁰(Aˣ) ⟶ H⁰(Qˣ) ⟶ H¹(I) ⟶ Pic(A) ⟶ Pic(Q) ⟶ H²(I)`
for `I = Ker(π)`. -/
noncomputable def picardCohomologySequence (π : A ⟶ Q)
    (hzero : IsSquareZero π) (hS : (unitsShortComplex π hzero).ShortExact) :
    ComposableArrows AddCommGrpCat.{max u v + 1} 7 :=
  ((ComposableArrows.mk₅
      ((unitsCohomologyWindow π hzero hS 0).map' 1 2)
      ((unitsCohomologyWindow π hzero hS 0).map' 2 3)
      (toPicard π hzero hS) (picardMap π hzero hS)
      (fromPicard π hzero hS)).precomp
    ((unitsCohomologyWindow π hzero hS 0).map' 0 1)).precomp
      (0 : ⊥_ AddCommGrpCat.{max u v + 1} ⟶
        AddCommGrpCat.of ((underlyingAdditive π).H 0))

/-- The first arrow of the Picard cohomology row is the zero map into
`H⁰(Ker(π))`. -/
theorem picardCohomologySequence_map_zero (π : A ⟶ Q)
    (hzero : IsSquareZero π) (hS : (unitsShortComplex π hzero).ShortExact) :
    (picardCohomologySequence π hzero hS).map' 0 1 =
      (0 : ⊥_ AddCommGrpCat.{max u v + 1} ⟶
        AddCommGrpCat.of ((underlyingAdditive π).H 0)) := sorry

/-- The second arrow of the Picard cohomology row is induced by `x ↦ 1 + x`
on degree-zero cohomology. -/
theorem picardCohomologySequence_map_one (π : A ⟶ Q)
    (hzero : IsSquareZero π) (hS : (unitsShortComplex π hzero).ShortExact) :
    (picardCohomologySequence π hzero hS).map' 1 2 =
      (unitsCohomologyWindow π hzero hS 0).map' 0 1 := sorry

/-- The third arrow of the Picard cohomology row is the degree-zero map on
units induced by `π`. -/
theorem picardCohomologySequence_map_two (π : A ⟶ Q)
    (hzero : IsSquareZero π) (hS : (unitsShortComplex π hzero).ShortExact) :
    (picardCohomologySequence π hzero hS).map' 2 3 =
      (unitsCohomologyWindow π hzero hS 0).map' 1 2 := sorry

/-- The fourth arrow of the Picard cohomology row is the first connecting
morphism. -/
theorem picardCohomologySequence_map_three (π : A ⟶ Q)
    (hzero : IsSquareZero π) (hS : (unitsShortComplex π hzero).ShortExact) :
    (picardCohomologySequence π hzero hS).map' 3 4 =
      (unitsCohomologyWindow π hzero hS 0).map' 2 3 := sorry

/-- The fifth arrow of the Picard cohomology row is the transported map from
`H¹(Ker(π))` to `Pic(A)`. -/
theorem picardCohomologySequence_map_four (π : A ⟶ Q)
    (hzero : IsSquareZero π) (hS : (unitsShortComplex π hzero).ShortExact) :
    (picardCohomologySequence π hzero hS).map' 4 5 =
      toPicard π hzero hS := sorry

/-- The sixth arrow of the Picard cohomology row is the Picard map induced by
`π`. -/
theorem picardCohomologySequence_map_five (π : A ⟶ Q)
    (hzero : IsSquareZero π) (hS : (unitsShortComplex π hzero).ShortExact) :
    (picardCohomologySequence π hzero hS).map' 5 6 =
      picardMap π hzero hS := sorry

/-- The seventh arrow of the Picard cohomology row is the transported second
connecting morphism. -/
theorem picardCohomologySequence_map_six (π : A ⟶ Q)
    (hzero : IsSquareZero π) (hS : (unitsShortComplex π hzero).ShortExact) :
    (picardCohomologySequence π hzero hS).map' 6 7 =
      fromPicard π hzero hS := sorry

/-- The Picard cohomology row of a square-zero units short complex is exact. -/
theorem picardCohomologySequence_exact (π : A ⟶ Q)
    (hzero : IsSquareZero π) (hS : (unitsShortComplex π hzero).ShortExact) :
    (picardCohomologySequence π hzero hS).Exact := sorry

end SheafOfModules.RingedSite.KernelIdeal
