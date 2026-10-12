/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Etale.CurveComparison.FiniteCurveComplexModel
public import ReasLib.AlgebraicGeometry.Scheme.Module.Etale.CurveComparison.NoncommCompletedRing

@[expose] public section
open CategoryTheory CategoryTheory.Action.ModuleCat
noncomputable section
universe u v

namespace FiniteComplexQuotient
variable (R : Type u) [Ring R]
variable (G : Type v) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- The actual action kernel of this one representation. -/
def kernel (M : DiscreteModuleCat R G) : Subgroup G where
  carrier := {g | M.obj.ρ g = 𝟙 _}
  one_mem' := by sorry
  mul_mem' := by sorry
  inv_mem' := by sorry

/-- Openness requires a FINITE carrier here; no unrestricted open-kernel instance. -/
theorem kernel_open (M : DiscreteModuleCat R G) [Finite M.obj.V] :
    IsOpen (kernel R G M : Set G) := by sorry

/-- Bundle exactly this finite action's open normal kernel. -/
def normalKernel (M : DiscreteModuleCat R G) [Finite M.obj.V] : OpenNormalSubgroup G where
  toOpenSubgroup := ⟨kernel R G M, kernel_open R G M⟩
  isNormal' := by sorry

variable (K : CochainComplex (DiscreteModuleCat R G) ℤ)
variable [Finite (K.X 0).obj.V] [Finite (K.X 1).obj.V] [Finite (K.X 2).obj.V]

/-- A specified common quotient for the three nonzero finite terms. -/
def commonKernel : OpenNormalSubgroup G :=
  normalKernel R G (K.X 0) ⊓ normalKernel R G (K.X 1) ⊓ normalKernel R G (K.X 2)

/-- The quotient embeds in the product of the three finite automorphism groups. -/
instance quotient_finite : Finite (G ⧸ (commonKernel R G K).toSubgroup) := by sorry

/-- Outside the three degrees the complex is strictly zero; the common kernel
acts trivially in EVERY degree under these explicit support hypotheses. -/
theorem commonKernel_fixes [K.IsStrictlyGE 0] [K.IsStrictlyLE 2]
    (i : ℤ) (g : G) (hg : g ∈ commonKernel R G K) : (K.X i).obj.ρ g = 𝟙 _ := by sorry

variable [K.IsStrictlyGE 0] [K.IsStrictlyLE 2]

/-- The actual degreewise finite-quotient action, obtained by quotient descent. -/
def quotientAction (i : ℤ) :
    Action (ModuleCat.{max u v} R) (G ⧸ (commonKernel R G K).toSubgroup) where
  V := (K.X i).obj.V
  ρ := QuotientGroup.lift (commonKernel R G K).toSubgroup (K.X i).obj.ρ
    (fun g hg ↦ commonKernel_fixes R G K i g hg)

/-- Descend the actual cochain maps; no replacement of the finite complex by
its cohomology objects is involved. -/
def complex : CochainComplex
    (Action (ModuleCat.{max u v} R) (G ⧸ (commonKernel R G K).toSubgroup)) ℤ where
  X := quotientAction R G K
  d i j := { hom := (K.d i j).hom.hom, comm := fun _ ↦ by sorry }
  shape := by sorry
  d_comp_d' := by sorry

/-- Inflating this finite-quotient complex recovers the original action and
all original differentials through identity coefficient maps. -/
def inflationIso :
    ((Action.res (ModuleCat.{max u v} R)
      (QuotientGroup.mk' (commonKernel R G K).toSubgroup)).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj (complex R G K) ≅
    (((openStabilizer R G).ι).mapHomologicalComplex (ComplexShape.up ℤ)).obj K :=
  HomologicalComplex.Hom.isoOfComponents
    (fun i ↦ Action.mkIso (Iso.refl (K.X i).obj.V) (fun _ ↦ by sorry)) (by sorry)

end FiniteComplexQuotient
