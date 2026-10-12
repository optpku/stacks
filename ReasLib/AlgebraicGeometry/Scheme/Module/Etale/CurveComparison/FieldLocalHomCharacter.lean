/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module
public import ReasLib.AlgebraicGeometry.Scheme.Module.Etale.CurveComparison.FieldLocalHomStalk
public import ReasLib.AlgebraicGeometry.Scheme.Module.Etale.CurveComparison.NoncommCompactCharacters
public import ReasLib.AlgebraicGeometry.Scheme.Module.Etale.CurveComparison.ResidualNormalizedRootsTrace

@[expose] public section
open CategoryTheory CategoryTheory.Action.ModuleCat
open AlgebraicGeometry AlgebraicGeometry.Scheme
noncomputable section
universe u

namespace FieldLocalHomCharacter
variable (k : Type u) [Field k]
variable (n : ℕ) [hnzero : NeZero n]
variable {R : Type (u + 1)} [Ring R] [Finite R]
variable (h : ActualRootsModule.Coeff.{u} n →+* R)
variable (hc : ∀ (a : ActualRootsModule.Coeff.{u} n) (r : R), h a * r = r * h a)
variable [(Spec (CommRingCat.of k)).smallEtaleTopology.HasSheafCompose (NoncommLocalHom.modules h)]
variable [(Spec (CommRingCat.of k)).smallEtaleTopology.HasSheafCompose
  (ModuleCat.restrictScalars (NoncommLocalHom.opScalarHom h hc))]
variable (B : DiscreteModuleCat R Gal(AlgebraicClosure k/k))

abbrev source := (FieldModuleDescent.forward k Rᵐᵒᵖ).obj
  (NoncommLocalHom.obj h hc (Spec (CommRingCat.of k)) ((FieldModuleDescent.inverse k R).obj B)
    (ResidualNormalizedRootsTrace.fieldTarget (k := k) n))

/-- Read the Hom germ through the actual two field counits and send its Z/n
value to Q/Z by z↦z/n. No primitive-root basis is chosen for this trace coefficient. -/
def moduleMap : (source k n h hc B).obj.V →ₗ[Rᵐᵒᵖ] (NoncommCompactCharacters.dual R B.obj.V).toModule where
  toFun α :=
    { toFun := fun b ↦ ActualGeometricTraceCharacter.normalizedCharacter n
        ((FieldModuleDescent.counitLinear k (ActualRootsModule.Coeff.{u} n)
          (ResidualNormalizedRootsTrace.target (k := k) n)).hom
          (FieldLocalHomStalk.evaluate k h hc ((FieldModuleDescent.inverse k R).obj B)
            (ResidualNormalizedRootsTrace.fieldTarget (k := k) n) α
            (((FieldModuleDescent.equivalence k R).counitIso.app B).inv.hom.hom.hom b))).down
      map_zero' := by sorry
      map_add' := by sorry }
  map_add' := by sorry
  map_smul' := by sorry

include hnzero in
/-- Finite presentation of the field coefficient makes Hom commute with the
actual stalk. The normalized Z/n character identifies all n-torsion characters. -/
theorem moduleMap_bijective [Finite B.obj.V] : Function.Bijective (moduleMap k n h hc B) := by sorry

def moduleEquiv [Finite B.obj.V] : (source k n h hc B).obj.V ≃ₗ[Rᵐᵒᵖ]
    (NoncommCompactCharacters.dual R B.obj.V).toModule :=
  LinearEquiv.ofBijective (moduleMap k n h hc B) (moduleMap_bijective k n h hc B)

/-- Field-point natural automorphisms give precisely contragredient action on
the resulting characters; the trace coefficient has its actual trivial action. -/
theorem equivariant (σ : Gal(AlgebraicClosure k/k)) (α : (source k n h hc B).obj.V) :
    moduleMap k n h hc B (((source k n h hc B).obj.ρ σ).hom α) =
      ActualOppositeCharacter.map R B.obj.V (B.obj.ρ σ⁻¹).hom (moduleMap k n h hc B α) := by sorry

/-- The finite input wrapper retains exactly the given representation. -/
def finiteInput [Finite B.obj.V] : (finiteTypeDiscreteModule R Gal(AlgebraicClosure k/k)).FullSubcategory :=
  ⟨B, by
    change Module.Finite R B.obj.V
    infer_instance⟩

def characterRepresentation [Finite B.obj.V] :=
  (ActualOppositeCharacter.finiteRepresentation R Gal(AlgebraicClosure k/k) (finiteInput k B)).obj

/-- The field-Hom character map, with BOTH coefficient and residual actions,
is a genuine iso of discrete representations for the actual finite input. -/
def discreteIso [Finite B.obj.V] : source k n h hc B ≅ characterRepresentation k B :=
  ObjectProperty.isoMk _ (Action.mkIso (moduleEquiv k n h hc B).toModuleIso (by
    intro σ
    apply ModuleCat.hom_ext
    ext α
    exact equivariant k n h hc B σ α))

/-- Complete this specified finite-character map, not merely its underlying additive function. -/
def completedIso [Finite B.obj.V] :
    (NoncommPointwiseCompletedAction.functor Rᵐᵒᵖ Gal(AlgebraicClosure k/k)).obj (source k n h hc B) ≅
    (NoncommPointwiseCompletedAction.functor Rᵐᵒᵖ Gal(AlgebraicClosure k/k)).obj (characterRepresentation k B) :=
  (NoncommPointwiseCompletedAction.functor Rᵐᵒᵖ Gal(AlgebraicClosure k/k)).mapIso (discreteIso k n h hc B)

end FieldLocalHomCharacter
