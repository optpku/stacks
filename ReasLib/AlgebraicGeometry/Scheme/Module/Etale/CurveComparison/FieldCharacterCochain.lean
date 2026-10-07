module
public import ReasLib.AlgebraicGeometry.Scheme.Module.Etale.CurveComparison.FieldLocalHomCharacter
public import ReasLib.AlgebraicGeometry.Scheme.Module.Etale.CurveComparison.LocalHomSingleTarget
public import ReasLib.AlgebraicGeometry.Scheme.Module.Etale.CurveComparison.FieldHomNormalizedTrace

@[expose] public section
open CategoryTheory CategoryTheory.Action.ModuleCat
open AlgebraicGeometry AlgebraicGeometry.Scheme
noncomputable section
universe u

namespace FieldCharacterCochain
variable (k : Type u) [Field k]
variable {R : Type (u + 1)} [Ring R] [Finite R]
variable (B : ChainComplex (DiscreteModuleCat R Gal(AlgebraicClosure k/k)) ℕ)
variable [hB : ∀ i : ℕ, Finite (B.X i).obj.V]

/-- Actual finite characters of the given chain terms, retaining contragredient action. -/
abbrev term (i : ℕ) := FieldLocalHomCharacter.characterRepresentation k (B.X i)

/-- The signed character differential is precomposition, with opposite scalars. -/
def differential (i : ℕ) : term k B i ⟶ term k B (i + 1) :=
  ((-1 : ℤ) ^ (i + 1)) •
    (ActualOppositeCharacter.finiteMap R Gal(AlgebraicClosure k/k)
      (N := FieldLocalHomCharacter.finiteInput k (B.X (i + 1)))
      (L := FieldLocalHomCharacter.finiteInput k (B.X i))
      (ObjectProperty.homMk (B.d (i + 1) i))).hom

theorem differential_sq (i : ℕ) :
    differential k B i ≫ differential k B (i + 1) = 0 := by sorry

def complex : CochainComplex (DiscreteModuleCat Rᵐᵒᵖ Gal(AlgebraicClosure k/k)) ℕ :=
  CochainComplex.of (term k B) (differential k B) (differential_sq k B)

variable (n : ℕ) [NeZero n]
variable (h : ActualRootsModule.Coeff.{u} n →+* R)
variable (hc : ∀ (a : ActualRootsModule.Coeff.{u} n) (r : R), h a * r = r * h a)
variable [(Spec (CommRingCat.of k)).smallEtaleTopology.HasSheafCompose (NoncommLocalHom.modules h)]
variable [(Spec (CommRingCat.of k)).smallEtaleTopology.HasSheafCompose
  (ModuleCat.restrictScalars (NoncommLocalHom.opScalarHom h hc))]

/-- Every component is the specified stalk-evaluation character map. The
cochain law is naturality of evaluation with the same explicit Hom signs. -/
def simpleIso :
    ((FieldModuleDescent.forward k Rᵐᵒᵖ).mapHomologicalComplex (ComplexShape.up ℕ)).obj
      (LocalHomSingleTarget.simple h hc (Spec (CommRingCat.of k))
        (FieldHomCochainComparison.fieldB B)
        (ResidualNormalizedRootsTrace.fieldTarget (k := k) n)) ≅ complex k B :=
  HomologicalComplex.Hom.isoOfComponents
    (fun i ↦ FieldLocalHomCharacter.discreteIso k n h hc (B.X i)) (by sorry)

/-- Connected comparison from the actual field-Hom trace target to signed
finite characters: project the unique surviving factor, then evaluate germs. -/
def iso : FieldHomNormalizedTrace.characterModel n h hc B ≅
    (complex k B).extend ComplexShape.embeddingUpNat :=
  ((FieldModuleDescent.forward k Rᵐᵒᵖ).mapHomologicalComplex (ComplexShape.up ℤ)).mapIso
    (LocalHomSingleTarget.iso h hc (Spec (CommRingCat.of k))
      (FieldHomCochainComparison.fieldB B)
      (ResidualNormalizedRootsTrace.fieldTarget (k := k) n)) ≪≫
  ComplexShape.embeddingUpNat.mapAppIso (FieldModuleDescent.forward k Rᵐᵒᵖ)
    (LocalHomSingleTarget.simple h hc (Spec (CommRingCat.of k))
      (FieldHomCochainComparison.fieldB B)
      (ResidualNormalizedRootsTrace.fieldTarget (k := k) n)) ≪≫
  (ComplexShape.embeddingUpNat.extendFunctor _).mapIso (simpleIso k B n h hc)

def completedIso :
    NoncommCompletedCochainTransport.cochain Rᵐᵒᵖ Gal(AlgebraicClosure k/k)
      (FieldHomNormalizedTrace.characterModel n h hc B) ≅
    NoncommCompletedCochainTransport.cochain Rᵐᵒᵖ Gal(AlgebraicClosure k/k)
      ((complex k B).extend ComplexShape.embeddingUpNat) :=
  ((NoncommPointwiseCompletedAction.functor Rᵐᵒᵖ Gal(AlgebraicClosure k/k)).mapHomologicalComplex
    (ComplexShape.up ℤ)).mapIso (iso k B n h hc)

end FieldCharacterCochain
