module
public import ReasLib.AlgebraicGeometry.Scheme.Module.Etale.CurveComparison.LocalHomTranspose
public import ReasLib.AlgebraicGeometry.Scheme.Module.Etale.CurveComparison.NoncommLocalHomComplex
public import ReasLib.AlgebraicGeometry.Scheme.Module.Etale.CurveComparison.CompactDegreePlacement

@[expose] public section
open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme
noncomputable section
universe u

namespace LocalHomCurveTranspose
variable {A R : Type (u + 1)} [CommRing A] [Ring R]
variable (h : A →+* R) (hc : ∀ (a : A) (r : R), h a * r = r * h a)
variable (Y : Scheme.{u})
variable [Y.smallEtaleTopology.HasSheafCompose (NoncommLocalHom.modules h)]
variable [Y.smallEtaleTopology.HasSheafCompose
  (NoncommLocalHom.modules (NoncommLocalHom.opScalarHom h hc))]
variable [Y.smallEtaleTopology.HasSheafCompose (ModuleCat.restrictScalars (RingEquiv.opOp R).toRingHom)]
variable (L : ChainComplex (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} R)) ℕ)
variable (B : ChainComplex (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Rᵐᵒᵖ)) ℕ)
variable (J : CochainComplex (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} A)) ℕ)
variable (e : B.extend CompactRepresentation.curveDegreeEmbedding ⟶
  NoncommLocalHomComplex.integerComplex h hc Y L J)

abbrev restriction := sheafCompose Y.smallEtaleTopology
  (ModuleCat.restrictScalars (RingEquiv.opOp R).toRingHom)

instance restriction_additive : (restriction (R := R) Y).Additive := by sorry

/-- Read the actual (i,j) evaluation block of the supplied global sheaf map.
Both degree transports use proved integer/natural index equalities. -/
def block (i j : ℕ) (hij : i + j ≤ 2) :
    B.X j ⟶ NoncommLocalHom.obj h hc Y (L.X i) (J.X (2 - i - j)) :=
  (B.extendXIso CompactRepresentation.curveDegreeEmbedding (i := j) (i' := 2 - (j : ℤ)) rfl).inv ≫
  e.f (2 - (j : ℤ)) ≫
  ((NoncommLocalHomComplex.complex h hc Y L J).extendXIso ComplexShape.embeddingUpNat
    (i := 2 - j) (i' := 2 - (j : ℤ)) (by change ((2 - j : ℕ) : ℤ) = 2 - (j : ℤ); omega)).hom ≫
  NoncommLocalHomComplex.projection h hc Y L J (2 - j) ⟨i, by omega⟩ ≫
  NoncommLocalHom.postcomp h hc Y (eqToHom (congrArg J.X (by omega : 2 - j - i = 2 - i - j)))

/-- Transposition uses the Koszul sign (-1)^(i(2-j)), with the existing
balanced local evaluation and canonical double-opposite scalar normalization. -/
def transposeBlock (i j : ℕ) (hij : i + j ≤ 2) :=
  LocalHomTranspose.map h hc Y (L.X i) (B.X j) (J.X (2 - i - j))
    (((-1 : ℤ) ^ (i * (2 - j))) • block h hc Y L B J e i j hij)

/-- Assemble exactly the finite diagonal in transposed degree -i. -/
def degreeMap (i : ℕ) (hi : i ≤ 2) : L.X i ⟶
    (restriction (R := R) Y).obj
      (NoncommLocalHomComplex.degree (NoncommLocalHom.opScalarHom h hc)
        (NoncommLocalHom.opScalarHom_central h hc) Y B J (2 - i)) :=
  ObjectProperty.homMk
    { app := fun U ↦ ConcreteCategory.ofHom (C := ModuleCat.{u + 1} R)
        { toFun := fun m j ↦ ((transposeBlock h hc Y L B J e i j.val (by have := j.isLt; omega)).hom.app U).hom m
          map_add' := by sorry
          map_smul' := by sorry }
      naturality := by sorry }

/-- The transpose target is Kuhn's actual Hom complex shifted by +2,
with its double-opposite coefficients returned to R. -/
def target := ((restriction (R := R) Y).mapHomologicalComplex (ComplexShape.up ℤ)).obj
  (NoncommLocalHomComplex.shiftedComplex (NoncommLocalHom.opScalarHom h hc)
    (NoncommLocalHom.opScalarHom_central h hc) Y B J)

/-- Actual global cochain transpose. Only degrees -2,-1,0 overlap: the source
is zero above 0 and the target is zero below -2. All other components are zero
for this support reason, not an asserted zero-isomorphism. -/
def map : L.extend ComplexShape.embeddingDownNat ⟶ target h hc Y B J where
  f i := if hi : -2 ≤ i ∧ i ≤ 0 then
      (L.extendXIso ComplexShape.embeddingDownNat (i := (-i).toNat) (i' := i)
        (by change -(((-i).toNat : ℕ) : ℤ) = i; omega)).hom ≫
      degreeMap h hc Y L B J e (-i).toNat (by omega) ≫
      (restriction (R := R) Y).map
        (((NoncommLocalHomComplex.complex (NoncommLocalHom.opScalarHom h hc)
          (NoncommLocalHom.opScalarHom_central h hc) Y B J).extendXIso
          ComplexShape.embeddingUpNat (i := 2 - (-i).toNat) (i' := i + 2)
          (by change ((2 - (-i).toNat : ℕ) : ℤ) = i + 2; omega)).inv ≫
          (CochainComplex.shiftFunctorObjXIso
            (NoncommLocalHomComplex.integerComplex (NoncommLocalHom.opScalarHom h hc)
              (NoncommLocalHom.opScalarHom_central h hc) Y B J)
            (2 : ℤ) i (i + 2) rfl).inv)
    else 0
  comm' := by sorry

end LocalHomCurveTranspose
