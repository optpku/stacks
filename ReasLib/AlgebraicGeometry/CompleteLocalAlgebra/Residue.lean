module

public import ReasLib.AlgebraicGeometry.CompleteLocalAlgebra.Basic
public import ReasLib.AlgebraicGeometry.Scheme.Artinian.ResidueFactorization

@[expose] public section

open CategoryTheory AlgebraicGeometry Functor IsLocalRing

noncomputable section

universe u

namespace AlgebraicGeometry.CompleteLocalSAlgebra

variable {S : Scheme.{u}}

/-- Canonical morphism `Spec(κ(A)) ⟶ Spec(A)` induced by the residue map. -/
def residueToSpec (A : CompleteLocalSAlgebra S) :
    Spec (CommRingCat.of (ResidueField A.carrier)) ⟶
      Spec (CommRingCat.of A.carrier) :=
  Spec.map (CommRingCat.ofHom (residue A.carrier))

/-- Structure morphism `Spec(κ(A)) ⟶ S` of the residue field of `A`. -/
def residueToS (A : CompleteLocalSAlgebra S) :
    Spec (CommRingCat.of (ResidueField A.carrier)) ⟶ S :=
  A.residueToSpec ≫ A.toS

/-- `residueToS` is the residue-field spectrum of `A` over `S`. -/
theorem residueToS_eq (A : CompleteLocalSAlgebra S) :
    A.residueToS =
      Spec.map (CommRingCat.ofHom (residue A.carrier)) ≫ A.toS := rfl

/-- The residue-field point of a complete local `S`-algebra remains locally of
finite type over `S`. -/
instance instLocallyOfFiniteType_residueToS (A : CompleteLocalSAlgebra S) :
    LocallyOfFiniteType A.residueToS :=
  A.residue_locallyOfFiniteType

/-- Residue morphism `Spec(κ(A)) ⟶ Spec(A)` in `Over S`. -/
def residueOverHom (A : CompleteLocalSAlgebra S) :
    Over.mk A.residueToS ⟶ Over.mk A.toS :=
  Over.homMk A.residueToSpec rfl

/-- The underlying scheme morphism of `residueOverHom` is `residueToSpec`. -/
theorem residueOverHom_left (A : CompleteLocalSAlgebra S) :
    (A.residueOverHom).left = A.residueToSpec := rfl

/-- The first truncation of `A` is the residue-field spectrum of `A` over `S`. -/
theorem stageOver_zero_eq (A : CompleteLocalSAlgebra S) :
    A.stageOver 0 = Over.mk A.residueToS := sorry

/-- The residue-field identification commutes with the structure maps to the base. -/
theorem residueStageHom_over {A : CompleteLocalSAlgebra S} {k : Type u} [Field k]
    {σ : Spec (CommRingCat.of k) ⟶ S} (e : ResidueField A.carrier ≃+* k)
    (h : residueSpecMap e ≫ A.toS = σ) :
    Spec.map (CommRingCat.ofHom e.toRingHom) ≫ A.residueToS = σ := sorry

/-- The morphism `Spec(k) ⟶ Spec(κ(A))` in `Over S` induced by a residue-field
identification compatible with the structure morphisms to `S`. -/
def residueStageHom {A : CompleteLocalSAlgebra S} {k : Type u} [Field k]
    {σ : Spec (CommRingCat.of k) ⟶ S} (e : ResidueField A.carrier ≃+* k)
    (h : residueSpecMap e ≫ A.toS = σ) :
    Over.mk σ ⟶ Over.mk A.residueToS :=
  Over.homMk (Spec.map (CommRingCat.ofHom e.toRingHom)) (residueStageHom_over e h)

/-- `residueStageHom` is `Spec` of the residue-field identification. -/
theorem residueStageHom_left {A : CompleteLocalSAlgebra S} {k : Type u} [Field k]
    {σ : Spec (CommRingCat.of k) ⟶ S} (e : ResidueField A.carrier ≃+* k)
    (h : residueSpecMap e ≫ A.toS = σ) :
    (residueStageHom e h).left = Spec.map (CommRingCat.ofHom e.toRingHom) := rfl

end AlgebraicGeometry.CompleteLocalSAlgebra
