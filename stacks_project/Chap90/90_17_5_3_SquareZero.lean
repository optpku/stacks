module

public import Mathlib.Algebra.Module.RingHom
public import Mathlib.Algebra.Ring.Opposite
public import Mathlib.Algebra.TrivSqZeroExt.Basic
public import Mathlib.Algebra.TrivSqZeroExt.Ideal
public import Mathlib.RingTheory.Artinian.Module
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
public import stacks_project.Chap90.Definition_90_16_8_Predeformation

/-!
# Square-zero extensions `k[I]` in `ArtinianLocalAlgCat`

For a finite `k`-module `I`, the trivial square-zero extension `TrivSqZeroExt k I` bundles
as the object `k[I]` of `C_Λ`, together with the canonical projection onto the residue field
`k`. The kernel of a morphism `A' ⟶ A` annihilated by `m_{A'}` is such a module.
-/

@[expose] public section

open CategoryTheory IsLocalRing TrivSqZeroExt

universe u

namespace ArtinianLocalAlgCat

variable {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]

/-- The kernel of a morphism in `ArtinianLocalAlgCat` annihilated by `m_{A'}`. -/
abbrev kerModule {A' A : ArtinianLocalAlgCat Λ k} (f : A' ⟶ A)
    (h_ann : maximalIdeal A'.carrier * RingHom.ker f.hom.toRingHom = ⊥) : Type u :=
  RingHom.ker f.hom.toRingHom

/-- The residue identification of `A'` makes `ker f` into a `k`-module, using that
`m_{A'}` annihilates the kernel. -/
noncomputable instance instModule_kerModule {A' A : ArtinianLocalAlgCat Λ k} (f : A' ⟶ A)
    (h_ann : maximalIdeal A'.carrier * RingHom.ker f.hom.toRingHom = ⊥) :
    Module k (kerModule f h_ann) where
  smul c x :=
    ⟨Quotient.out (A'.residueFieldIso.symm c) * x.1, Ideal.mul_mem_left _ _ x.property⟩
  one_smul := sorry
  mul_smul := sorry
  smul_zero := sorry
  smul_add := sorry
  add_smul := sorry
  zero_smul := sorry

/-- The kernel of a morphism of Artinian local algebras annihilated by the maximal ideal is
a finite module over the residue field. -/
instance instModuleFinite_kerModule {A' A : ArtinianLocalAlgCat Λ k} (f : A' ⟶ A)
    (h_ann : maximalIdeal A'.carrier * RingHom.ker f.hom.toRingHom = ⊥) :
    Module.Finite k (kerModule f h_ann) := sorry

/-- Opposite scalars on a `k`-module, using that `k` is commutative. -/
instance (priority := 100) instModuleOp {I : Type u} [AddCommGroup I] [Module k I] :
    Module kᵐᵒᵖ I :=
  Module.compHom I ((RingHom.id k).fromOpposite mul_comm)

/-- Scalar actions of `k` and `kᵐᵒᵖ` agree on a `k`-module. -/
instance (priority := 100) instIsCentralScalar {I : Type u} [AddCommGroup I] [Module k I] :
    IsCentralScalar k I where
  op_smul_eq_smul _ _ := rfl

/-- The trivial square-zero extension is a `Λ`-algebra via the composite `Λ → k → k[I]`.
Priority is below the canonical `k`-algebra instance `algebra' k k I`. -/
instance (priority := 80) instAlgebra_squareZero {I : Type u} [AddCommGroup I] [Module k I] :
    Algebra Λ (TrivSqZeroExt k I) :=
  RingHom.toAlgebra ((algebraMap k (TrivSqZeroExt k I)).comp (algebraMap Λ k))

/-- The tower `Λ → k → TrivSqZeroExt k I`. -/
instance instIsScalarTower_squareZero {I : Type u} [AddCommGroup I] [Module k I] :
    IsScalarTower Λ k (TrivSqZeroExt k I) := sorry

/-- The trivial square-zero extension of a module over a field is a local ring. -/
instance instIsLocalRing_squareZero {I : Type u} [AddCommGroup I] [Module k I] :
    IsLocalRing (TrivSqZeroExt k I) := sorry

/-- The trivial square-zero extension of a finite module over a field is Artinian. -/
instance instIsArtinianRing_squareZero {I : Type u} [AddCommGroup I] [Module k I]
    [Module.Finite k I] : IsArtinianRing (TrivSqZeroExt k I) := sorry

/-- The coefficient projection of `TrivSqZeroExt k I` is a local homomorphism. -/
instance instIsLocalHom_fstHom {I : Type u} [AddCommGroup I] [Module k I] :
    IsLocalHom (fstHom k k I) := sorry

/-- The coefficient projection, as a `Λ`-algebra map, is local. -/
instance instIsLocalHom_fstHom_restrict {I : Type u} [AddCommGroup I] [Module k I] :
    IsLocalHom ((fstHom k k I).restrictScalars Λ) := sorry

/-- The underlying ring homomorphism of the coefficient projection is local. -/
instance instIsLocalHom_fstHom_restrict_toRingHom {I : Type u} [AddCommGroup I] [Module k I] :
    IsLocalHom ((fstHom k k I).restrictScalars Λ).toRingHom := sorry

variable (Λ k)

/-- Residue-field identification of `TrivSqZeroExt k I` with `k`, via the coefficient
projection and the inclusion of scalars. -/
noncomputable def squareZeroResidueFieldIso (I : Type u) [AddCommGroup I] [Module k I] :
    ResidueField (TrivSqZeroExt k I) ≃ₐ[Λ] k :=
  AlgEquiv.ofAlgHom
    { ResidueField.lift ((fstHom k k I).restrictScalars Λ).toRingHom with
      commutes' := sorry }
    ((Ideal.Quotient.mkₐ Λ (maximalIdeal (TrivSqZeroExt k I))).comp
      ((inlAlgHom k k I).restrictScalars Λ))
    sorry sorry

/-- The residue identification of `k[I]` sends the class of a square-zero extension to its
scalar coefficient. -/
theorem squareZeroResidueFieldIso_apply (I : Type u) [AddCommGroup I] [Module k I]
    (x : TrivSqZeroExt k I) :
    squareZeroResidueFieldIso Λ k I (IsLocalRing.residue (TrivSqZeroExt k I) x) = x.fst := sorry

/-- The trivial square-zero extension `TrivSqZeroExt k I`, viewed as an object of
`ArtinianLocalAlgCat Λ k`. -/
noncomputable def squareZero (I : Type u) [AddCommGroup I] [Module k I] [Module.Finite k I] :
    ArtinianLocalAlgCat Λ k :=
  of (TrivSqZeroExt k I) (squareZeroResidueFieldIso Λ k I)

/-- The bundled square-zero object has carrier `TrivSqZeroExt k I`. -/
theorem squareZero_carrier (I : Type u) [AddCommGroup I] [Module k I] [Module.Finite k I] :
    (squareZero Λ k I).carrier = TrivSqZeroExt k I := sorry

/-- The canonical projection `k[I] ⟶ k` in `ArtinianLocalAlgCat`. -/
noncomputable def squareZeroToResidue (I : Type u) [AddCommGroup I] [Module k I]
    [Module.Finite k I] : squareZero Λ k I ⟶ residue Λ k where
  hom := (fstHom k k I).restrictScalars Λ
  isLocalHom := sorry
  residue_compat := sorry

/-- The underlying algebra map of `squareZeroToResidue` is the coefficient projection. -/
theorem squareZeroToResidue_hom (I : Type u) [AddCommGroup I] [Module k I] [Module.Finite k I] :
    (squareZeroToResidue Λ k I).hom = (fstHom k k I).restrictScalars Λ := sorry

/-- The projection `k[I] ⟶ k` is surjective. -/
theorem squareZeroToResidue_surjective (I : Type u) [AddCommGroup I] [Module k I]
    [Module.Finite k I] : Function.Surjective (squareZeroToResidue Λ k I).hom := sorry

/-- The projection `k[I] ⟶ k` is a local `Λ`-algebra map compatible with residue
identifications. -/
theorem squareZeroToResidue_spec (I : Type u) [AddCommGroup I] [Module k I] [Module.Finite k I] :
    IsLocalHom (squareZeroToResidue Λ k I).hom ∧
      (residue Λ k).residueFieldIso.toAlgHom.comp
          (ResidueField.mapAlgHom (squareZeroToResidue Λ k I).hom) =
        (squareZero Λ k I).residueFieldIso.toAlgHom := sorry

end ArtinianLocalAlgCat
