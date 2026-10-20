module

public import Mathlib.Algebra.Module.RingHom
public import Mathlib.RingTheory.Artinian.Module
public import ReasLib.AlgebraicGeometry.FormalDeformation.ArtinianLocal.Residue

/-!
# Residue-field modules on annihilated kernels of Artinian local algebra morphisms
-/

@[expose] public section

open CategoryTheory IsLocalRing

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

/-- Multiplication by any representative of a residue scalar computes its action on an
annihilated kernel. -/
theorem kerModule_smul_eq {A' A : ArtinianLocalAlgCat Λ k} (f : A' ⟶ A)
    (h_ann : maximalIdeal A'.carrier * RingHom.ker f.hom.toRingHom = ⊥)
    (c : k) (r : A'.carrier) (hr : A'.residueFieldIso (IsLocalRing.residue A'.carrier r) = c)
    (i : kerModule f h_ann) :
    (c • i).1 = r * i.1 := sorry

end ArtinianLocalAlgCat
