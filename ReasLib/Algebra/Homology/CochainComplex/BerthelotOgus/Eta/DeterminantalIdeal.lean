module

public import Mathlib.Algebra.Homology.Embedding.CochainComplex
public import ReasLib.Algebra.Homology.CochainComplex.BerthelotOgus.Eta.Int.DeterminantalIdeal

/-!
# Determinantal ideals for nonnegative Berthelot-Ogus eta presentations

The nonnegative construction is defined directly on an `ℕ`-indexed cochain complex.  Extension by
zero to integer degrees is exposed only through canonical comparison API, so the public datum does
not depend on private instances or a chosen bridge representation.
@stack 0GSU
-/

@[expose] public section

open CategoryTheory ComplexShape

noncomputable section

universe u v w

namespace CochainComplex.BerthelotOgus.Nat

variable {A : Type u} [CommRing A]

/-- The map `(f, d i (i + 1))` defining the degree-`i` eta presentation of a nonnegative
complex. -/
@[stacks 0F7V "nonnegative Berthelot-Ogus eta presentation map"]
abbrev etaPresentationMap
    (f : A) (K : CochainComplex (ModuleCat.{v} A) ℕ) (i : ℕ) :
    K.X i →ₗ[A] K.X i × K.X (i + 1) :=
  HomologicalComplex.ScalarPresentation.map f K i (i + 1)

/-- The nonnegative eta presentation quotient in degree `i`. -/
@[stacks 0F7V "nonnegative Berthelot-Ogus eta presentation quotient"]
abbrev etaPresentationQuotient
    (f : A) (K : CochainComplex (ModuleCat.{v} A) ℕ) (i : ℕ) :=
  HomologicalComplex.ScalarPresentation.quotient f K i (i + 1)

/-- The degree-`i` Berthelot-Ogus determinantal ideal of a nonnegative cochain complex. -/
@[stacks 0F7V "nonnegative Berthelot-Ogus eta determinantal ideal"]
def etaDeterminantalIdeal
    (f : A) (K : CochainComplex (ModuleCat.{v} A) ℕ) (i : ℕ)
    [Module.Finite A (K.X i)]
    [Module.Free A (K.X (i + 1))] [Module.Finite A (K.X (i + 1))] : Ideal A :=
  HomologicalComplex.ScalarPresentation.fittingIdeal f K i (i + 1)

/-- The nonnegative eta determinantal ideal commutes with extension of scalars, under only the
degreewise finiteness and freeness needed to define it. -/
@[stacks 0GSU "base change of the nonnegative Berthelot-Ogus eta determinantal ideal"]
theorem etaDeterminantalIdeal_baseChange
    {B : Type w} [CommRing B] [Algebra A B]
    (f : A) (K : CochainComplex (ModuleCat.{v} A) ℕ) (i : ℕ)
    [Module.Finite A (K.X i)]
    [Module.Free A (K.X (i + 1))] [Module.Finite A (K.X (i + 1))] :
    etaDeterminantalIdeal (algebraMap A B f)
        (((ModuleCat.extendScalars (algebraMap A B)).mapHomologicalComplex (ComplexShape.up ℕ)).obj
          K) i =
      Ideal.map (algebraMap A B) (etaDeterminantalIdeal f K i) := sorry

/-- Extension by zero preserves freeness in a displayed nonnegative degree. -/
noncomputable instance extendModuleFree
    (K : CochainComplex (ModuleCat.{v} A) ℕ) (i : ℕ) [Module.Free A (K.X i)] :
    Module.Free A ((K.extend embeddingUpNat).X (i : ℤ)) := sorry

/-- Extension by zero preserves freeness at the successor written in integer arithmetic. -/
noncomputable instance extendModuleFree_succ
    (K : CochainComplex (ModuleCat.{v} A) ℕ) (i : ℕ)
    [Module.Free A (K.X (i + 1))] :
    Module.Free A ((K.extend embeddingUpNat).X ((i : ℤ) + 1)) := sorry

/-- Extension by zero preserves finiteness in a displayed nonnegative degree. -/
noncomputable instance extendModuleFinite
    (K : CochainComplex (ModuleCat.{v} A) ℕ) (i : ℕ) [Module.Finite A (K.X i)] :
    Module.Finite A ((K.extend embeddingUpNat).X (i : ℤ)) := sorry

/-- Extension by zero preserves finiteness at the successor written in integer arithmetic. -/
noncomputable instance extendModuleFinite_succ
    (K : CochainComplex (ModuleCat.{v} A) ℕ) (i : ℕ)
    [Module.Finite A (K.X (i + 1))] :
    Module.Finite A ((K.extend embeddingUpNat).X ((i : ℤ) + 1)) := sorry

/-- The embedding of nonnegative degrees into integer degrees sends `i` to its integer cast. -/
@[simp]
theorem embeddingUpNat_apply (i : ℕ) : embeddingUpNat.f i = (i : ℤ) := sorry

/-- The embedding of nonnegative degrees into integer degrees preserves successors. -/
@[simp]
theorem embeddingUpNat_succ (i : ℕ) : embeddingUpNat.f (i + 1) = (i : ℤ) + 1 := sorry

/-- The two degree components of extension by zero identify the integer presentation target with
the original nonnegative presentation target. -/
noncomputable def extendTargetEquiv
    (K : CochainComplex (ModuleCat.{v} A) ℕ) (i : ℕ) :
    ((K.extend embeddingUpNat).X (i : ℤ) ×
        (K.extend embeddingUpNat).X ((i : ℤ) + 1)) ≃ₗ[A]
      K.X i × K.X (i + 1) :=
  LinearEquiv.prodCongr
    (K.extendXIso embeddingUpNat (embeddingUpNat_apply i)).toLinearEquiv
    (K.extendXIso embeddingUpNat (embeddingUpNat_succ i)).toLinearEquiv

/-- The extension target equivalence applies the two canonical extension component
isomorphisms coordinatewise. -/
@[simp]
theorem extendTargetEquiv_apply
    (K : CochainComplex (ModuleCat.{v} A) ℕ) (i : ℕ)
    (x : (K.extend embeddingUpNat).X (i : ℤ))
    (y : (K.extend embeddingUpNat).X ((i : ℤ) + 1)) :
    extendTargetEquiv K i (x, y) =
      ((K.extendXIso embeddingUpNat (embeddingUpNat_apply i)).hom x,
        (K.extendXIso embeddingUpNat (embeddingUpNat_succ i)).hom y) := sorry

/-- The inverse extension target equivalence applies the inverses of the two canonical extension
component isomorphisms coordinatewise. -/
@[simp]
theorem extendTargetEquiv_symm_apply
    (K : CochainComplex (ModuleCat.{v} A) ℕ) (i : ℕ)
    (x : K.X i) (y : K.X (i + 1)) :
    (extendTargetEquiv K i).symm (x, y) =
      ((K.extendXIso embeddingUpNat (embeddingUpNat_apply i)).inv x,
        (K.extendXIso embeddingUpNat (embeddingUpNat_succ i)).inv y) := sorry

/-- The extension-by-zero target equivalence intertwines the integer and nonnegative eta
presentation maps. -/
theorem extendTargetEquiv_map
    (f : A) (K : CochainComplex (ModuleCat.{v} A) ℕ) (i : ℕ) (x : K.X i) :
    extendTargetEquiv K i
        (CochainComplex.BerthelotOgus.Int.etaPresentationMap f (K.extend embeddingUpNat) (i : ℤ)
          ((K.extendXIso embeddingUpNat (embeddingUpNat_apply i)).inv x)) =
      etaPresentationMap f K i x := sorry

/-- The extension-by-zero target equivalence carries the integer presentation range onto the
nonnegative presentation range. -/
theorem extendTargetEquiv_range
    (f : A) (K : CochainComplex (ModuleCat.{v} A) ℕ) (i : ℕ) :
    (LinearMap.range
        (CochainComplex.BerthelotOgus.Int.etaPresentationMap f
          (K.extend embeddingUpNat) (i : ℤ))).map
        (extendTargetEquiv K i).toLinearMap =
      LinearMap.range (etaPresentationMap f K i) := sorry

/-- The eta presentation quotient of a nonnegative complex agrees with that of its extension by
zero. -/
noncomputable def quotientExtendIso
    (f : A) (K : CochainComplex (ModuleCat.{v} A) ℕ) (i : ℕ) :
    CochainComplex.BerthelotOgus.Int.etaPresentationQuotient f
        (K.extend embeddingUpNat) (i : ℤ) ≃ₗ[A]
      etaPresentationQuotient f K i :=
  Submodule.Quotient.equiv
    (LinearMap.range
      (CochainComplex.BerthelotOgus.Int.etaPresentationMap f
        (K.extend embeddingUpNat) (i : ℤ)))
    (LinearMap.range (etaPresentationMap f K i))
    (extendTargetEquiv K i)
    (extendTargetEquiv_range f K i)

/-- The extension comparison of eta presentation quotients acts on representatives through the
two canonical component isomorphisms. -/
@[simp]
theorem quotientExtendIso_mk
    (f : A) (K : CochainComplex (ModuleCat.{v} A) ℕ) (i : ℕ)
    (x : (K.extend embeddingUpNat).X (i : ℤ) ×
      (K.extend embeddingUpNat).X ((i : ℤ) + 1)) :
    quotientExtendIso f K i (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk (extendTargetEquiv K i x) := sorry

/-- The inverse extension comparison acts on representatives through the inverse component
isomorphisms. -/
@[simp]
theorem quotientExtendIso_symm_mk
    (f : A) (K : CochainComplex (ModuleCat.{v} A) ℕ) (i : ℕ)
    (x : K.X i × K.X (i + 1)) :
    (quotientExtendIso f K i).symm (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk ((extendTargetEquiv K i).symm x) := sorry

/-- The direct nonnegative eta determinantal ideal agrees with the integer owner after extension
by zero. -/
theorem etaDeterminantalIdeal_extend
    (f : A) (K : CochainComplex (ModuleCat.{v} A) ℕ) (i : ℕ)
    [Module.Finite A (K.X i)]
    [Module.Free A (K.X (i + 1))] [Module.Finite A (K.X (i + 1))] :
    CochainComplex.BerthelotOgus.Int.etaDeterminantalIdeal f (K.extend embeddingUpNat) (i : ℤ) =
      etaDeterminantalIdeal f K i := sorry

end CochainComplex.BerthelotOgus.Nat
