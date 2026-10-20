module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Graded.Algebra

/-!
# Reindexing graded algebra sheaves

An additive homomorphism of grading monoids pulls a graded algebra sheaf back to the source
grading monoid.  The unit and multiplication are transported along preservation of zero and
addition.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u v

namespace SheafOfModules.RingedSite.GradedAlgebraSheaf

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable {𝒪 : Sheaf J CommRingCat.{max u v}}
variable {ι κ : Type} [AddMonoid ι] [AddMonoid κ]

/-- The unit of a graded algebra sheaf transported to degree zero along an additive homomorphism. -/
noncomputable def reindexOne
    (𝒜 : GradedAlgebraSheaf 𝒪 κ) (φ : ι →+ κ) (U : Cᵒᵖ) :
    (𝒜 (φ 0)).val.obj U :=
  Eq.mp
    (congrArg (fun k : κ ↦ ((𝒜 k).val.obj U : Type (max u v))) φ.map_zero.symm)
    (𝒜.one U)

/-- The multiplication of a graded algebra sheaf transported along preservation of addition. -/
noncomputable def reindexMul
    (𝒜 : GradedAlgebraSheaf 𝒪 κ) (φ : ι →+ κ) (U : Cᵒᵖ) (n m : ι) :
    (𝒜 (φ n)).val.obj U →ₗ[𝒪.obj.obj U]
      (𝒜 (φ m)).val.obj U →ₗ[𝒪.obj.obj U] (𝒜 (φ (n + m))).val.obj U :=
  Eq.mp
    (congrArg
      (fun k : κ ↦
        (𝒜 (φ n)).val.obj U →ₗ[𝒪.obj.obj U]
          (𝒜 (φ m)).val.obj U →ₗ[𝒪.obj.obj U] (𝒜 k).val.obj U)
      (φ.map_add n m).symm)
    (𝒜.mul U (φ n) (φ m))

/-- The transported unit commutes with restriction. -/
theorem reindex_map_one
    (𝒜 : GradedAlgebraSheaf 𝒪 κ) (φ : ι →+ κ)
    {U V : Cᵒᵖ} (f : U ⟶ V) :
    ((𝒜 (φ 0)).val.map f).hom (reindexOne 𝒜 φ U) = reindexOne 𝒜 φ V := sorry

/-- The transported multiplication commutes with restriction. -/
theorem reindex_map_mul
    (𝒜 : GradedAlgebraSheaf 𝒪 κ) (φ : ι →+ κ)
    {U V : Cᵒᵖ} (f : U ⟶ V) (n m : ι)
    (a : (𝒜 (φ n)).val.obj U) (b : (𝒜 (φ m)).val.obj U) :
    ((𝒜 (φ (n + m))).val.map f).hom (reindexMul 𝒜 φ U n m a b) =
      reindexMul 𝒜 φ V n m
        (((𝒜 (φ n)).val.map f).hom a) (((𝒜 (φ m)).val.map f).hom b) := sorry

/-- The transported multiplication is associative. -/
theorem reindex_mul_assoc
    (𝒜 : GradedAlgebraSheaf 𝒪 κ) (φ : ι →+ κ)
    (U : Cᵒᵖ) (i j k : ι)
    (a : (𝒜 (φ i)).val.obj U) (b : (𝒜 (φ j)).val.obj U)
    (c : (𝒜 (φ k)).val.obj U) :
    HEq (reindexMul 𝒜 φ U (i + j) k (reindexMul 𝒜 φ U i j a b) c)
      (reindexMul 𝒜 φ U i (j + k) a (reindexMul 𝒜 φ U j k b c)) := sorry

/-- The transported unit is a left identity. -/
theorem reindex_one_mul
    (𝒜 : GradedAlgebraSheaf 𝒪 κ) (φ : ι →+ κ)
    (U : Cᵒᵖ) (n : ι) (a : (𝒜 (φ n)).val.obj U) :
    HEq (reindexMul 𝒜 φ U 0 n (reindexOne 𝒜 φ U) a) a := sorry

/-- The transported unit is a right identity. -/
theorem reindex_mul_one
    (𝒜 : GradedAlgebraSheaf 𝒪 κ) (φ : ι →+ κ)
    (U : Cᵒᵖ) (n : ι) (a : (𝒜 (φ n)).val.obj U) :
    HEq (reindexMul 𝒜 φ U n 0 a (reindexOne 𝒜 φ U)) a := sorry

/-- Pull a graded algebra sheaf back along an additive homomorphism of grading monoids. -/
noncomputable def reindex
    (𝒜 : GradedAlgebraSheaf 𝒪 κ) (φ : ι →+ κ) : GradedAlgebraSheaf 𝒪 ι where
  obj n := 𝒜 (φ n)
  one := reindexOne 𝒜 φ
  mul := reindexMul 𝒜 φ
  map_one := reindex_map_one 𝒜 φ
  map_mul := reindex_map_mul 𝒜 φ
  mul_assoc := reindex_mul_assoc 𝒜 φ
  one_mul := reindex_one_mul 𝒜 φ
  mul_one := reindex_mul_one 𝒜 φ

/-- The degree-`n` piece of a reindexed graded algebra is the piece indexed by `φ n`. -/
@[simp]
theorem reindex_apply
    (𝒜 : GradedAlgebraSheaf 𝒪 κ) (φ : ι →+ κ) (n : ι) :
    reindex 𝒜 φ n = 𝒜 (φ n) := rfl

/-- The unit of a reindexed graded algebra is the explicitly transported unit. -/
theorem reindex_one
    (𝒜 : GradedAlgebraSheaf 𝒪 κ) (φ : ι →+ κ) (U : Cᵒᵖ) :
    (reindex 𝒜 φ).one U = reindexOne 𝒜 φ U := rfl

/-- Multiplication in a reindexed graded algebra is the explicitly transported multiplication. -/
theorem reindex_mul
    (𝒜 : GradedAlgebraSheaf 𝒪 κ) (φ : ι →+ κ)
    (U : Cᵒᵖ) (n m : ι) :
    (reindex 𝒜 φ).mul U n m = reindexMul 𝒜 φ U n m := rfl

/-- The `d`-Veronese reindexing of an integer-graded algebra sheaf. -/
noncomputable def veronese
    (𝒜 : GradedAlgebraSheaf 𝒪 ℤ) (d : ℕ) : GradedAlgebraSheaf 𝒪 ℤ :=
  reindex 𝒜 (AddMonoidHom.mulRight (Int.ofNat d))

/-- The degree-`n` piece of the `d`-Veronese reindexing is the degree-`n * d` piece. -/
@[simp]
theorem veronese_apply
    (𝒜 : GradedAlgebraSheaf 𝒪 ℤ) (d : ℕ) (n : ℤ) :
    veronese 𝒜 d n = 𝒜 (n * Int.ofNat d) := rfl

end SheafOfModules.RingedSite.GradedAlgebraSheaf
