module

public import Mathlib.CategoryTheory.Limits.Shapes.FiniteProducts
public import Mathlib.CategoryTheory.Limits.Shapes.ZeroMorphisms
public import ReasLib.CategoryTheory.InverseSystem.MittagLeffler
public import ReasLib.CategoryTheory.ObjectProperty.Cover

/-!
# Mittag-Leffler Envelopes

Finite prefix products turn any sequential inverse system into a Mittag-Leffler system with a
monomorphic comparison map.  This leaf owns the concrete prefix-product tower, its comparison
morphism, and the resulting object-property interface.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe v u

namespace CategoryTheory.SequentialInverseSystem

variable {A : Type u} [Category.{v} A]

namespace FiniteProductEnvelope

section FiniteProducts

variable [HasFiniteProducts A]

/-- The product of the first `n + 1` stages of a sequential inverse system. -/
noncomputable abbrev obj (F : SequentialInverseSystem A) (n : ℕ) : A :=
  ∏ᶜ fun i : Fin (n + 1) ↦ F.obj (op (i : ℕ))

/-- The projection which drops the final coordinate of consecutive prefix products. -/
noncomputable def drop (F : SequentialInverseSystem A) (n : ℕ) :
    obj F (n + 1) ⟶ obj F n :=
  Pi.lift fun i ↦
    Pi.π (fun j : Fin (n + 2) ↦ F.obj (op (j : ℕ))) i.castSucc

/-- The sequential inverse system of finite prefix products. -/
noncomputable def tower (F : SequentialInverseSystem A) : SequentialInverseSystem A :=
  Functor.ofOpSequence (drop F)

/-- The successor transition of the prefix-product tower is its coordinate-dropping map. -/
theorem tower_step (F : SequentialInverseSystem A) (n : ℕ) :
    (tower F).stepMap n = drop F n := sorry

/-- The map from the `n`th stage of a system into its finite prefix product. -/
noncomputable def ιApp (F : SequentialInverseSystem A) (n : ℕ) :
    F.obj (op n) ⟶ obj F n :=
  Pi.lift fun i ↦ F.transitionMap (Nat.le_of_lt_succ i.isLt)

/-- The naturality identity for the finite-prefix comparison maps. -/
theorem ιApp_naturality (F : SequentialInverseSystem A) (n : ℕ) :
    F.map (homOfLE (Nat.le_add_right n 1)).op ≫ ιApp F n =
      ιApp F (n + 1) ≫ (tower F).map (homOfLE (Nat.le_add_right n 1)).op := sorry

/-- The comparison from a sequential inverse system to its finite prefix-product tower. -/
noncomputable def ι (F : SequentialInverseSystem A) : F ⟶ tower F :=
  NatTrans.ofOpSequence (fun n ↦ ιApp F n) (fun n ↦ ιApp_naturality F n)

/-- The `n`th component of the finite-prefix comparison is the corresponding product lift. -/
theorem ι_app (F : SequentialInverseSystem A) (n : ℕ) :
    (ι F).app (op n) = ιApp F n := sorry

/-- Projection to the final factor of a finite prefix product. -/
noncomputable def retraction (F : SequentialInverseSystem A) (n : ℕ) :
    obj F n ⟶ F.obj (op n) :=
  Pi.π (fun i : Fin (n + 1) ↦ F.obj (op (i : ℕ))) (Fin.last n)

/-- The finite-prefix comparison at a stage is split by its final-coordinate projection. -/
theorem ιApp_comp_retraction (F : SequentialInverseSystem A) (n : ℕ) :
    ιApp F n ≫ retraction F n = 𝟙 _ := sorry

/-- Each component of the finite-prefix comparison is a split monomorphism. -/
instance ιApp_isSplitMono (F : SequentialInverseSystem A) (n : ℕ) :
    IsSplitMono (ιApp F n) := sorry

/-- The finite-prefix comparison is monomorphic. -/
instance ι_mono (F : SequentialInverseSystem A) : Mono (ι F) := sorry

end FiniteProducts

section ZeroMorphisms

variable [HasFiniteProducts A] [HasZeroMorphisms A]

/-- The extension of a finite prefix product by a zero final coordinate. -/
noncomputable def zeroExtension (F : SequentialInverseSystem A) (n : ℕ) :
    obj F n ⟶ obj F (n + 1) :=
  Pi.lift fun i ↦
    Fin.lastCases
      (0 : obj F n ⟶ F.obj (op (n + 1)))
      (fun j ↦ Pi.π (fun k : Fin (n + 1) ↦ F.obj (op (k : ℕ))) j)
      i

/-- Extending by zero is a section of the coordinate-dropping map. -/
theorem zeroExtension_comp_drop (F : SequentialInverseSystem A) (n : ℕ) :
    zeroExtension F n ≫ drop F n = 𝟙 _ := sorry

/-- Every transition in the finite prefix-product tower is a split epimorphism. -/
instance drop_isSplitEpi (F : SequentialInverseSystem A) (n : ℕ) :
    IsSplitEpi (drop F n) := sorry

end ZeroMorphisms

section MittagLeffler

variable [HasFiniteProducts A] [HasZeroMorphisms A] [HasImages A]

/-- The finite prefix-product tower satisfies the Mittag-Leffler condition. -/
theorem isMittagLeffler (F : SequentialInverseSystem A) :
    (tower F).IsMittagLeffler := sorry

end MittagLeffler

end FiniteProductEnvelope

variable [HasImages A]

/-- Every sequential inverse system embeds monomorphically into a Mittag-Leffler system whenever
the ambient category has zero morphisms, finite products, and images. -/
instance IsMittagLeffler.hasMonoEmbedding [HasZeroMorphisms A] [HasFiniteProducts A] :
    ObjectProperty.HasMonoEmbedding
      (fun F : SequentialInverseSystem A ↦ F.IsMittagLeffler) := sorry

end CategoryTheory.SequentialInverseSystem
