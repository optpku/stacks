module

public import ReasLib.CategoryTheory.Monoidal.Bimod.Tensor

/-!
# Associativity of iterated balanced tensor functors

Tensoring on the right first with `Q` and then with `P` is naturally isomorphic to tensoring
with the balanced tensor product `Q ⊗_T P`.  The components are Mathlib's bimodule associator
`Bimod.associatorBimod`.
-/

@[expose] public section

open CategoryTheory.Limits

noncomputable section

universe u v

namespace CategoryTheory.Bimod

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]
variable [HasCoequalizers C]
variable [∀ X : C, PreservesColimitsOfSize.{0, 0} (MonoidalCategory.tensorLeft X)]
variable [∀ X : C, PreservesColimitsOfSize.{0, 0} (MonoidalCategory.tensorRight X)]
variable {R S T U : Mon C}

/-- The bimodule associator is natural in the left variable of an iterated balanced tensor. -/
@[reassoc]
theorem tensorRightCompIso_naturality (Q : Bimod S T) (P : Bimod T U)
    {M M' : Bimod R S} (f : M ⟶ M') :
    (tensorRight Q ⋙ tensorRight P).map f ≫ (_root_.Bimod.associatorBimod M' Q P).hom =
      (_root_.Bimod.associatorBimod M Q P).hom ≫ (tensorRight (Q.tensorBimod P)).map f := sorry

/-- Iterated balanced tensoring `(- ⊗_S Q) ⊗_T P` is naturally isomorphic to balanced
tensoring with `Q ⊗_T P`, with components the bimodule associator. -/
def tensorRightCompIso (Q : Bimod S T) (P : Bimod T U) :
    (tensorRight Q ⋙ tensorRight P : Bimod R S ⥤ Bimod R U) ≅
      tensorRight (Q.tensorBimod P) :=
  NatIso.ofComponents (fun M ↦ _root_.Bimod.associatorBimod M Q P)
    (fun f ↦ tensorRightCompIso_naturality Q P f)

/-- The components of `tensorRightCompIso` are the bimodule associators. -/
@[simp]
theorem tensorRightCompIso_app (Q : Bimod S T) (P : Bimod T U) (M : Bimod R S) :
    (tensorRightCompIso Q P).app M = _root_.Bimod.associatorBimod M Q P := rfl

end CategoryTheory.Bimod

end
