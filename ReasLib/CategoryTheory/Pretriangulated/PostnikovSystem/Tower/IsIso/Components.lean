module

public import ReasLib.CategoryTheory.Iso.Explicit
public import ReasLib.CategoryTheory.Pretriangulated.PostnikovSystem.Tower.IsIso.Basic

/-!
# Auxiliary Component Isomorphisms of Sequential Postnikov Towers

This leaf turns the explicitly supplied auxiliary part of a levelwise-invertibility
certificate into component isomorphisms. Consumers can therefore use these inverses
without installing proof-local `IsIso` instances.
-/

@[expose] public section

open CategoryTheory.Pretriangulated

noncomputable section

universe v u

namespace CategoryTheory.PostnikovSystem.Tower

variable {D : Type u} [Category.{v} D] [Limits.HasZeroObject D] [HasShift D ℤ] [Preadditive D]
  [∀ k : ℤ, Functor.Additive (shiftFunctor D k)] [Pretriangulated D]
variable {T T' : Tower D}

namespace Hom.IsLevelwiseIso

/-- The auxiliary-object isomorphism determined by a levelwise-invertible tower morphism. -/
@[stacks 0D8Z "auxiliary-object isomorphism of a levelwise Postnikov-tower isomorphism"]
noncomputable def yIso {f : T ⟶ T'} (hf : f.IsLevelwiseIso) (n : ℕ) :
    T.Y n ≅ T'.Y n :=
  (hf n).toIso

/-- The forward map of `yIso` is the corresponding auxiliary-object component. -/
@[simp, stacks 0D8Z]
theorem yIso_hom {f : T ⟶ T'} (hf : f.IsLevelwiseIso) (n : ℕ) :
    (hf.yIso n).hom = f.yMap n := sorry

/-- The inverse map of `yIso` is the inverse of the corresponding auxiliary-object component. -/
@[simp, stacks 0D8Z]
theorem yIso_inv {f : T ⟶ T'} (hf : f.IsLevelwiseIso) (n : ℕ) :
    (hf.yIso n).inv = (hf n).toIso.inv := sorry

/-- The auxiliary-object isomorphism induced by the identity tower morphism is the identity
isomorphism. -/
@[simp, stacks 0D8Z]
theorem id_yIso (T : Tower D) (n : ℕ) :
    ((Hom.IsLevelwiseIso.id T).yIso n) = Iso.refl (T.Y n) := sorry

/-- The auxiliary-object isomorphism induced by a composite is the composite of the
auxiliary-object isomorphisms. -/
@[simp, stacks 0D8Z]
theorem comp_yIso {T'' : Tower D} {f : T ⟶ T'} {g : T' ⟶ T''}
    (hf : f.IsLevelwiseIso) (hg : g.IsLevelwiseIso) (n : ℕ) :
    ((hf.comp hg).yIso n) = (hf.yIso n).trans (hg.yIso n) := sorry

/-- An auxiliary-object component followed by the inverse of its explicit component
isomorphism is the identity. -/
@[simp, stacks 0D8Z]
theorem hom_inv_id {f : T ⟶ T'} (hf : f.IsLevelwiseIso) (n : ℕ) :
    f.yMap n ≫ (hf.yIso n).inv = 𝟙 (T.Y n) := sorry

/-- The inverse of an explicit component isomorphism followed by its auxiliary-object
component is the identity. -/
@[simp, stacks 0D8Z]
theorem inv_hom_id {f : T ⟶ T'} (hf : f.IsLevelwiseIso) (n : ℕ) :
    (hf.yIso n).inv ≫ f.yMap n = 𝟙 (T'.Y n) := sorry

end Hom.IsLevelwiseIso

end CategoryTheory.PostnikovSystem.Tower
