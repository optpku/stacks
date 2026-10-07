module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Pullback.Monoidal
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.TensorPower.Comparison
public import ReasLib.AlgebraicGeometry.Scheme.Module.Monoidal
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Monoidal pullback of scheme modules

The pullback functor on scheme modules is the specialization of the strong-monoidal pullback
constructed for commutative ringed sites.  This file is the scheme-level owner and
exposes the unit and tensor comparisons without duplicating their data.
-/

@[expose] public section

open CategoryTheory CategoryTheory.MonoidalCategory

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- The presheaf-level monoidal core used to construct pullback of scheme modules. -/
abbrev pullbackPresheafCore (f : X ⟶ Y) :=
  RingedSpace.Hom.presheafCore f.toLRSHom.toShHom

/-- Construct the strong-monoidal structure on scheme-module pullback from an explicit
presheaf-level core. -/
@[implicit_reducible]
noncomputable def pullbackMonoidalOf (m : pullbackPresheafCore f) :
    (Scheme.Modules.pullback f).Monoidal :=
  RingedSpace.Hom.pullbackMonoidalOf f.toLRSHom.toShHom m

/-- Pullback of scheme modules is canonically strong monoidal. -/
@[stacks 01CD "monoidal pullback of scheme modules", implicit_reducible]
noncomputable def pullbackMonoidal :
    (Scheme.Modules.pullback f).Monoidal :=
  RingedSpace.Hom.pullbackMonoidal f.toLRSHom.toShHom

/-- Pullback identifies the tensor unit on scheme modules with the tensor unit. -/
@[stacks 01CD "pullback of the scheme-module tensor unit"]
noncomputable abbrev pullbackUnitIso :
    (Scheme.Modules.pullback f).obj (𝟙_ Y.Modules) ≅ 𝟙_ X.Modules :=
  (@Functor.Monoidal.εIso _ _ _ _ _ _ (Scheme.Modules.pullback f)
    (pullbackMonoidal f)).symm

/-- The natural tensor comparison isomorphism for pullback of scheme modules. -/
@[stacks 01CD "natural pullback-tensor comparison for scheme modules"]
noncomputable abbrev pullbackTensorNatIso :
    MonoidalCategory.tensor Y.Modules ⋙ Scheme.Modules.pullback f ≅
      Functor.prod (Scheme.Modules.pullback f) (Scheme.Modules.pullback f) ⋙
        MonoidalCategory.tensor X.Modules :=
  (@Functor.Monoidal.μNatIso _ _ _ _ _ _ (Scheme.Modules.pullback f)
    (pullbackMonoidal f)).symm

/-- Pullback along a scheme morphism commutes with tensor products of module sheaves. -/
@[stacks 01CD "pullback-tensor comparison for scheme modules"]
noncomputable abbrev pullbackTensorIso (M N : Y.Modules) :
    (Scheme.Modules.pullback f).obj (M ⊗ N) ≅
      (Scheme.Modules.pullback f).obj M ⊗ (Scheme.Modules.pullback f).obj N :=
  (pullbackTensorNatIso f).app (M, N)

/-- The forward morphism of the pullback-tensor comparison for scheme modules. -/
noncomputable abbrev pullbackTensorComparison (M N : Y.Modules) :
    (Scheme.Modules.pullback f).obj (M ⊗ N) ⟶
      (Scheme.Modules.pullback f).obj M ⊗ (Scheme.Modules.pullback f).obj N :=
  (pullbackTensorIso f M N).hom

/-- Pull back a morphism out of a tensor product, using the canonical strong-monoidal
comparison to identify the tensor product of the two pullbacks with the pullback of the tensor
product. -/
noncomputable def pullbackTensorMap {M N P : Y.Modules} (φ : M ⊗ N ⟶ P) :
    (Scheme.Modules.pullback f).obj M ⊗ (Scheme.Modules.pullback f).obj N ⟶
      (Scheme.Modules.pullback f).obj P :=
  (pullbackTensorIso f M N).inv ≫ (Scheme.Modules.pullback f).map φ

/-- Pullback along a scheme morphism commutes canonically with every nonnegative tensor power. -/
noncomputable def pullbackTensorPowerIso (L : Y.Modules) (n : ℕ) :
    (Scheme.Modules.pullback f).obj (RingedSpace.TensorPower.sheaf L n) ≅
      RingedSpace.TensorPower.sheaf ((Scheme.Modules.pullback f).obj L) n :=
  (Scheme.Modules.pullback f).mapIso
      (RingedSpace.TensorPower.monoidalComparison.iso L n).symm ≪≫
    (@Functor.Monoidal.tensorPowerIso
      Y.Modules X.Modules _ _ _ _ (Scheme.Modules.pullback f)
      (pullbackMonoidal f) L n).symm ≪≫
      RingedSpace.TensorPower.monoidalComparison.iso
        ((Scheme.Modules.pullback f).obj L) n

end AlgebraicGeometry.Scheme.Modules
