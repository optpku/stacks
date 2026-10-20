module

public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.CategoryTheory.Equivalence
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FiniteType
public import ReasLib.AlgebraicGeometry.Scheme.Module.Invertible.Basic
public import ReasLib.AlgebraicGeometry.Scheme.Module.Coherent.Linearity

@[expose] public section

open CategoryTheory
open AlgebraicGeometry
open AlgebraicGeometry.Scheme

universe u

namespace AlgebraicGeometry.Scheme

/-- A linear equivalence between coherent modules on finite-type schemes over a field,
with separated source and reduced target, is naturally isomorphic to pullback along
an isomorphism over the field followed by tensoring with an invertible module. -/
theorem coherent_equivalence_pullback_tensor_invertible_over_field
    {k : Type u} [Field k] {X Y : Scheme.{u}}
    (x : X ⟶ Spec (CommRingCat.of k)) (y : Y ⟶ Spec (CommRingCat.of k))
    [x.FiniteType] [y.FiniteType] [IsSeparated x] [IsReduced Y]
    (F : RingedSpace.Coh X.toRingedSpace ⥤ RingedSpace.Coh Y.toRingedSpace)
    [F.IsEquivalence] [LinearOverCoh x y F] :
    ∃ (f : Y ≅ X) (L : Y.Modules),
      Scheme.Modules.Invertible L ∧
        f.hom ≫ x = y ∧
          Nonempty
            ((F ⋙ (SheafOfModules.isCoherent Y.toRingedSpace.ringCatSheaf).ι ⋙
                Scheme.Modules.fromRingedSpace Y) ≅
              ((SheafOfModules.isCoherent X.toRingedSpace.ringCatSheaf).ι ⋙
                Scheme.Modules.fromRingedSpace X ⋙
                Scheme.Modules.pullback f.hom ⋙
                CategoryTheory.MonoidalCategory.tensorRight L)) := sorry

end AlgebraicGeometry.Scheme
