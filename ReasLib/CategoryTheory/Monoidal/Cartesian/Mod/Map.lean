/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Monoidal.Cartesian.PseudoTorsor

/-!
# Mapping actions in Cartesian monoidal categories

Braided monoidal functors between Cartesian monoidal categories transport group actions and
pseudo-torsors.
-/

@[expose] public section

open CategoryTheory MonoidalCategory
open scoped MonObj MonoidalLeftAction

noncomputable section

universe v₁ v₂ u₁ u₂

namespace CategoryTheory.Functor

variable {C : Type u₁} [Category.{v₁} C] [CartesianMonoidalCategory C]
  [BraidedCategory C]
  {D : Type u₂} [Category.{v₂} D] [CartesianMonoidalCategory D]
  [BraidedCategory D]
  (F : C ⥤ D) [F.Braided] (G : Grp C) (X : Mod C G.X)

/-- The action morphism obtained by applying a braided monoidal functor. -/
def mapModSmul :
    (F.mapGrp.obj G).X ⊗ F.obj X.X ⟶ F.obj X.X :=
  Functor.LaxMonoidal.μ F G.X X.X ≫ F.map X.mod.smul

/-- The mapped action morphism satisfies the identity-action law. -/
theorem mapMod_one_smul :
    η[(F.mapGrp.obj G).X] ⊵ₗ F.obj X.X ≫ mapModSmul F G X =
      (λₗ (F.obj X.X)).hom := sorry

/-- The mapped action morphism is compatible with group multiplication. -/
theorem mapMod_mul_smul :
    μ[(F.mapGrp.obj G).X] ⊵ₗ F.obj X.X ≫ mapModSmul F G X =
      (αₗ (F.mapGrp.obj G).X (F.mapGrp.obj G).X (F.obj X.X)).hom ≫
        (F.mapGrp.obj G).X ⊴ₗ mapModSmul F G X ≫ mapModSmul F G X := sorry

/-- The module-object structure obtained by applying a braided monoidal functor. -/
@[reducible]
def mapModObj : ModObj (F.mapGrp.obj G).X (F.obj X.X) where
  smul := mapModSmul F G X
  one_smul := mapMod_one_smul F G X
  mul_smul := mapMod_mul_smul F G X

/-- The bundled group action obtained by applying a braided monoidal functor. -/
def mapMod : Mod D (F.mapGrp.obj G).X where
  X := F.obj X.X
  mod := mapModObj F G X

/-- The carrier of a mapped action is the image of the original carrier. -/
theorem mapMod_X : (mapMod F G X).X = F.obj X.X := sorry

/-- The action morphism stored by a mapped action is the mapped action morphism. -/
theorem mapMod_smul : (mapMod F G X).mod.smul = mapModSmul F G X := sorry

/-- A braided monoidal functor between Cartesian monoidal categories preserves pseudo-torsors. -/
instance instIsPseudoTorsorMapMod [Mod.IsPseudoTorsor X] :
    Mod.IsPseudoTorsor (mapMod F G X) := sorry

end CategoryTheory.Functor
