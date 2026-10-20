/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.H.Big

@[expose] public section

open CategoryTheory
open AlgebraicGeometry
open AlgebraicGeometry.Scheme
open scoped MorphismOfTopoiIn

noncomputable section

universe u

/- Compatibility checks for the promoted big h-site API. -/
#check AlgebraicGeometry.Scheme.H.Big.site
#check (AlgebraicGeometry.Scheme.H.Big.map :
  ∀ {S T : Scheme.{u}}, (T ⟶ S) → Over T ⥤ Over S)
#check (AlgebraicGeometry.Scheme.H.Big.pullback :
  ∀ {S T : Scheme.{u}}, (T ⟶ S) → Over S ⥤ Over T)
#check (AlgebraicGeometry.Scheme.H.Big.map_isContinuous :
  ∀ {S T : Scheme.{u}} (f : T ⟶ S),
    (AlgebraicGeometry.Scheme.H.Big.map f).IsContinuous
      (AlgebraicGeometry.Scheme.H.Big.site T)
      (AlgebraicGeometry.Scheme.H.Big.site S))
#check (AlgebraicGeometry.Scheme.H.Big.map_isCocontinuous :
  ∀ {S T : Scheme.{u}} (f : T ⟶ S),
    (AlgebraicGeometry.Scheme.H.Big.map f).IsCocontinuous
      (AlgebraicGeometry.Scheme.H.Big.site T)
      (AlgebraicGeometry.Scheme.H.Big.site S))
#check (AlgebraicGeometry.Scheme.H.Big.map_op_hasLeftKanExtension :
  ∀ {S T : Scheme.{u}} (f : T ⟶ S)
    (P : (Over T)ᵒᵖ ⥤ Type (u + 1)),
    (AlgebraicGeometry.Scheme.H.Big.map f).op.HasLeftKanExtension P)
#check (AlgebraicGeometry.Scheme.H.Big.map_op_hasPointwiseRightKanExtension :
  ∀ {S T : Scheme.{u}} (f : T ⟶ S)
    (P : (Over T)ᵒᵖ ⥤ Type (u + 1)),
    (AlgebraicGeometry.Scheme.H.Big.map f).op.HasPointwiseRightKanExtension P)
#check (AlgebraicGeometry.Scheme.H.Big.hasWeakSheafify :
  ∀ (S : Scheme.{u}),
    HasWeakSheafify (AlgebraicGeometry.Scheme.H.Big.site S) (Type (u + 1)))
#check (AlgebraicGeometry.Scheme.H.Big.morphismOfTopoi :
  ∀ {S T : Scheme.{u}} (f : T ⟶ S),
    MorphismOfTopoiIn
      (AlgebraicGeometry.Scheme.H.Big.site S)
      (AlgebraicGeometry.Scheme.H.Big.site T))
#check (AlgebraicGeometry.Scheme.H.Big.directImage :
  ∀ {S T : Scheme.{u}} (f : T ⟶ S),
    Sheaf (AlgebraicGeometry.Scheme.H.Big.site T) (Type (u + 1)) ⥤
      Sheaf (AlgebraicGeometry.Scheme.H.Big.site S) (Type (u + 1)))

end

end
