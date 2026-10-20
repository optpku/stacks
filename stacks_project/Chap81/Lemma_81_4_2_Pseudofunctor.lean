/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtaleSite.SheafPseudofunctor

/-!
# Small étale sheaf pullback for algebraic spaces

The canonical pullback and pseudofunctor API for Type-valued small étale sheaves.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u

#check (AlgebraicGeometry.AlgebraicSpace.EtaleSheaf.pullback :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y),
    Sheaf (smallEtaleTopology Y) (Type (u + 1)) ⥤
      Sheaf (smallEtaleTopology X) (Type (u + 1)))

#check (AlgebraicGeometry.AlgebraicSpace.EtaleSheaf.pullback_eq :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y),
    EtaleSheaf.pullback f = (smallEtaleMorphismOfTopoi f).inverseImage)

#check (AlgebraicGeometry.AlgebraicSpace.EtaleSheaf.pullbackId :
  ∀ {S : Scheme.{u}} (X : AlgebraicSpace S),
    EtaleSheaf.pullback (𝟙 X) ≅ 𝟭 (Sheaf (smallEtaleTopology X) (Type (u + 1))))

#check (AlgebraicGeometry.AlgebraicSpace.EtaleSheaf.pullbackComp :
  ∀ {S : Scheme.{u}} {X Y Z : AlgebraicSpace S} (f : Y ⟶ Z) (g : X ⟶ Y),
    EtaleSheaf.pullback f ⋙ EtaleSheaf.pullback g ≅ EtaleSheaf.pullback (g ≫ f))

#check (AlgebraicGeometry.AlgebraicSpace.EtaleSheaf.pseudofunctor :
  ∀ {S : Scheme.{u}}, Pseudofunctor (LocallyDiscrete (AlgebraicSpace S)ᵒᵖ) Cat)

#check (AlgebraicGeometry.AlgebraicSpace.EtaleSheaf.pseudofunctor_obj :
  ∀ {S : Scheme.{u}} (X : AlgebraicSpace S),
    EtaleSheaf.pseudofunctor.obj (.mk (.op X)) =
      Cat.of (Sheaf (smallEtaleTopology X) (Type (u + 1))))

#check (AlgebraicGeometry.AlgebraicSpace.EtaleSheaf.pseudofunctor_map :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y),
    (EtaleSheaf.pseudofunctor.map f.op.toLoc).toFunctor = EtaleSheaf.pullback f)
