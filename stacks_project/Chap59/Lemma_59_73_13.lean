/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.ConstantPushforward
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

/- Lemma 59.73.13 (1): on an integral normal scheme `X` with function field `K`,
the small-étale pushforward of the constant sheaf on a set `E` along the
generic-point inclusion `g : Spec K ⟶ X` is the constant sheaf on `E`. -/
@[stacks 09Z5] #check (AlgebraicGeometry.Scheme.pushforward_constantSheaf_genericPoint :
    ∀ {X : Scheme.{u}} [IsIntegral X]
    (hX : X.isNormal) (E : Type u)
    [HasWeakSheafify X.smallEtaleTopology (Type u)]
    [HasWeakSheafify (Spec X.functionField).smallEtaleTopology (Type u)],
    Nonempty
      ((Scheme.smallEtaleDirectImage (X.fromSpecStalk (genericPoint X))).obj
          ((constantSheaf (Spec X.functionField).smallEtaleTopology (Type u)).obj E) ≅
        (constantSheaf X.smallEtaleTopology (Type u)).obj E))

/- Lemma 59.73.13 (2): on an integral normal scheme `X`, the small-étale
pushforward of the constant sheaf on a set `E` along the inclusion of a
nonempty open `U ⟶ X` is the constant sheaf on `E`. -/
@[stacks 09Z5] #check (AlgebraicGeometry.Scheme.pushforward_constantSheaf_opensι :
    ∀ {X : Scheme.{u}} [IsIntegral X]
    (hX : X.isNormal) (U : X.Opens) [Nonempty U] (E : Type u)
    [HasWeakSheafify X.smallEtaleTopology (Type u)]
    [HasWeakSheafify U.toScheme.smallEtaleTopology (Type u)],
    Nonempty
      ((Scheme.smallEtaleDirectImage U.ι).obj
          ((constantSheaf U.toScheme.smallEtaleTopology (Type u)).obj E) ≅
        (constantSheaf X.smallEtaleTopology (Type u)).obj E))
