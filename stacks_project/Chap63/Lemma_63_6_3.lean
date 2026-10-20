/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.UpperShriek.LocallyQuasiFinite.Composition
import StacksCheckRecall

open CategoryTheory
open CategoryTheory.Functor
open CategoryTheory.Limits
open AlgebraicGeometry
open AlgebraicGeometry.Scheme
open AlgebraicGeometry.Scheme.Etale

universe u

variable {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
variable [LocallyQuasiFinite f] [LocallyQuasiFinite g]
variable [LocallyOfFiniteType f] [LocallyOfFiniteType g]
variable [IsSeparated f] [IsSeparated g]
variable [HasCoproducts.{u} (Sheaf Z.smallEtaleTopology AddCommGrpCat.{u})]

/- Lemma 63.6.3. For separated locally quasi-finite morphisms `f` and `g`,
there is a canonical isomorphism `(g ∘ f)^! ≅ f^! ∘ g^!`. -/
@[stacks 0F5B] #check (AlgebraicGeometry.Scheme.Etale.upperShriekCompIso f g :
    upperShriek (f ≫ g) ≅ upperShriek g ⋙ upperShriek f)

variable {T : Scheme.{u}} (h : Z ⟶ T)
variable [LocallyQuasiFinite h] [LocallyOfFiniteType h]
variable [HasCoproducts.{u} (Sheaf T.smallEtaleTopology AddCommGrpCat.{u})]

/- Lemma 63.6.3. For a third locally quasi-finite morphism `h`, the
associativity square of the canonical composition identifications commutes. -/
@[stacks 0F5B] #check (AlgebraicGeometry.Scheme.Etale.upperShriekCompIso_assoc f g h :
    (upperShriekCompIso (f ≫ g) h).hom ≫
        whiskerLeft (upperShriek h) (upperShriekCompIso f g).hom =
      eqToHom (upperShriek_assoc f g h) ≫
        (upperShriekCompIso f (g ≫ h)).hom ≫
        whiskerRight (upperShriekCompIso g h).hom (upperShriek f) ≫
        (associator (upperShriek h) (upperShriek g) (upperShriek f)).hom)
