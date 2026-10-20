/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Monoidal.Bimod.ChangeOfScalars.Equivalence
public import ReasLib.CategoryTheory.Monoidal.Bimod.Tensor
import Mathlib.Tactic.CrossRefAttribute

/-!
# Balanced tensor products and isomorphic coefficients

Changing the middle coefficient monoid by an isomorphism does not change a balanced tensor
product.  This file constructs the comparison directly from the two defining coequalizers and
records its naturality in both bimodule variables.
-/

@[expose] public section

open CategoryTheory.Limits CategoryTheory.MonoidalCategory

noncomputable section

universe u v

namespace CategoryTheory.Bimod.ChangeOfScalars

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]
variable [HasCoequalizers C]
variable [∀ X : C, PreservesColimitsOfSize.{0, 0} (MonoidalCategory.tensorLeft X)]
variable [∀ X : C, PreservesColimitsOfSize.{0, 0} (MonoidalCategory.tensorRight X)]
variable {R A B T : Mon C}

/-- The carrier map comparing balanced tensors after replacing the middle monoid `A` by an
isomorphic monoid `B`.  It is induced by the quotient map for the `A`-balanced tensor. -/
@[stacks 0FSA "balanced tensor comparison under a coefficient isomorphism"]
noncomputable def tensorIsoHomCarrier (e : A ≅ B) (P : Bimod R A) (Q : Bimod B T) :
    (((Bimod.restrictRight R e.inv).obj P).tensorBimod Q).X ⟶
      (P.tensorBimod ((Bimod.restrictLeft e.hom T).obj Q)).X :=
  coequalizer.desc
    (coequalizer.π
      (P.actRight ▷ ((Bimod.restrictLeft e.hom T).obj Q).X)
      ((α_ P.X A.X ((Bimod.restrictLeft e.hom T).obj Q).X).hom ≫
        (P.X ◁ ((Bimod.restrictLeft e.hom T).obj Q).actLeft)))
    sorry

/-- The inverse carrier map, induced by the quotient map for the `B`-balanced tensor. -/
@[stacks 0FSA "inverse balanced tensor comparison under a coefficient isomorphism"]
noncomputable def tensorIsoInvCarrier (e : A ≅ B) (P : Bimod R A) (Q : Bimod B T) :
    (P.tensorBimod ((Bimod.restrictLeft e.hom T).obj Q)).X ⟶
      (((Bimod.restrictRight R e.inv).obj P).tensorBimod Q).X :=
  coequalizer.desc
    (coequalizer.π
      (((Bimod.restrictRight R e.inv).obj P).actRight ▷ Q.X)
      ((α_ ((Bimod.restrictRight R e.inv).obj P).X B.X Q.X).hom ≫
        (((Bimod.restrictRight R e.inv).obj P).X ◁ Q.actLeft)))
    sorry

/-- The balanced-tensor comparison as a morphism of the outer `(R,T)`-bimodules. -/
@[stacks 0FSA "balanced tensor morphism under a coefficient isomorphism"]
noncomputable def tensorIsoHom (e : A ≅ B) (P : Bimod R A) (Q : Bimod B T) :
    ((Bimod.restrictRight R e.inv).obj P).tensorBimod Q ⟶
      P.tensorBimod ((Bimod.restrictLeft e.hom T).obj Q) where
  hom := tensorIsoHomCarrier e P Q
  left_act_hom := sorry
  right_act_hom := sorry

/-- The inverse balanced-tensor comparison as a morphism of outer bimodules. -/
@[stacks 0FSA "inverse balanced tensor morphism under a coefficient isomorphism"]
noncomputable def tensorIsoInv (e : A ≅ B) (P : Bimod R A) (Q : Bimod B T) :
    P.tensorBimod ((Bimod.restrictLeft e.hom T).obj Q) ⟶
      ((Bimod.restrictRight R e.inv).obj P).tensorBimod Q where
  hom := tensorIsoInvCarrier e P Q
  left_act_hom := sorry
  right_act_hom := sorry

/-- The two coefficient-change comparisons compose to the identity on the `B`-balanced tensor. -/
theorem tensorIsoHomInv (e : A ≅ B) (P : Bimod R A) (Q : Bimod B T) :
    tensorIsoHom e P Q ≫ tensorIsoInv e P Q = 𝟙 _ := sorry

/-- The two coefficient-change comparisons compose to the identity on the `A`-balanced tensor. -/
theorem tensorIsoInvHom (e : A ≅ B) (P : Bimod R A) (Q : Bimod B T) :
    tensorIsoInv e P Q ≫ tensorIsoHom e P Q = 𝟙 _ := sorry

/-- Balanced tensor product is invariant under an isomorphism of its middle coefficient monoid. -/
@[stacks 0FSA "balanced tensor isomorphism under a coefficient isomorphism"]
noncomputable def tensorIso (e : A ≅ B) (P : Bimod R A) (Q : Bimod B T) :
    ((Bimod.restrictRight R e.inv).obj P).tensorBimod Q ≅
      P.tensorBimod ((Bimod.restrictLeft e.hom T).obj Q) where
  hom := tensorIsoHom e P Q
  inv := tensorIsoInv e P Q
  hom_inv_id := tensorIsoHomInv e P Q
  inv_hom_id := tensorIsoInvHom e P Q

/-- The coefficient-change tensor isomorphism is natural in its left bimodule. -/
theorem tensorIso_natural_left (e : A ≅ B) {P P' : Bimod R A} (f : P ⟶ P')
    (Q : Bimod B T) :
    Bimod.whiskerRight ((Bimod.restrictRight R e.inv).map f) Q ≫
        (tensorIso e P' Q).hom =
      (tensorIso e P Q).hom ≫
        Bimod.whiskerRight f ((Bimod.restrictLeft e.hom T).obj Q) := sorry

/-- The coefficient-change tensor isomorphism is natural in its right bimodule. -/
theorem tensorIso_natural_right (e : A ≅ B) (P : Bimod R A)
    {Q Q' : Bimod B T} (g : Q ⟶ Q') :
    Bimod.whiskerLeft ((Bimod.restrictRight R e.inv).obj P) g ≫
        (tensorIso e P Q').hom =
      (tensorIso e P Q).hom ≫
        Bimod.whiskerLeft P ((Bimod.restrictLeft e.hom T).map g) := sorry

end CategoryTheory.Bimod.ChangeOfScalars

end
