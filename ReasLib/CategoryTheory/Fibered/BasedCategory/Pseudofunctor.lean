/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Bicategory.FullSubbicategory.Definition
public import ReasLib.CategoryTheory.Bicategory.InducedBicategory.Iso
public import ReasLib.CategoryTheory.Fibered.BasedCategory.NaturalIso
public import Mathlib.CategoryTheory.Bicategory.Functor.Pseudofunctor
import Mathlib.Tactic.CrossRefAttribute

/-!
# Total-functor isomorphisms induced by based-category pseudofunctors

This module is the neutral bridge from an isomorphism in a hom-category mapped into
`BasedCategory` to the resulting natural isomorphism of total-category functors.
-/

@[expose] public section

namespace CategoryTheory

open scoped Bicategory

universe uB vB wB uC vC uS vS

variable {B : Type uB} [Bicategory.{wB, vB} B]
variable {C : Type uC} [Category.{vC} C]

namespace Pseudofunctor

variable {X Y : B}

/-- Map an isomorphism in a hom-category through a pseudofunctor valued in categories over `C`,
then forget the resulting based natural isomorphism to total-category functors. -/
def mapToFunctorIso
    (P : B ⥤ᵖ BasedCategory.{vS, uS} C)
    {F G : X ⟶ Y} (e : F ≅ G) :
    (P.map F).toFunctor ≅ (P.map G).toFunctor :=
  BasedNatIso.toNatIso ((P.mapFunctor X Y).mapIso e)

end Pseudofunctor

namespace ObjectProperty.FullSubbicategory.toFunctor

variable {P : ObjectProperty (BasedCategory.{vS, uS} C)}
variable {X Y Z : P.FullSubbicategory}

/-- The total functor underlying a composite in a full subbicategory of `BasedCategory C` is
canonically isomorphic to the composite of the two underlying total functors. Its components are
identities because both induced-bicategory and based-functor composition preserve the data
strictly. -/
@[stacks 04Z4 "total-functor composition comparison"]
def compIso (F : X ⟶ Y) (G : Y ⟶ Z) :
    F.hom.toFunctor ⋙ G.hom.toFunctor ≅ (F ≫ G).hom.toFunctor :=
  BasedNatIso.toNatIso (Bicategory.InducedBicategory.Hom.compIso F G)

/-- Every forward component of the total-functor composition comparison is the identity. -/
@[simp, stacks 04Z4 "total-functor composition forward component"]
theorem compIso.hom.app (F : X ⟶ Y) (G : Y ⟶ Z) (x : X.1.obj) :
    (compIso F G).hom.app x = 𝟙 (G.hom.obj (F.hom.obj x)) := sorry

/-- Every inverse component of the total-functor composition comparison is the identity. -/
@[simp, stacks 04Z4 "total-functor composition inverse component"]
theorem compIso.inv.app (F : X ⟶ Y) (G : Y ⟶ Z) (x : X.1.obj) :
    (compIso F G).inv.app x = 𝟙 (G.hom.obj (F.hom.obj x)) := sorry

end ObjectProperty.FullSubbicategory.toFunctor

end CategoryTheory
