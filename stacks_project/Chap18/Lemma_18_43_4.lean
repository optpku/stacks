/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Sites.LocallyConstant.Hom
import StacksCheckRecall

/-!
# Lemma 18.43.4

Compatibility facade for local morphisms and local isomorphisms between locally constant
module-valued sheaves.  Their constructions and reusable APIs are owned by
`ReasLib.CategoryTheory.Sites.LocallyConstant.Hom`.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u v w

namespace CategoryTheory.Sheaf

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
variable {Λ : Type w} [CommRing Λ]

section ConstantHom

variable [HasWeakSheafify J (ModuleCat.{max u v w} Λ)]
variable (M N : ModuleCat.{max u v w} Λ)
variable [Module.FinitePresentation Λ M]

/- Lemma 18.43.4 (093T) (1): local morphisms between the constant sheaves on a finitely
presented module `M` and a module `N` form the constant sheaf on `M ⟶ N`. -/
@[stacks 093T "(1)"]
#check
  (LocalHom.isIsomorphic_constant (J := J) M N :
    IsIsomorphic
      (LocalHom.sheaf
        ((constantSheaf J (ModuleCat.{max u v w} Λ)).obj M)
        ((constantSheaf J (ModuleCat.{max u v w} Λ)).obj N))
      ((constantSheaf J (ModuleCat.{max u v w} Λ)).obj
        (ModuleCat.of Λ (M ⟶ N))))

end ConstantHom

section ConstantIso

variable [HasWeakSheafify J (ModuleCat.{max u v w} Λ)]
variable [HasWeakSheafify J (Type (max u v w))]
variable (M N : ModuleCat.{max u v w} Λ)
variable [Module.FinitePresentation Λ M] [Module.FinitePresentation Λ N]

/- Lemma 18.43.4 (093T) (2): local isomorphisms between the constant sheaves on finitely
presented modules `M` and `N` form the constant sheaf on `M ≅ N`. -/
@[stacks 093T "(2)"]
#check
  (LocalIso.isIsomorphic_constant (J := J) M N :
    IsIsomorphic
      (LocalIso.sheaf
        ((constantSheaf J (ModuleCat.{max u v w} Λ)).obj M)
        ((constantSheaf J (ModuleCat.{max u v w} Λ)).obj N))
      ((constantSheaf J (Type (max u v w))).obj (M ≅ N)))

end ConstantIso

section LocalHom

variable [HasWeakSheafify J (ModuleCat.{max u v w} Λ)]
variable [∀ U : C, HasWeakSheafify (J.over U) (ModuleCat.{max u v w} Λ)]
variable (F G : Sheaf J (ModuleCat.{max u v w} Λ))
variable [LocallyConstant.IsFinitePresentation F] [IsLocallyConstant G]

/- Lemma 18.43.4 (093T) (3): local Hom from a locally constant sheaf with finitely presented
constant models to a locally constant sheaf is locally constant. -/
@[stacks 093T "(3)"]
#check
  (LocalHom.isLocallyConstant F G :
    IsLocallyConstant (LocalHom.sheaf F G))

end LocalHom

section LocalIso

variable [HasWeakSheafify J (ModuleCat.{max u v w} Λ)]
variable [∀ U : C, HasWeakSheafify (J.over U) (ModuleCat.{max u v w} Λ)]
variable [HasWeakSheafify J (Type (max u v w))]
variable [∀ U : C, HasWeakSheafify (J.over U) (Type (max u v w))]
variable (F G : Sheaf J (ModuleCat.{max u v w} Λ))
variable [LocallyConstant.IsFinitePresentation F]
variable [LocallyConstant.IsFinitePresentation G]

/- Lemma 18.43.4 (093T) (4): local isomorphisms between locally constant sheaves with finitely
presented constant models form a locally constant sheaf of types. -/
@[stacks 093T "(4)"]
#check
  (LocalIso.isLocallyConstant F G :
    IsLocallyConstant (LocalIso.sheaf F G))

end LocalIso

end CategoryTheory.Sheaf
