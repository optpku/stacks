/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.Sites.Etale
public import ReasLib.CategoryTheory.Sites.ConstantSheaf.Characterization
public import ReasLib.CategoryTheory.Sites.LocallyConstant.Finite
import StacksCheckRecall

@[expose] public section

open CategoryTheory
open AlgebraicGeometry

universe u v w

section Types

variable (X : Scheme.{u})
variable [HasWeakSheafify X.smallEtaleTopology (Type v)]
variable [∀ U : X.Etale, HasWeakSheafify (X.smallEtaleTopology.over U) (Type v)]
variable (E : Type v) (F : Sheaf X.smallEtaleTopology (Type v))

/- Definition 59.64.1 (1): the constant set-valued sheaf with value `E` is the
sheafification of the constant presheaf with value `E`. -/
@[stacks 03RU] #check
  (CategoryTheory.constantSheaf_obj X.smallEtaleTopology (Type v) E :
    (constantSheaf X.smallEtaleTopology (Type v)).obj E =
      (presheafToSheaf X.smallEtaleTopology (Type v)).obj
        ((Functor.const X.Etaleᵒᵖ).obj E))

/- Definition 59.64.1 (2): a set-valued sheaf is constant when it is isomorphic to a
constant sheaf. -/
@[stacks 03RU] #check
  (CategoryTheory.Sheaf.isConstant_iff_exists_iso X.smallEtaleTopology F :
    Sheaf.IsConstant X.smallEtaleTopology F ↔
      ∃ E : Type v, Nonempty (F ≅ (constantSheaf X.smallEtaleTopology (Type v)).obj E))

/- Definition 59.64.1 (3): local constancy for a set-valued sheaf on the small étale site. -/
@[stacks 03RU] #check (CategoryTheory.Sheaf.IsLocallyConstant F : Prop)

/- Definition 59.64.1 (4): finite local constancy for a set-valued sheaf on the small
étale site. -/
@[stacks 03RU] #check (CategoryTheory.Sheaf.IsFiniteLocallyConstant F : Prop)

end Types

section AddCommGroups

variable (X : Scheme.{u})
variable [HasWeakSheafify X.smallEtaleTopology AddCommGrpCat.{w}]
variable [∀ U : X.Etale,
  HasWeakSheafify (X.smallEtaleTopology.over U) AddCommGrpCat.{w}]
variable (A : AddCommGrpCat.{w})
variable (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{w})

/- Definition 59.64.1 (5): the constant abelian-group-valued sheaf with value `A` is the
sheafification of the constant presheaf with value `A`. -/
@[stacks 03RU] #check
  (CategoryTheory.constantSheaf_obj X.smallEtaleTopology AddCommGrpCat.{w} A :
    (constantSheaf X.smallEtaleTopology AddCommGrpCat.{w}).obj A =
      (presheafToSheaf X.smallEtaleTopology AddCommGrpCat.{w}).obj
        ((Functor.const X.Etaleᵒᵖ).obj A))

/- Definition 59.64.1 (6): an abelian-group-valued sheaf is constant when it is isomorphic
as an abelian sheaf to a constant sheaf. -/
@[stacks 03RU] #check
  (CategoryTheory.Sheaf.isConstant_iff_exists_iso X.smallEtaleTopology F :
    Sheaf.IsConstant X.smallEtaleTopology F ↔
      ∃ A : AddCommGrpCat.{w},
        Nonempty (F ≅ (constantSheaf X.smallEtaleTopology AddCommGrpCat.{w}).obj A))

/- Definition 59.64.1 (7): local constancy for an abelian-group-valued sheaf on the small
étale site. -/
@[stacks 03RU] #check (CategoryTheory.Sheaf.IsLocallyConstant F : Prop)

/- Definition 59.64.1 (8): finite local constancy for an abelian-group-valued sheaf on the
small étale site. -/
@[stacks 03RU] #check (CategoryTheory.Sheaf.IsFiniteLocallyConstantAddCommGrp F : Prop)

end AddCommGroups

section Modules

variable (X : Scheme.{u})
variable {Λ : Type w} [Ring Λ]
variable [HasWeakSheafify X.smallEtaleTopology (ModuleCat.{w} Λ)]
variable [∀ U : X.Etale,
  HasWeakSheafify (X.smallEtaleTopology.over U) (ModuleCat.{w} Λ)]
variable (M : ModuleCat.{w} Λ)
variable (F : Sheaf X.smallEtaleTopology (ModuleCat.{w} Λ))

/- Definition 59.64.1 (9): the constant `Λ`-module-valued sheaf with value `M` is the
sheafification of the constant presheaf with value `M`. -/
@[stacks 03RU] #check
  (CategoryTheory.constantSheaf_obj X.smallEtaleTopology (ModuleCat.{w} Λ) M :
    (constantSheaf X.smallEtaleTopology (ModuleCat.{w} Λ)).obj M =
      (presheafToSheaf X.smallEtaleTopology (ModuleCat.{w} Λ)).obj
        ((Functor.const X.Etaleᵒᵖ).obj M))

/- Definition 59.64.1 (10): a `Λ`-module-valued sheaf is constant when it is isomorphic as
a sheaf of `Λ`-modules to a constant sheaf. -/
@[stacks 03RU] #check
  (CategoryTheory.Sheaf.isConstant_iff_exists_iso X.smallEtaleTopology F :
    Sheaf.IsConstant X.smallEtaleTopology F ↔
      ∃ M : ModuleCat.{w} Λ,
        Nonempty (F ≅ (constantSheaf X.smallEtaleTopology (ModuleCat.{w} Λ)).obj M))

/- Definition 59.64.1 (11): local constancy for a `Λ`-module-valued sheaf on the small
étale site. -/
@[stacks 03RU] #check (CategoryTheory.Sheaf.IsLocallyConstant F : Prop)

end Modules
