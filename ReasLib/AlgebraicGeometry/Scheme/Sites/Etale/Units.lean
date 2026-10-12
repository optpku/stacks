/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.MultiplicativeGroup
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Basic
public import Mathlib.Algebra.Category.Grp.EquivalenceGroupAddGroup

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

universe u

noncomputable section

namespace AlgebraicGeometry.Scheme.Etale.Small

/-- The additive presheaf of global units on the small etale site of a scheme `X`. -/
abbrev unitsAddPresheaf (X : Scheme.{u}) :
    X.Etaleᵒᵖ ⥤ AddCommGrpCat.{u} :=
  (Scheme.smallEtaleToScheme X).op ⋙
    MultiplicativeGroup.unitsFunctor ⋙ CommGrpCat.toAddCommGrp

/-- The global-units presheaf on the small etale site satisfies the sheaf condition. -/
theorem unitsAddPresheaf_isSheaf (X : Scheme.{u}) :
    Presheaf.IsSheaf X.smallEtaleTopology (unitsAddPresheaf X) := sorry

/-- The additive sheaf of global units on the small etale site of a scheme `X`. -/
noncomputable def unitsAddSheaf (X : Scheme.{u}) :
    Sheaf X.smallEtaleTopology AddCommGrpCat.{u} :=
  ⟨unitsAddPresheaf X, unitsAddPresheaf_isSheaf X⟩

/-- The value of the small-etale units sheaf at `U` is the additive presentation of global units. -/
theorem unitsAddSheaf_obj (X : Scheme.{u}) (U : X.Etaleᵒᵖ) :
    (unitsAddSheaf X).1.obj U =
      CommGrpCat.toAddCommGrp.obj (CommGrpCat.of Γ((unop U).left, ⊤)ˣ) := sorry

end AlgebraicGeometry.Scheme.Etale.Small
