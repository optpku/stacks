/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap63.Lemma_63_4_3_Comparison

/-!
# Identification of étale extension by zero with finite-support lower shriek

Lemma 63.4.3: for an étale morphism `j : U ⟶ X`, the sheafification of the
canonical presheaf comparison `j_{p!} F ⟶ f_{p!} F` identifies
`j_! F = (j_{p!} F)^#` with `(f_{p!} F)^#`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.Scheme.Etale

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Etale

variable {U X : Scheme.{u}} (j : U ⟶ X) [Etale j] [LocallyQuasiFinite j]
variable [∀ F : U.Etaleᵒᵖ ⥤ AddCommGrpCat.{u},
  (etaleRestriction j).op.HasLeftKanExtension F]
variable [HasWeakSheafify X.smallEtaleTopology AddCommGrpCat.{u}]

/-- The sheafified graph comparison `j_! ⟶ (f_{p!})^#` is an isomorphism. -/
instance extensionByZeroToLowerShriek_isIso :
    IsIso (extensionByZeroToLowerShriek j) :=
  sorry

/-- Lemma 63.4.3: Let `j : U ⟶ X` be an étale morphism of schemes. Functorially
in an abelian étale sheaf `F` on `U_étale`, there is a canonical map of abelian
presheaves `j_{p!} F ⟶ f_{p!} F` which identifies the sheaf
`j_! F = (j_{p!} F)^#` of Definition 59.70.1 with `(f_{p!} F)^#`.
The TeX binder `F ∈ Ab(X_étale)` is a source slip: both constructions evaluate
`F` on `U`-schemes. Stacks locally quasi-finite is rendered as
`[LocallyQuasiFinite j]`. -/
@[stacks 0F6Q]
def extensionByZeroIsoLowerShriek :
    abelianExtensionByZero j ≅
      lowerShriekPresheaf j ⋙
        presheafToSheaf X.smallEtaleTopology AddCommGrpCat.{u} :=
  asIso (extensionByZeroToLowerShriek j)

/-- The identification of Lemma 63.4.3 at an abelian étale sheaf `F`. -/
def extensionByZeroIsoLowerShriek_app
    (F : Sheaf U.smallEtaleTopology AddCommGrpCat.{u}) :
    (abelianExtensionByZero j).obj F ≅
      (presheafToSheaf X.smallEtaleTopology AddCommGrpCat.{u}).obj
        ((lowerShriekPresheaf j).obj F) :=
  (extensionByZeroIsoLowerShriek j).app F

/-- The forward map of `extensionByZeroIsoLowerShriek` is the sheafified graph
comparison. -/
theorem extensionByZeroIsoLowerShriek_hom :
    (extensionByZeroIsoLowerShriek j).hom = extensionByZeroToLowerShriek j :=
  sorry

/-- The objectwise identification is the component of
`extensionByZeroIsoLowerShriek`. -/
theorem extensionByZeroIsoLowerShriek_app_eq
    (F : Sheaf U.smallEtaleTopology AddCommGrpCat.{u}) :
    extensionByZeroIsoLowerShriek_app j F =
      (extensionByZeroIsoLowerShriek j).app F :=
  sorry

end AlgebraicGeometry.Scheme.Etale

end
