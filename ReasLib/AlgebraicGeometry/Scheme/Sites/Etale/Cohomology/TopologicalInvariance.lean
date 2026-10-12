/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.TopologicalInvariance
public import ReasLib.CategoryTheory.Sites.AbelianSheaf.Additive
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.Map
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Terminal

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme

/-- Abelian sheaves on a small étale site have Ext groups in the standard
universe one level above the universe of the scheme. -/
instance smallEtaleAbelianSheaf_hasExt (X : Scheme.{u}) :
    HasExt.{u + 1} (Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) :=
  HasExt.standard _

-- Local declaration justification (metaprogramming implementation): the private comparison
-- must be exposed for use in the public restriction map under Lean's module system.
set_option backward.privateInPublic true in
/-- Inverse image along a universal homeomorphism identifies the constant
integer sheaf with the constant integer sheaf on the source. -/
private def constantIntegersPullbackIso {X0 X : Scheme.{u}} (f : X0 ⟶ X)
    [UniversalHomeomorphism f] :
    ((smallEtalePullback f).sheafPullback AddCommGrpCat.{u}
      X.smallEtaleTopology X0.smallEtaleTopology).obj
        ((constantSheaf X.smallEtaleTopology AddCommGrpCat.{u}).obj
          (AddCommGrpCat.of (ULift.{u} ℤ))) ≅
      (constantSheaf X0.smallEtaleTopology AddCommGrpCat.{u}).obj
        (AddCommGrpCat.of (ULift.{u} ℤ)) :=
  let terminal : X.Etale := MorphismProperty.Over.mk ⊤ (𝟙 X) inferInstance
  let h_terminal : IsTerminal terminal :=
    IsTerminal.isTerminalOfObj (MorphismProperty.Over.forget @Etale ⊤ X)
      terminal Over.mkIdTerminal
  let h_image : IsTerminal ((smallEtalePullback f).obj terminal) :=
    IsTerminal.isTerminalObj (smallEtalePullback f) terminal h_terminal
  let comparison :=
    ((constantSheafAdj X.smallEtaleTopology AddCommGrpCat.{u} h_terminal).comp
      ((smallEtalePullback f).sheafAdjunctionContinuous AddCommGrpCat.{u}
        X.smallEtaleTopology X0.smallEtaleTopology)).leftAdjointUniq
        (constantSheafAdj X0.smallEtaleTopology AddCommGrpCat.{u} h_image)
  comparison.app (AddCommGrpCat.of (ULift.{u} ℤ))

-- Local declaration justification (metaprogramming implementation): public module elaboration
-- needs access to the private constant-integer comparison in this exposed definition's body.
set_option backward.privateInPublic true in
/-- Restriction of étale cohomology along a universal homeomorphism is induced
by exact inverse image and the comparison of constant integer sheaves. -/
def etaleCohomologyRestriction {X0 X : Scheme.{u}} (f : X0 ⟶ X)
    [UniversalHomeomorphism f] (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u})
    (q : ℕ) :
    (Sheaf.functorH.{u + 1} X.smallEtaleTopology q).obj F ⟶
      (Sheaf.functorH.{u + 1} X0.smallEtaleTopology q).obj
        (((smallEtalePullback f).sheafPullback AddCommGrpCat.{u}
          X.smallEtaleTopology X0.smallEtaleTopology).obj F) :=
  let pull := (smallEtalePullback f).sheafPullback AddCommGrpCat.{u}
    X.smallEtaleTopology X0.smallEtaleTopology
  let integers := (constantSheaf X.smallEtaleTopology AddCommGrpCat.{u}).obj
    (AddCommGrpCat.of (ULift.{u} ℤ))
  let exactMap := Functor.mapExtAddHom.{u + 1, u + 1} pull integers F q
  let integerClass := Ext.mk₀.{u + 1} (constantIntegersPullbackIso f).inv
  AddCommGrpCat.ofHom exactMap ≫
    AddCommGrpCat.ofHom (Ext.precomp integerClass (pull.obj F) (zero_add q))

/-- Restriction along a universal homeomorphism is invertible in every degree
for every abelian étale sheaf. -/
instance etaleCohomologyRestriction_isIso {X0 X : Scheme.{u}} (f : X0 ⟶ X)
    [UniversalHomeomorphism f] (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u})
    (q : ℕ) : IsIso (etaleCohomologyRestriction f F q) := sorry

/-- The canonical restriction isomorphism identifies the étale cohomology of
an abelian sheaf with that of its inverse image along a universal homeomorphism. -/
def etaleCohomologyRestrictionIso {X0 X : Scheme.{u}} (f : X0 ⟶ X)
    [UniversalHomeomorphism f] (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u})
    (q : ℕ) :
    (Sheaf.functorH.{u + 1} X.smallEtaleTopology q).obj F ≅
      (Sheaf.functorH.{u + 1} X0.smallEtaleTopology q).obj
        (((smallEtalePullback f).sheafPullback AddCommGrpCat.{u}
          X.smallEtaleTopology X0.smallEtaleTopology).obj F) :=
  asIso (etaleCohomologyRestriction f F q)

end AlgebraicGeometry.Scheme
