module

public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import stacks_project.Chap59.Lemma_59_54_1
public import stacks_project.Chap63.Lemma_63_3_4_LowerShriek

/-!
# Proper morphisms: compact-support direct image equals pushforward
-/

@[expose] public section

open CategoryTheory
open AlgebraicGeometry
open AlgebraicGeometry.Scheme
open AlgebraicGeometry.Scheme.Etale
open Opposite

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Etale

variable {X Y : Scheme.{u}} (f : X ⟶ Y) [IsProper f]

/-- Lemma 63.3.4: Let `f : X ⟶ Y` be a proper morphism of schemes. Then
`f_! = f_*`, as abelian sheaves on the small étale site: the canonical inclusion
`etaleLowerShriek f ⟶ etaleAbelianPushforward f` is an isomorphism. -/
@[stacks 0F51]
instance etaleLowerShriekι_isIso : IsIso (etaleLowerShriekι f) := sorry

/-- Every section of the small-étale pushforward along a proper morphism has
proper support over the base. -/
theorem hasProperSupport_of_isProper
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) (V : Y.Etale)
    (σ : F.obj.obj (op ((smallEtalePullback f).obj V))) :
    HasProperSupport f F V σ :=
  sorry

/-- The comparison isomorphism `f_! ≅ f_*` for a proper morphism of schemes. -/
def etaleLowerShriekIso :
    etaleLowerShriek f ≅ etaleAbelianPushforward f :=
  asIso (etaleLowerShriekι f)

end AlgebraicGeometry.Scheme.Etale

end
