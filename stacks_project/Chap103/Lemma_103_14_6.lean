module

public import stacks_project.Chap96.Lemma_96_12_4_LQCoh
public import stacks_project.Chap103.Definition_103_7_1_FlatBaseChange
public import stacks_project.Chap103.Definition_103_9_1_Parasitic
public import stacks_project.Chap103.Lemma_103_14_2_Ringed

/-!
# Parasitic modules via lisse-étale and flat-fppf pullback

On an algebraic stack, parasitic vanishing of an étale module with the flat
base change property is equivalent to vanishing after pullback along the
lisse-étale ringed morphism of Lemma 103.14.2, and parasitic vanishing of an
fppf module is equivalent to vanishing after pullback along the flat-fppf
ringed morphism.
-/

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicStack AlgebraicGeometry.GroupoidsOver
open CategoryTheory CategoryTheory.Limits

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicStack

variable {S : Scheme.{u}}

/-- Lemma 103.14.6 (1): for an algebraic stack `X` and an étale `𝒪_X`-module `F`
with the flat base change property, `F` is parasitic if and only if
`(lisseEtaleRingedToposHom X).modulePullback.obj F` is zero. -/
@[stacks 07AR]
theorem isParasitic_iff_lisseEtaleModulePullback_isZero
    (X : GroupoidsOver S) [AlgebraicStack X] (F : etaleModules X)
    [HasFlatBaseChange F] :
    IsParasitic (etaleModulePresheaf F) ↔
      IsZero ((lisseEtaleRingedToposHom X).modulePullback.obj F) :=
  sorry

/-- Lemma 103.14.6 (2): for an algebraic stack `X` and an `𝒪_X`-module `F` on
the fppf site, `F` is parasitic if and only if
`(flatFppfRingedToposHom X).modulePullback.obj F` is zero. -/
@[stacks 07AR]
theorem isParasitic_iff_flatFppfModulePullback_isZero
    (X : GroupoidsOver S) [AlgebraicStack X]
    (F : SheafOfModules.{u} (structureSheaf X)) :
    IsParasitic F.val ↔
      IsZero ((flatFppfRingedToposHom X).modulePullback.obj F) :=
  sorry

/-- The lisse-étale module pullback of a parasitic étale module with the flat
base change property is zero. -/
theorem lisseEtaleModulePullback_isZero_of_isParasitic
    (X : GroupoidsOver S) [AlgebraicStack X] (F : etaleModules X)
    [HasFlatBaseChange F] :
    IsParasitic (etaleModulePresheaf F) →
      IsZero ((lisseEtaleRingedToposHom X).modulePullback.obj F) :=
  sorry

/-- An étale module with the flat base change property is parasitic if its
lisse-étale module pullback is zero. -/
theorem isParasitic_of_lisseEtaleModulePullback_isZero
    (X : GroupoidsOver S) [AlgebraicStack X] (F : etaleModules X)
    [HasFlatBaseChange F] :
    IsZero ((lisseEtaleRingedToposHom X).modulePullback.obj F) →
      IsParasitic (etaleModulePresheaf F) :=
  sorry

/-- The flat-fppf module pullback of a parasitic fppf module is zero. -/
theorem flatFppfModulePullback_isZero_of_isParasitic
    (X : GroupoidsOver S) [AlgebraicStack X]
    (F : SheafOfModules.{u} (structureSheaf X)) :
    IsParasitic F.val →
      IsZero ((flatFppfRingedToposHom X).modulePullback.obj F) :=
  sorry

/-- An fppf module is parasitic if its flat-fppf module pullback is zero. -/
theorem isParasitic_of_flatFppfModulePullback_isZero
    (X : GroupoidsOver S) [AlgebraicStack X]
    (F : SheafOfModules.{u} (structureSheaf X)) :
    IsZero ((flatFppfRingedToposHom X).modulePullback.obj F) →
      IsParasitic F.val :=
  sorry

end AlgebraicGeometry.AlgebraicStack
