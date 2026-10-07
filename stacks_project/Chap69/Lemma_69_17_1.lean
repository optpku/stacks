module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Coherent
public import stacks_project.Chap66.Definition_66_24_1_Noetherian
public import stacks_project.Chap66.«66_26_0_1_Pushforward»
public import stacks_project.Chap67.Definition_67_5_2_Surjective
public import stacks_project.Chap67.Definition_67_13_2_InverseImage
public import stacks_project.Chap67.Definition_67_45_2_Integral
public import stacks_project.Chap67.Lemma_67_15_1_ModuleSupport
public import stacks_project.Chap69.Definition_69_12_1_Instances

/-!
# Lemma 69.17.1

The pushforward of the structure sheaf of the inverse image of a closed
immersion along a finite surjective morphism of locally Noetherian algebraic
spaces is a coherent module of full étale-site support.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Modules

/-- Lemma 69.17.1 (1): if `f : Y ⟶ X` is a finite surjective morphism of algebraic spaces
over a scheme `S` with `X` locally Noetherian, and `i : Z ⟶ X` is a closed immersion,
then `f'_* 𝒪_{Z'}` is a coherent `𝒪_Z`-module, where `Z'` is `inverseImage f i` and
`f'` is `inverseImageTo f i`. -/
@[stacks 0GF7]
instance pushforward_inverseImageTo_unit_isCoherent
    {S : Scheme.{u}} {X Y Z : AlgebraicSpace S} (f : Y ⟶ X) [IsFinite f] [Surjective f]
    [IsLocallyNoetherian X] (i : Z ⟶ X) [IsClosedImmersion i] :
    ((pushforward (inverseImageTo f i)).obj
        (SheafOfModules.unit (structureSheaf (inverseImage f i)))).IsCoherent :=
  sorry

/-- Lemma 69.17.1 (2): under the same hypotheses, the étale-site support of `f'_* 𝒪_{Z'}`
equals `|Z|`. -/
@[stacks 0GF7]
theorem moduleSupport_pushforward_inverseImageTo_unit_eq_univ
    {S : Scheme.{u}} {X Y Z : AlgebraicSpace S} (f : Y ⟶ X) [IsFinite f] [Surjective f]
    [IsLocallyNoetherian X] (i : Z ⟶ X) [IsClosedImmersion i] :
    moduleSupport
        ((pushforward (inverseImageTo f i)).obj
          (SheafOfModules.unit (structureSheaf (inverseImage f i)))) =
      (Set.univ : Set (Points Z)) :=
  sorry

/-- Every point of `|Z|` lies in the étale-site support of the pushforward of `𝒪_{Z'}`
along `inverseImageTo f i`. -/
theorem mem_moduleSupport_pushforward_inverseImageTo_unit
    {S : Scheme.{u}} {X Y Z : AlgebraicSpace S} (f : Y ⟶ X) [IsFinite f] [Surjective f]
    [IsLocallyNoetherian X] (i : Z ⟶ X) [IsClosedImmersion i] (z : Points Z) :
    z ∈ moduleSupport
        ((pushforward (inverseImageTo f i)).obj
          (SheafOfModules.unit (structureSheaf (inverseImage f i)))) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Modules
