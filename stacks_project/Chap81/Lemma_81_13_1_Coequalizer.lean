/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Limits.Shapes.Equalizers
public import stacks_project.Chap67.Remark_67_20_9_Factorization
public import stacks_project.Chap76.Definition_76_6_5_NormalCone
public import stacks_project.Chap81.Lemma_81_13_1_Equalizer

/-!
# Kernel-pair coequalizers of proper morphisms

The coequalizer of the kernel pair of a proper morphism `g : Y ⟶ X` of
algebraic spaces, with `X` locally Noetherian, is the relative spectrum of the
equalizer algebra of `s^♯, t^♯`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.KernelPairCoequalizer

variable {S : Scheme.{u}} {X Y : AlgebraicSpace S}

/-- The coequalizer `X'` of the kernel pair of a proper morphism `g : Y ⟶ X`, as
the relative spectrum of the equalizer algebra. -/
def space (g : Y ⟶ X) [IsLocallyNoetherian X] [Proper g] : AlgebraicSpace S :=
  relativeSpec (equalizerAlgebra g)

/-- The kernel-pair coequalizer is the relative spectrum of `equalizerAlgebra`. -/
theorem space_eq_relativeSpec (g : Y ⟶ X) [IsLocallyNoetherian X] [Proper g] :
    space g = relativeSpec (equalizerAlgebra g) :=
  rfl

/-- The structure morphism `X' ⟶ X` of the kernel-pair coequalizer. -/
def toTarget (g : Y ⟶ X) [IsLocallyNoetherian X] [Proper g] : space g ⟶ X :=
  relativeSpecπ (equalizerAlgebra g)

/-- The structure morphism of the kernel-pair coequalizer is the relative-spectrum
projection of `equalizerAlgebra`. -/
theorem toTarget_eq_relativeSpecπ (g : Y ⟶ X) [IsLocallyNoetherian X]
    [Proper g] : toTarget g = relativeSpecπ (equalizerAlgebra g) :=
  rfl

/-- The canonical morphism `Y ⟶ X'` through the relative spectrum of `g_* 𝒪_Y`
and the equalizer inclusion. -/
def fromSource (g : Y ⟶ X) [IsLocallyNoetherian X] [Proper g] : Y ⟶ space g :=
  Hom.toPushforwardRelativeSpec g ≫ relativeSpecMap (inclusion g)

/-- The source morphism of the kernel-pair coequalizer is the composite of
`Hom.toPushforwardRelativeSpec` with `relativeSpecMap` of the equalizer
inclusion. -/
theorem fromSource_eq (g : Y ⟶ X) [IsLocallyNoetherian X] [Proper g] :
    fromSource g =
      Hom.toPushforwardRelativeSpec g ≫ relativeSpecMap (inclusion g) :=
  rfl

/-- The factorization identity `fromSource g ≫ toTarget g = g`. -/
theorem fromSource_comp_toTarget (g : Y ⟶ X) [IsLocallyNoetherian X]
    [Proper g] : fromSource g ≫ toTarget g = g :=
  sorry

/-- The kernel-pair projections equalize `fromSource g`. -/
theorem equalizes (g : Y ⟶ X) [IsLocallyNoetherian X] [Proper g] :
    fst g ≫ fromSource g = snd g ≫ fromSource g :=
  sorry

/-- The cofork `R ⇉ Y ⟶ X'` presenting the kernel-pair coequalizer candidate. -/
def cofork (g : Y ⟶ X) [IsLocallyNoetherian X] [Proper g] :
    Cofork (fst g) (snd g) :=
  Cofork.ofπ (fromSource g) (equalizes g)

/-- The coequalizer candidate of `cofork g` is `fromSource g`. -/
theorem cofork_π (g : Y ⟶ X) [IsLocallyNoetherian X] [Proper g] :
    (cofork g).π = fromSource g :=
  sorry

/-- The cofork of `fromSource g` is a colimit in `AlgebraicSpace S`. -/
theorem nonempty_isColimit_cofork (g : Y ⟶ X) [IsLocallyNoetherian X]
    [Proper g] : Nonempty (IsColimit (cofork g)) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.KernelPairCoequalizer
