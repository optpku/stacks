/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
public import stacks_project.Chap42.Remark_42_56_7_Euler
public import ReasLib.AlgebraicGeometry.Scheme.K0.Support.Comparison

@[expose] public section

open CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.K0'

/- Remark 42.56.8: a closed immersion into a regular locally Noetherian scheme induces the
canonical map from coherent `K₀` of the closed subscheme to perfect `K₀` supported on its
image, by placing each pushed-forward coherent sheaf in degree zero. -/
@[stacks 0FEQ] #check (AlgebraicGeometry.Scheme.K0'.toK0WithSupport :
  ∀ {X Z : Scheme.{u}} [IsLocallyNoetherian X] [Scheme.Regular X]
    (i : Z ⟶ X) [IsClosedImmersion i],
    @K0' Z (LocallyOfFiniteType.isLocallyNoetherian i) →+
      K0WithSupport X (Set.range i.base))

/- The closed-immersion comparison sends a coherent generator to the degree-zero class of
its supported pushforward. -/
#check (AlgebraicGeometry.Scheme.K0'.toK0WithSupport_of :
  ∀ {X Z : Scheme.{u}} [IsLocallyNoetherian X] [Scheme.Regular X]
    (i : Z ⟶ X) [IsClosedImmersion i]
    (F : RingedSpace.Coh Z.toRingedSpace),
    AlgebraicGeometry.Scheme.K0'.toK0WithSupport i
        (ObjectProperty.GrothendieckGroup.of
          (SheafOfModules.isCoherent Z.toRingedSpace.ringCatSheaf) F) =
      TriangulatedK0.of
        ((K0'WithSupport.singlePerfect X (Set.range i.base)).obj
          ((@Modules.ClosedImmersion.toSupported X Z _
            (LocallyOfFiniteType.isLocallyNoetherian i) i _).obj F)))

end AlgebraicGeometry.Scheme.K0'
