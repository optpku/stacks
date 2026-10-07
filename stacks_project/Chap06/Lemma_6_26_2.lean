module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Definition
import StacksCheckRecall

@[expose] public section

open CategoryTheory
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry

/- The site-generic adjunction `SheafOfModules.pullbackPushforwardAdjunction` is the canonical
owner. Definition 6.26.1 supplies its exact ringed-space specialization, so the source is best
represented by the resulting `homEquiv`, rather than by a second adjunction or bijection wrapper.
This preserves the textbook `f^*` and `f_*` notation while exposing the equivalence directly for
later module-sheaf arguments. -/

section

variable {X Y : RingedSpace.{u}} (f : X ⟶ Y)
variable (𝒢 : Y.Modules) (ℱ : X.Modules)

/- Lemma 6.26.2: for a morphism of ringed spaces `f : X ⟶ Y`, an `𝒪_Y`-module sheaf `𝒢`, and an
`𝒪_X`-module sheaf `ℱ`, there is a canonical bijection
`((f^*).obj 𝒢 ⟶ ℱ) ≃ (𝒢 ⟶ (f _*).obj ℱ)`; equivalently, `f^*` is left adjoint to `f_*`. -/
@[stacks 0096 "pullback of module sheaves is left adjoint to pushforward"]
#check
  (((SheafOfModules.pullbackPushforwardAdjunction
      (RingedSpace.Hom.toRingCatSheafHom f)).homEquiv 𝒢 ℱ) :
    ((f^*).obj 𝒢 ⟶ ℱ) ≃ (𝒢 ⟶ (f _*).obj ℱ))

end

end AlgebraicGeometry
