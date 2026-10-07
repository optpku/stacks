module

public import Mathlib.CategoryTheory.Sites.CoverLifting
public import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
public import ReasLib.CategoryTheory.Sites.Family.Covering
public import stacks_project.Chap07.Definition_7_6_2_Site

/-!
# Cocontinuity for selected precoverages

A functor of precoverages is cocontinuous when every selected covering of an
image object is refined by the image of some selected covering of the source
object. The image family need not itself be covering in the target.
-/

@[expose] public section

universe u₁ u₂ u₃ v₁ v₂ v₃ w

namespace CategoryTheory.Functor.Precoverage

open SemiRepresentableFamily.Over

variable {C : Type u₁} [Category.{v₁} C]
variable {D : Type u₂} [Category.{v₂} D]

/-- A functor of precoverages is cocontinuous when every selected covering of
`u.obj U` is refined by the image of some selected covering of `U`. -/
class IsCocontinuous (u : C ⥤ D) (P : _root_.CategoryTheory.Precoverage C)
    (Q : _root_.CategoryTheory.Precoverage D) : Prop where
  /-- A covering of `u.obj U` is refined by the image of a covering of `U`. -/
  exists_refinement :
    ∀ ⦃U : C⦄ {R : Presieve (u.obj U)},
      R ∈ Q (u.obj U) → ∃ S : Presieve U, S ∈ P U ∧ (S.map u).FactorsThru R

namespace IsCocontinuous

variable {P : _root_.CategoryTheory.Precoverage C}
variable {Q : _root_.CategoryTheory.Precoverage D} {u : C ⥤ D}

/-- Selected-cover form: every covering family of `u.obj U` admits a covering
family of `U` whose image family refines it. -/
theorem exists_cover [IsCocontinuous u P Q] {U : C}
    (𝒱 : SemiRepresentableFamily.Over.{w} (u.obj U)) (h𝒱 : IsCovering Q 𝒱) :
    ∃ 𝒰 : SemiRepresentableFamily.Over.{max u₁ v₁} U,
      IsCovering P 𝒰 ∧ (𝒰.toPresieve.map u).FactorsThru 𝒱.toPresieve :=
  sorry

/-- The identity functor is cocontinuous for every precoverage. -/
instance id (J : _root_.CategoryTheory.Precoverage C) :
    IsCocontinuous (𝟭 C) J J :=
  sorry

/-- The composition of cocontinuous functors of precoverages is cocontinuous. -/
theorem comp {E : Type u₃} [Category.{v₃} E] {v : D ⥤ E}
    {R : _root_.CategoryTheory.Precoverage E}
    [IsCocontinuous u P Q] [IsCocontinuous v Q R] :
    IsCocontinuous (u ⋙ v) P R :=
  sorry

/-- Selected-cover cocontinuity induces cocontinuity of the generated
Grothendieck topologies when both precoverages are sites. -/
instance toCocontinuous [P.IsSite] [Q.IsSite] [IsCocontinuous u P Q] :
    u.IsCocontinuous P.toGrothendieck Q.toGrothendieck :=
  sorry

/-- Cocontinuity for the generated topologies of sites implies selected-cover
cocontinuity. This is deliberately not an instance, so it cannot loop with
`toCocontinuous`. -/
theorem ofGrothendieck [P.IsSite] [Q.IsSite]
    [u.IsCocontinuous P.toGrothendieck Q.toGrothendieck] :
    IsCocontinuous u P Q :=
  sorry

end IsCocontinuous

end CategoryTheory.Functor.Precoverage
