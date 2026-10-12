/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap50.Lemma_50_3_5_DerivedDeRham
public import ReasLib.AlgebraicGeometry.RingedSite.Module.HigherDirectImage

@[expose] public section

open AlgebraicGeometry CategoryTheory
open scoped ZeroObject

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.DeRham

/-- The zero-extended source of the top-degree map on higher direct images of relative
differential forms. -/
noncomputable def topHigherDirectImageSource {X S : Scheme.{u}} (f : X ⟶ S) :
    (d : ℕ) →
      RingedSite.ModuleCat.{u}
        (RingedSpace.DeRham.coefficientSite (𝟙 S.toRingedSpace))
  | 0 => 0
  | p + 1 =>
      RingedSite.Hom.higherDirectImageModule (pushforwardHom f)
        (RingedSpace.DeRham.term f.toLRSHom.toShHom p) (p + 1)

/-- In degree zero, the zero-extended source of the top higher-direct-image differential
is zero. -/
theorem topHigherDirectImageSource_zero {X S : Scheme.{u}} (f : X ⟶ S) :
    topHigherDirectImageSource f 0 = 0 := sorry

/-- In successor degree, the source is the corresponding higher direct image of relative
differential forms. -/
theorem topHigherDirectImageSource_succ {X S : Scheme.{u}}
    (f : X ⟶ S) (p : ℕ) :
    topHigherDirectImageSource f (p + 1) =
      RingedSite.Hom.higherDirectImageModule (pushforwardHom f)
        (RingedSpace.DeRham.term f.toLRSHom.toShHom p) (p + 1) := sorry

/-- The zero-extended top-degree higher-direct-image map induced by the relative de Rham
differential. -/
noncomputable def topHigherDirectImageDifferential {X S : Scheme.{u}} (f : X ⟶ S) :
    (d : ℕ) →
      topHigherDirectImageSource f d ⟶
        RingedSite.Hom.higherDirectImageModule (pushforwardHom f)
          (RingedSpace.DeRham.term f.toLRSHom.toShHom d) d
  | 0 => 0
  | p + 1 =>
      RingedSite.Hom.higherDirectImageModuleMap (pushforwardHom f)
        (RingedSpace.DeRham.d f.toLRSHom.toShHom p) (p + 1)

/-- In degree zero, the zero-extended top higher-direct-image differential is zero. -/
theorem topHigherDirectImageDifferential_zero {X S : Scheme.{u}} (f : X ⟶ S) :
    topHigherDirectImageDifferential f 0 = 0 := sorry

/-- In successor degree, the zero-extended map is the higher-direct-image map induced by the
relative de Rham differential. -/
theorem topHigherDirectImageDifferential_succ {X S : Scheme.{u}}
    (f : X ⟶ S) (p : ℕ) :
    topHigherDirectImageDifferential f (p + 1) =
      RingedSite.Hom.higherDirectImageModuleMap (pushforwardHom f)
        (RingedSpace.DeRham.d f.toLRSHom.toShHom p) (p + 1) := sorry

end AlgebraicGeometry.Scheme.DeRham
