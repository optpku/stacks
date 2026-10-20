module

public import ReasLib.AlgebraicGeometry.Scheme.DeRham.DerivedPushforward
public import ReasLib.AlgebraicGeometry.RingedSite.Module.HigherDirectImage
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.RelativeDimension
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace
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
      RingedSite.Hom.higherDirectImageModule (DerivedPushforward.pushforwardHom f)
        (RingedSpace.DeRham.term f.toLRSHom.toShHom p) (p + 1)

/-- In degree zero, the zero-extended source of the top higher-direct-image differential
is zero. -/
theorem topHigherDirectImageSource_zero {X S : Scheme.{u}} (f : X ⟶ S) :
    topHigherDirectImageSource f 0 = 0 := rfl

/-- In successor degree, the source is the corresponding higher direct image of relative
differential forms. -/
theorem topHigherDirectImageSource_succ {X S : Scheme.{u}}
    (f : X ⟶ S) (p : ℕ) :
    topHigherDirectImageSource f (p + 1) =
      RingedSite.Hom.higherDirectImageModule (DerivedPushforward.pushforwardHom f)
        (RingedSpace.DeRham.term f.toLRSHom.toShHom p) (p + 1) := rfl

/-- The zero-extended top-degree higher-direct-image map induced by the relative de Rham
differential. -/
noncomputable def topHigherDirectImageDifferential {X S : Scheme.{u}} (f : X ⟶ S) :
    (d : ℕ) →
      topHigherDirectImageSource f d ⟶
        RingedSite.Hom.higherDirectImageModule (DerivedPushforward.pushforwardHom f)
          (RingedSpace.DeRham.term f.toLRSHom.toShHom d) d
  | 0 => 0
  | p + 1 =>
      RingedSite.Hom.higherDirectImageModuleMap (DerivedPushforward.pushforwardHom f)
        (RingedSpace.DeRham.d f.toLRSHom.toShHom p) (p + 1)

/-- In degree zero, the zero-extended top higher-direct-image differential is zero. -/
theorem topHigherDirectImageDifferential_zero {X S : Scheme.{u}} (f : X ⟶ S) :
    topHigherDirectImageDifferential f 0 = 0 := rfl

/-- In successor degree, the zero-extended map is the higher-direct-image map induced by the
relative de Rham differential. -/
theorem topHigherDirectImageDifferential_succ {X S : Scheme.{u}}
    (f : X ⟶ S) (p : ℕ) :
    topHigherDirectImageDifferential f (p + 1) =
      RingedSite.Hom.higherDirectImageModuleMap (DerivedPushforward.pushforwardHom f)
        (RingedSpace.DeRham.d f.toLRSHom.toShHom p) (p + 1) := rfl

/-- For a proper smooth morphism with nonempty equidimensional fibres of dimension `n`
over a quasi-compact, quasi-separated base, the relative de Rham differential induces
the zero map on degree-`n` higher direct images. -/
theorem topHigherDirectImageDifferential_eq_zero {X S : Scheme.{u}}
    (f : X ⟶ S) (n : ℕ) [CompactSpace S] [QuasiSeparatedSpace S]
    [IsProper f] [Smooth f] [Scheme.Hom.RelativeDimension f n]
    (h_nonempty : ∀ s : S, Nonempty (f.fiber s)) :
    topHigherDirectImageDifferential f n = 0 := sorry

end AlgebraicGeometry.Scheme.DeRham
