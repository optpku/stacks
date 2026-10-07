module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.TorDimension
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.FlatMorphism
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.CohomologyBaseChange.TensorPushforward
public import ReasLib.AlgebraicGeometry.Scheme.Module.NaiveCotangent.BaseChange
public import ReasLib.RingTheory.Extension.Cotangent.NaiveComplex.BaseChange.Pushout

/-!
# Derived base change for naive cotangent complexes of schemes

The canonical cochain-level base-change map gives comparison morphisms in the derived
category for both ordinary and derived pullback.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits ComplexShape

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Hom.NaiveCotangent.BaseChange

variable {X X' Y Y' : _root_.AlgebraicGeometry.Scheme.{u}}
variable {g' : X' ⟶ X} {f' : X' ⟶ Y'} {f : X ⟶ Y} {g : Y' ⟶ Y}

/-- The image in the derived category of the canonical cochain-level base-change map for a
commutative square of schemes. -/
noncomputable def underivedComparison (sq : CommSq g' f' f g) :
    DerivedCategory.Q.obj
        (((_root_.AlgebraicGeometry.Scheme.Modules.pullback g').mapHomologicalComplex
          (up ℤ)).obj (RingedSpace.naiveCotangent f.toShHom)) ⟶
      DerivedCategory.Q.obj (RingedSpace.naiveCotangent f'.toShHom) :=
  DerivedCategory.Q.map (map sq)

/-- The underived comparison is the localization of the canonical cochain-level base-change
map. -/
theorem underivedComparison_def (sq : CommSq g' f' f g) :
    underivedComparison sq = DerivedCategory.Q.map (map sq) := rfl

/-- The canonical comparison from derived pullback of `NL(f)` to `NL(f')`, obtained by first
comparing derived pullback with termwise pullback. -/
noncomputable def derivedComparison (sq : CommSq g' f' f g) :
    (RingedSpace.modulePullbackDerived g'.toShHom).obj
        (DerivedCategory.Q.obj (RingedSpace.naiveCotangent f.toShHom)) ⟶
      DerivedCategory.Q.obj (RingedSpace.naiveCotangent f'.toShHom) :=
  Scheme.DerivedQCoh.pullbackComplexComparison g'
      (RingedSpace.naiveCotangent f.toShHom) ≫
    underivedComparison sq

/-- The derived comparison factors through the canonical derived-to-termwise pullback map and
the underived comparison. -/
theorem derivedComparison_def (sq : CommSq g' f' f g) :
    derivedComparison sq =
      Scheme.DerivedQCoh.pullbackComplexComparison g'
          (RingedSpace.naiveCotangent f.toShHom) ≫
        underivedComparison sq := rfl

/-- For a pullback square of schemes whose right vertical morphism is flat, the underived
naive-cotangent base-change comparison is an isomorphism. -/
theorem underivedComparison_isIso_of_flat (hcart : IsPullback g' f' f g) [Flat f] :
    IsIso (underivedComparison hcart.toCommSq) := sorry

/-- For a pullback square of schemes whose right vertical morphism is flat, if its naive
cotangent complex has Tor-amplitude in `[-1, 0]`, then the derived base-change comparison is an
isomorphism. -/
theorem derivedComparison_isIso_of_flat_of_hasTorAmplitudeIn
    (hcart : IsPullback g' f' f g) [Flat f]
    (hNL : RingedSpace.HasTorAmplitudeIn
      (DerivedCategory.Q.obj (RingedSpace.naiveCotangent f.toShHom)) (-1) 0) :
    IsIso (derivedComparison hcart.toCommSq) := sorry

end AlgebraicGeometry.Scheme.Hom.NaiveCotangent.BaseChange
