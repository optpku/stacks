module

public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Fiber.GeometricallyConnected
public import stacks_project.Chap59.Definition_59_33_2_HenselizationScheme
public import stacks_project.Chap59.Lemma_59_55_3

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.Etale.SheafSystem

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Etale

/-- Image of a geometric point of `X` along `f : X ⟶ S`. -/
noncomputable def geometricPointImage {X S : Scheme.{u}} (f : X ⟶ S)
    (x : GeometricPoint X) : GeometricPoint S where
  toFieldValuedPoint := { K := x.K, hom := x.hom ≫ f }
  isAlgClosed := x.isAlgClosed

/-- The scheme morphism of `geometricPointImage f x` is `x.hom ≫ f`. -/
theorem geometricPointImage_hom {X S : Scheme.{u}} (f : X ⟶ S)
    (x : GeometricPoint X) : (geometricPointImage f x).hom = x.hom ≫ f :=
  sorry

/-- The morphism of strict henselizations of local rings induced by `f`
at a geometric point, if it exists, has geometrically connected fibres. -/
def hasGeometricallyConnectedStrictHenselFibers {X S : Scheme.{u}}
    (f : X ⟶ S) : Prop :=
  ∀ (x : GeometricPoint X) (RshX RshS : Type u)
    [CommRing RshX] [CommRing RshS]
    [Algebra (X.presheaf.stalk x.image) RshX]
    [Algebra (S.presheaf.stalk (geometricPointImage f x).image) RshS]
    [IsStrictHenselizationOf (X.presheaf.stalk x.image) RshX]
    [IsStrictHenselizationOf
      (S.presheaf.stalk (geometricPointImage f x).image) RshS]
    (φ : strictHenselizationScheme X x RshX ⟶
      strictHenselizationScheme S (geometricPointImage f x) RshS),
    φ ≫
          (Spec.map (CommRingCat.ofHom
              (algebraMap (S.presheaf.stalk (geometricPointImage f x).image)
                RshS)) ≫
            S.fromSpecStalk (geometricPointImage f x).image) =
        (Spec.map (CommRingCat.ofHom
            (algebraMap (X.presheaf.stalk x.image) RshX)) ≫
          X.fromSpecStalk x.image) ≫ f →
      GeometricallyConnected φ

/-- Unfolding of `hasGeometricallyConnectedStrictHenselFibers` at a geometric
point and a commuting strict-henselization map. -/
theorem hasGeometricallyConnectedStrictHenselFibers_iff {X S : Scheme.{u}}
    (f : X ⟶ S) :
    hasGeometricallyConnectedStrictHenselFibers f ↔
      ∀ (x : GeometricPoint X) (RshX RshS : Type u)
        [CommRing RshX] [CommRing RshS]
        [Algebra (X.presheaf.stalk x.image) RshX]
        [Algebra (S.presheaf.stalk (geometricPointImage f x).image) RshS]
        [IsStrictHenselizationOf (X.presheaf.stalk x.image) RshX]
        [IsStrictHenselizationOf
          (S.presheaf.stalk (geometricPointImage f x).image) RshS]
        (φ : strictHenselizationScheme X x RshX ⟶
          strictHenselizationScheme S (geometricPointImage f x) RshS),
        φ ≫
              (Spec.map (CommRingCat.ofHom
                  (algebraMap (S.presheaf.stalk
                    (geometricPointImage f x).image) RshS)) ≫
                S.fromSpecStalk (geometricPointImage f x).image) =
            (Spec.map (CommRingCat.ofHom
                (algebraMap (X.presheaf.stalk x.image) RshX)) ≫
              X.fromSpecStalk x.image) ≫ f →
          GeometricallyConnected φ :=
  sorry

/-- Application of `hasGeometricallyConnectedStrictHenselFibers` at one
geometric point. -/
theorem hasGeometricallyConnectedStrictHenselFibers_apply {X S : Scheme.{u}}
    {f : X ⟶ S} (h_fib : hasGeometricallyConnectedStrictHenselFibers f)
    (x : GeometricPoint X) {RshX RshS : Type u}
    [CommRing RshX] [CommRing RshS]
    [Algebra (X.presheaf.stalk x.image) RshX]
    [Algebra (S.presheaf.stalk (geometricPointImage f x).image) RshS]
    [IsStrictHenselizationOf (X.presheaf.stalk x.image) RshX]
    [IsStrictHenselizationOf
      (S.presheaf.stalk (geometricPointImage f x).image) RshS]
    (φ : strictHenselizationScheme X x RshX ⟶
      strictHenselizationScheme S (geometricPointImage f x) RshS)
    (h_induced :
      φ ≫
          (Spec.map (CommRingCat.ofHom
              (algebraMap (S.presheaf.stalk (geometricPointImage f x).image)
                RshS)) ≫
            S.fromSpecStalk (geometricPointImage f x).image) =
        (Spec.map (CommRingCat.ofHom
            (algebraMap (X.presheaf.stalk x.image) RshX)) ≫
          X.fromSpecStalk x.image) ≫ f) :
    GeometricallyConnected φ :=
  sorry

/-- Lemma 59.87.6: if `f : X ⟶ S` is flat and every geometric point `x̄` of `X`
has geometrically connected fibres for the induced map of strict henselizations
`O_{S, f(x̄)}^{sh} ⟶ O_{X, x̄}^{sh}`, then for every cartesian square
with `g : T ⟶ S` quasi-compact and quasi-separated and every sheaf of sets
`F` on `T` étale, the comparison
`pullbackAlong f (pushforwardAlong g F) ⟶
  pushforwardAlong h (pullbackAlong e F)`
is an isomorphism, i.e. `f⁻¹ g_* F = h_* e⁻¹ F`. -/
@[stacks 0F00]
theorem etaleSetBaseChange_of_geometricallyConnectedStrictHenselFibers
    {X Y S T : Scheme.{u}} (f : X ⟶ S) (h : Y ⟶ X) (e : Y ⟶ T) (g : T ⟶ S)
    [Flat f] [QuasiCompact g] [QuasiSeparated g]
    (h_cart : IsPullback h e f g)
    (h_fib : hasGeometricallyConnectedStrictHenselFibers f)
    (F : Sheaf T.smallEtaleTopology (Type (u + 1))) :
    IsIso (finiteBaseChangeHom g f h e h_cart.flip F) :=
  sorry

end AlgebraicGeometry.Scheme.Etale

end

end
