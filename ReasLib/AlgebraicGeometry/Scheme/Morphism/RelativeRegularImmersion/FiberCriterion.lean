/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FinitePresentation
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FiberDimension
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Flat
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.RelativeRegularImmersion.FlatFinitePresentation

@[expose] public section

open CategoryTheory
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.RelativeQuasiRegularImmersion

/-- A closed subscheme whose fiber is quasi-regular near a point is locally contained in a
relative quasi-regular closed subscheme with the same fiber; the latter immersion is regular. -/
theorem exists_open_le_fiber_eq_of_isQuasiRegularImmersion_near
    {X S : Scheme.{u}} (f : X ⟶ S) (T : X.IdealSheafData) (x : T.subscheme)
    [Flat f] [LocallyOfFinitePresentation f]
    (hfiber :
      ∃ W : (Scheme.Hom.fiber f (f (T.subschemeι x))).Opens,
        Scheme.Hom.asFiber f (T.subschemeι x) ∈
            (W : Set (Scheme.Hom.fiber f (f (T.subschemeι x)))) ∧
          IsQuasiRegularImmersion
            (((T.comap (Scheme.Hom.fiberι f (f (T.subschemeι x)))).comap W.ι).subschemeι)) :
    ∃ U : X.Opens,
      ∃ _ : T.subschemeι x ∈ (U : Set X),
        ∃ Z : U.toScheme.IdealSheafData,
          ∃ _ : RelativeQuasiRegularImmersion (U.ι ≫ f) Z.subschemeι,
            ∃ _ : IsRegularImmersion Z.subschemeι,
              ∃ _ : Z ≤ T.comap U.ι,
                (T.comap U.ι).comap
                    (Scheme.Hom.fiberι (U.ι ≫ f) (f (T.subschemeι x))) =
                  Z.comap (Scheme.Hom.fiberι (U.ι ≫ f) (f (T.subschemeι x))) := sorry

/-- A finitely presented closed subscheme that is flat over the base at a point and whose fiber
is quasi-regular nearby is locally a relative quasi-regular immersion, hence a regular immersion. -/
theorem exists_open_eq_of_finitePresentation_flatAt
    {X S : Scheme.{u}} (f : X ⟶ S) (T : X.IdealSheafData) (x : T.subscheme)
    [Flat f] [LocallyOfFinitePresentation f]
    [Scheme.Hom.FinitePresentation T.subschemeι]
    (hTflat : Scheme.Hom.flatAt (T.subschemeι ≫ f) x)
    (hfiber :
      ∃ W : (Scheme.Hom.fiber f (f (T.subschemeι x))).Opens,
        Scheme.Hom.asFiber f (T.subschemeι x) ∈
            (W : Set (Scheme.Hom.fiber f (f (T.subschemeι x)))) ∧
          IsQuasiRegularImmersion
            (((T.comap (Scheme.Hom.fiberι f (f (T.subschemeι x)))).comap W.ι).subschemeι)) :
    ∃ U : X.Opens,
      ∃ _ : T.subschemeι x ∈ (U : Set X),
        ∃ Z : U.toScheme.IdealSheafData,
          ∃ _ : RelativeQuasiRegularImmersion (U.ι ≫ f) Z.subschemeι,
            ∃ _ : IsRegularImmersion Z.subschemeι,
              T.comap U.ι = Z := sorry

/-- A closed subscheme cut out by the expected number of equations and whose fiber is
quasi-regular near a point is locally a relative quasi-regular immersion and a regular immersion. -/
theorem exists_open_eq_of_cutOutBy_expectedCodimension
    {X S : Scheme.{u}} (f : X ⟶ S) (T : X.IdealSheafData) (x : T.subscheme)
    [Flat f] [LocallyOfFinitePresentation f] (c : ℕ)
    (V : X.affineOpens) (hV : T.subschemeι x ∈ (V : Set X))
    (g : Fin c → Γ(X, V)) (hcut : T.ideal V = Ideal.span (Set.range g))
    (hdim :
      f.fiberDimensionAt (T.subschemeι x) =
        (T.subschemeι ≫ f).fiberDimensionAt x + (c : WithBot ℕ∞))
    (hfiber :
      ∃ W : (Scheme.Hom.fiber f (f (T.subschemeι x))).Opens,
        Scheme.Hom.asFiber f (T.subschemeι x) ∈
            (W : Set (Scheme.Hom.fiber f (f (T.subschemeι x)))) ∧
          IsQuasiRegularImmersion
            (((T.comap (Scheme.Hom.fiberι f (f (T.subschemeι x)))).comap W.ι).subschemeι)) :
    ∃ U : X.Opens,
      ∃ _ : T.subschemeι x ∈ (U : Set X),
        ∃ Z : U.toScheme.IdealSheafData,
          ∃ _ : RelativeQuasiRegularImmersion (U.ι ≫ f) Z.subschemeι,
            ∃ _ : IsRegularImmersion Z.subschemeι,
              T.comap U.ι = Z := sorry

/-- A flat, locally finitely presented closed subscheme whose immersion in every fiber is
quasi-regular is a relative quasi-regular immersion. -/
theorem of_flat_locallyOfFinitePresentation_fibers
    {X S : Scheme.{u}} (f : X ⟶ S) (T : X.IdealSheafData)
    [Flat f] [LocallyOfFinitePresentation f]
    [LocallyOfFinitePresentation (T.subschemeι ≫ f)] [Flat (T.subschemeι ≫ f)]
    (hfibers : ∀ s : S,
      IsQuasiRegularImmersion ((T.comap (Scheme.Hom.fiberι f s)).subschemeι)) :
    RelativeQuasiRegularImmersion f T.subschemeι := sorry

end AlgebraicGeometry.RelativeQuasiRegularImmersion
