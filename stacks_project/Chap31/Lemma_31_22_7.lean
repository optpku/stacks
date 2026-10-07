module

import ReasLib.AlgebraicGeometry.Scheme.Morphism.RelativeRegularImmersion.FiberCriterion
import StacksCheckRecall

open AlgebraicGeometry
open CategoryTheory
open scoped AlgebraicGeometry

universe u

/- Lemma 31.22.7 (1): a fiberwise quasi-regular closed subscheme is locally contained in a
relative quasi-regular closed subscheme with the same fiber. -/
@[stacks 063W] #check
  (AlgebraicGeometry.RelativeQuasiRegularImmersion.exists_open_le_fiber_eq_of_isQuasiRegularImmersion_near :
    ∀ {X S : Scheme.{u}} (f : X ⟶ S) (T : X.IdealSheafData) (x : T.subscheme)
    [Flat f] [LocallyOfFinitePresentation f]
    (hfiber :
      ∃ W : (Scheme.Hom.fiber f (f (T.subschemeι x))).Opens,
        Scheme.Hom.asFiber f (T.subschemeι x) ∈
            (W : Set (Scheme.Hom.fiber f (f (T.subschemeι x)))) ∧
          IsQuasiRegularImmersion
            (((T.comap (Scheme.Hom.fiberι f (f (T.subschemeι x)))).comap W.ι).subschemeι)),
    ∃ U : X.Opens,
      ∃ _ : T.subschemeι x ∈ (U : Set X),
        ∃ Z : U.toScheme.IdealSheafData,
          ∃ _ : RelativeQuasiRegularImmersion (U.ι ≫ f) Z.subschemeι,
            ∃ _ : IsRegularImmersion Z.subschemeι,
              ∃ _ : Z ≤ T.comap U.ι,
                (T.comap U.ι).comap
                    (Scheme.Hom.fiberι (U.ι ≫ f) (f (T.subschemeι x))) =
                  Z.comap (Scheme.Hom.fiberι (U.ι ≫ f) (f (T.subschemeι x))))

/- Lemma 31.22.7 (2): under finite-presentation and pointwise-flatness hypotheses, the local
relative quasi-regular closed subscheme can be chosen equal to the original one. -/
@[stacks 063W] #check
  (AlgebraicGeometry.RelativeQuasiRegularImmersion.exists_open_eq_of_finitePresentation_flatAt :
    ∀ {X S : Scheme.{u}} (f : X ⟶ S) (T : X.IdealSheafData) (x : T.subscheme)
    [Flat f] [LocallyOfFinitePresentation f]
    [Scheme.Hom.FinitePresentation T.subschemeι]
    (hTflat : Scheme.Hom.flatAt (T.subschemeι ≫ f) x)
    (hfiber :
      ∃ W : (Scheme.Hom.fiber f (f (T.subschemeι x))).Opens,
        Scheme.Hom.asFiber f (T.subschemeι x) ∈
            (W : Set (Scheme.Hom.fiber f (f (T.subschemeι x)))) ∧
          IsQuasiRegularImmersion
            (((T.comap (Scheme.Hom.fiberι f (f (T.subschemeι x)))).comap W.ι).subschemeι)),
    ∃ U : X.Opens,
      ∃ _ : T.subschemeι x ∈ (U : Set X),
        ∃ Z : U.toScheme.IdealSheafData,
          ∃ _ : RelativeQuasiRegularImmersion (U.ι ≫ f) Z.subschemeι,
            ∃ _ : IsRegularImmersion Z.subschemeι,
              T.comap U.ι = Z)

/- Lemma 31.22.7 (3): under the expected-codimension equation hypothesis, the local relative
quasi-regular closed subscheme can be chosen equal to the original one. -/
@[stacks 063W] #check
  (AlgebraicGeometry.RelativeQuasiRegularImmersion.exists_open_eq_of_cutOutBy_expectedCodimension :
    ∀ {X S : Scheme.{u}} (f : X ⟶ S) (T : X.IdealSheafData) (x : T.subscheme)
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
            (((T.comap (Scheme.Hom.fiberι f (f (T.subschemeι x)))).comap W.ι).subschemeι)),
    ∃ U : X.Opens,
      ∃ _ : T.subschemeι x ∈ (U : Set X),
        ∃ Z : U.toScheme.IdealSheafData,
          ∃ _ : RelativeQuasiRegularImmersion (U.ι ≫ f) Z.subschemeι,
            ∃ _ : IsRegularImmersion Z.subschemeι,
              T.comap U.ι = Z)

/- Lemma 31.22.7 (4): a flat, locally finitely presented closed subscheme with quasi-regular
fiber immersions is a relative quasi-regular immersion. -/
@[stacks 063W] #check
  (AlgebraicGeometry.RelativeQuasiRegularImmersion.of_flat_locallyOfFinitePresentation_fibers :
    ∀ {X S : Scheme.{u}} (f : X ⟶ S) (T : X.IdealSheafData)
    [Flat f] [LocallyOfFinitePresentation f]
    [LocallyOfFinitePresentation (T.subschemeι ≫ f)] [Flat (T.subschemeι ≫ f)]
    (hfibers : ∀ s : S,
      IsQuasiRegularImmersion ((T.comap (Scheme.Hom.fiberι f s)).subschemeι)),
    RelativeQuasiRegularImmersion f T.subschemeι)
